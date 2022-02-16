use core::ops::Deref;

use bls12_381::Scalar;
use ff::Field;
use rand::{CryptoRng, RngCore};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Sha3XofReader, Shake256,
};
use subtle::{ConstantTimeEq, CtOption};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct NonZeroScalar(pub(crate) Scalar);

impl NonZeroScalar {
    pub fn new(scalar: Scalar) -> CtOption<Self> {
        CtOption::new(Self(scalar), !scalar.is_zero())
    }

    pub fn random(mut rng: impl CryptoRng + RngCore) -> Self {
        loop {
            let s = Scalar::random(&mut rng);
            if !bool::from(s.is_zero()) {
                break Self(s);
            }
        }
    }

    pub fn invert(&self) -> NonZeroScalar {
        Self(self.0.invert().unwrap())
    }
}

impl Deref for NonZeroScalar {
    type Target = Scalar;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug)]
/// Derive Scalar values by hashing an arbitrary length input using Shake256
pub struct HashScalar<'d> {
    hasher: Shake256,
    dst: Option<&'d [u8]>,
}

impl<'d> HashScalar<'d> {
    /// Create a new HashScalar instance
    pub fn new(dst: Option<&'d [u8]>) -> Self {
        Self {
            hasher: Shake256::default(),
            dst,
        }
    }
}

impl HashScalar<'_> {
    #[inline]
    /// Add input to the hash state and return the new state
    pub fn chain(mut self, input: impl AsRef<[u8]>) -> Self {
        self.update(input.as_ref());
        self
    }

    #[inline]
    /// Utility method to hash the input and return a single Scalar
    pub fn digest(input: impl AsRef<[u8]>, dst: Option<&[u8]>) -> NonZeroScalar {
        HashScalar::new(dst).chain(input.as_ref()).finalize()
    }

    #[inline]
    /// Add more input to the hash state
    pub fn update(&mut self, input: impl AsRef<[u8]>) {
        self.hasher.update(input.as_ref());
    }

    /// Finalize the hasher and return a factory for Scalar values
    pub fn read(mut self) -> HashScalarRead {
        if let Some(dst) = self.dst {
            self.hasher.update(dst);
        }
        HashScalarRead(self.hasher.finalize_xof())
    }

    /// Finalize the hasher and return a single NonZeroScalar
    pub fn finalize(self) -> NonZeroScalar {
        self.read().next()
    }
}

/// The output of a HashScalar, allowing for multiple Scalar values to be read
pub struct HashScalarRead(Sha3XofReader);

impl HashScalarRead {
    /// Read the next non-zero Scalar value from the extensible hash output
    pub fn next(&mut self) -> NonZeroScalar {
        let mut buf = [0u8; 64];
        let mut s;
        loop {
            self.0.read(&mut buf);
            s = Scalar::from_bytes_wide(&buf);
            if !bool::from(s.ct_eq(&Scalar::zero())) {
                break NonZeroScalar(s);
            }
        }
    }
}
