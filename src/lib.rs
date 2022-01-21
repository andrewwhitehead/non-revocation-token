use bls12_381::{
    hash_to_curve::{ExpandMsgXof, HashToCurve},
    pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar,
};
use ff::Field;
use group::{Curve, Group, Wnaf};
use rand::{CryptoRng, Rng};
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Sha3XofReader, Shake256,
};
use subtle::ConstantTimeEq;

const G2_UNCOMPRESSED_SIZE: usize = 192;

fn random_scalar(mut rng: impl CryptoRng + Rng) -> Scalar {
    loop {
        let s = Scalar::random(&mut rng);
        if !bool::from(s.is_zero()) {
            break s;
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// FIXME ensure non-zero scalar
pub struct SecretKey(Scalar);

impl SecretKey {
    pub fn random(rng: impl CryptoRng + Rng) -> Self {
        Self(random_scalar(rng))
    }

    pub fn public_key(&self) -> PublicKey {
        PublicKey((G2Projective::generator() * self.0).to_affine())
    }

    pub fn keypair(rng: impl CryptoRng + Rng) -> (Self, PublicKey) {
        let sk = Self::random(rng);
        (sk, sk.public_key())
    }
}

impl From<Scalar> for SecretKey {
    fn from(s: Scalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicKey(G2Affine);

impl From<G2Affine> for PublicKey {
    fn from(p: G2Affine) -> Self {
        Self(p)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// FIXME ensure non-zero scalar
pub struct MemberValue(Scalar);

impl MemberValue {
    pub fn random(rng: impl CryptoRng + Rng) -> Self {
        Self(random_scalar(rng))
    }
}

impl From<Scalar> for MemberValue {
    fn from(s: Scalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// FIXME ensure non-zero scalar
pub struct BlockValue(Scalar);

impl BlockValue {
    pub fn new(reg_id: &str, block_index: u32) -> Self {
        let mut hash_q = HashScalar::new(None);
        hash_q.update(reg_id);
        hash_q.update(&[0]);
        hash_q.update(block_index.to_be_bytes());
        Self(hash_q.finalize())
    }
}

impl From<Scalar> for BlockValue {
    fn from(s: Scalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Accumulator(G1Affine);

impl From<G1Affine> for Accumulator {
    #[inline]
    fn from(p: G1Affine) -> Self {
        Self(p)
    }
}

impl From<G1Projective> for Accumulator {
    #[inline]
    fn from(p: G1Projective) -> Self {
        Self(p.into())
    }
}

impl Accumulator {
    pub fn issuer_update(
        &self,
        members: impl IntoIterator<Item = MemberValue>,
        revoke_sk: &SecretKey,
        add: bool,
    ) -> Self {
        let mut members = members.into_iter();
        let acc = match members.next() {
            Some(m) => {
                let mut acc = members.fold(m.0 + revoke_sk.0, |acc, m| acc * (m.0 + revoke_sk.0));
                if !add {
                    acc = acc.invert().unwrap();
                }
                (self.0 * acc).into()
            }
            None => self.0,
        };
        Self(acc)
    }

    pub fn issuer_create_witness(&self, revoke_sk: &SecretKey, member: MemberValue) -> Witness {
        Witness::from(self.0 * (member.0 + revoke_sk.0).invert().unwrap())
    }

    pub fn check_witness(
        &self,
        member: MemberValue,
        witness: Witness,
        public_key: PublicKey,
    ) -> bool {
        pairing(
            &witness.0,
            &(G2Projective::generator() * member.0 + public_key.0).to_affine(),
        ) == pairing(&self.0, &G2Affine::generator())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Witness(G1Affine);

impl From<G1Affine> for Witness {
    #[inline]
    fn from(p: G1Affine) -> Self {
        Self(p)
    }
}

impl From<G1Projective> for Witness {
    #[inline]
    fn from(p: G1Projective) -> Self {
        Self(p.into())
    }
}

pub trait MemberDataAccess {
    fn accumulator(&self) -> Accumulator;

    fn public_key(&self) -> PublicKey;

    fn member_value(&self, index: usize) -> MemberValue;

    fn witness(&self, index: usize) -> Witness;

    fn len(&self) -> usize;
}

pub struct MemberData {
    accum: Accumulator,
    public_key: PublicKey,
    members: Vec<MemberValue>,
    witness: Vec<G1Affine>,
}

impl MemberData {
    pub fn new(
        accum: Accumulator,
        public_key: PublicKey,
        members: Vec<MemberValue>,
        witness: Vec<G1Affine>,
    ) -> Self {
        Self {
            accum,
            public_key,
            members,
            witness,
        }
    }

    pub fn create(revoke_sk: &SecretKey, size: usize, mut rng: impl CryptoRng + Rng) -> Self {
        let accum = G1Projective::random(&mut rng);
        let public_key = revoke_sk.public_key();
        let members: Vec<_> = (0..size).map(|_| MemberValue::random(&mut rng)).collect();

        let mut wnaf = Wnaf::new();
        let mut acc_wnaf = wnaf.base(accum, 4);
        let witness_proj: Vec<_> = members
            .iter()
            .map(|m| acc_wnaf.scalar(&(m.0 + revoke_sk.0).invert().unwrap()))
            .collect();
        let mut witness = vec![G1Affine::identity(); size];
        G1Projective::batch_normalize(&witness_proj, &mut witness);

        Self {
            accum: accum.to_affine().into(),
            public_key,
            members,
            witness,
        }
    }
}

impl MemberDataAccess for MemberData {
    fn accumulator(&self) -> Accumulator {
        self.accum
    }

    fn public_key(&self) -> PublicKey {
        self.public_key
    }

    fn member_value(&self, index: usize) -> MemberValue {
        self.members[index]
    }

    fn witness(&self, index: usize) -> Witness {
        self.witness[index].into()
    }

    fn len(&self) -> usize {
        self.members.len()
    }
}

fn prover_calc_witness<A: MemberDataAccess>(
    member_data: &A,
    revoked_indices: &[usize],
    member_index: usize,
) -> Witness {
    if revoked_indices.is_empty() {
        return member_data.witness(member_index);
    }
    let index_count = revoked_indices.len() + 1;
    let mut scalars = vec![Scalar::one(); index_count];
    let mut factors = Vec::with_capacity(index_count);
    for (pos_i, idx) in revoked_indices
        .iter()
        .copied()
        .chain([member_index])
        .enumerate()
    {
        for (pos_j, jdx) in revoked_indices.iter().take(pos_i).copied().enumerate() {
            let s = member_data.member_value(jdx).0 - member_data.member_value(idx).0;
            scalars[pos_i] *= s;
            scalars[pos_j] *= -s;
        }
        factors.push(member_data.witness(idx).0);
    }
    // TODO: sum-of-products
    let wit = scalars
        .into_iter()
        .zip(factors)
        .fold(G1Projective::identity(), |wit, (s, f)| {
            wit + f * s.invert().unwrap()
        });
    wit.to_affine().into()
}

fn prover_calc_witness_accum<A: MemberDataAccess>(
    member_data: &A,
    revoked_indices: &[usize],
    member_index: usize,
) -> (Witness, Accumulator) {
    if revoked_indices.is_empty() {
        return (member_data.witness(member_index), member_data.accumulator());
    }
    let index_count = revoked_indices.len() + 1;
    let mut scalars = vec![Scalar::one(); index_count];
    let mut factors = Vec::with_capacity(index_count);
    for (pos_i, idx) in revoked_indices
        .iter()
        .copied()
        .chain([member_index])
        .enumerate()
    {
        for (pos_j, jdx) in revoked_indices.iter().take(pos_i).copied().enumerate() {
            let s = member_data.member_value(jdx).0 - member_data.member_value(idx).0;
            scalars[pos_i] *= s;
            scalars[pos_j] *= -s;
        }
        factors.push(member_data.witness(idx).0);
    }
    scalars.iter_mut().for_each(|s| {
        *s = s.invert().unwrap();
    });
    // TODO: sum-of-products
    let wit = scalars
        .iter()
        .zip(factors.iter())
        .fold(G1Projective::identity(), |wit, (s, f)| wit + f * s);
    for (pos, idx) in revoked_indices.iter().copied().enumerate() {
        scalars[pos] *= member_data.member_value(idx).0;
    }
    factors[index_count - 1] =
        (wit - factors[index_count - 1] * scalars[index_count - 1]).to_affine();
    scalars[index_count - 1] = -member_data.member_value(member_index).0;
    // TODO: sum-of-products
    let accum = scalars
        .into_iter()
        .zip(factors)
        .fold(G1Projective::identity(), |acc, (s, f)| acc + f * s);
    let mut ret = [G1Affine::identity(); 2];
    G1Projective::batch_normalize(&[wit, -accum], &mut ret);
    (ret[0].into(), ret[1].into())
}

fn hash_to_g1(input: &[u8]) -> G1Projective {
    const DST: &[u8] = b"bbs-registry;v=1";
    <G1Projective as HashToCurve<ExpandMsgXof<Shake256>>>::hash_to_curve(input, DST)
}

#[derive(Clone, Copy, Debug)]
pub struct Generators {
    issue_pk: G2Affine,
    revoke_pk: G2Affine,
    h0: G1Projective,
    h1: G1Projective,
}

impl Generators {
    pub fn new(issue_pk: &PublicKey, revoke_pk: &PublicKey) -> Self {
        let mut buf = [0u8; G2_UNCOMPRESSED_SIZE + 1 + G2_UNCOMPRESSED_SIZE + 4];
        buf[..G2_UNCOMPRESSED_SIZE].copy_from_slice(&issue_pk.0.to_uncompressed());
        buf[(G2_UNCOMPRESSED_SIZE + 1)..(G2_UNCOMPRESSED_SIZE * 2 + 1)]
            .copy_from_slice(&revoke_pk.0.to_uncompressed());
        let h0 = hash_to_g1(&buf);
        buf[(G2_UNCOMPRESSED_SIZE * 2 + 1)..].copy_from_slice(&1u32.to_be_bytes());
        let h1 = hash_to_g1(&buf);
        Self {
            issue_pk: issue_pk.0,
            revoke_pk: revoke_pk.0,
            h0,
            h1,
        }
    }

    // FIXME - add serialization
    // add accessors for public keys
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Signature {
    a: G1Affine,
    e: Scalar,
}

impl Signature {
    pub fn new(
        issue_sk: &SecretKey,
        gens: &Generators,
        accum: Accumulator,
        block: BlockValue,
        timestamp: u64,
    ) -> Self {
        let t = Scalar::from(timestamp);
        let e = Self::calc_e(&gens, block.0, t);
        Self::new_raw(issue_sk, gens, accum, block, t, e)
    }

    fn new_raw(
        issue_sk: &SecretKey,
        gens: &Generators,
        accum: Accumulator,
        block: BlockValue,
        t: Scalar,
        e: Scalar,
    ) -> Self {
        let b = Self::calc_b(gens, accum, block, t);
        let a = (b * (issue_sk.0 + e).invert().unwrap()).to_affine();
        Self { a, e }
    }

    pub fn verify(
        &self,
        gens: &Generators,
        accum: Accumulator,
        block: BlockValue,
        t: Scalar,
    ) -> bool {
        let b = Self::calc_b(gens, accum, block, t);
        pairing(
            &self.a,
            &(G2Projective::generator() * self.e + gens.issue_pk).to_affine(),
        ) == pairing(&b.to_affine(), &G2Affine::generator())
    }

    #[inline]
    pub(crate) fn calc_b(
        gens: &Generators,
        accum: Accumulator,
        block: BlockValue,
        t: Scalar,
    ) -> G1Projective {
        // TODO: sum-of-products
        G1Projective::generator() + gens.h0 * block.0 + gens.h1 * t + accum.0
    }

    #[inline]
    pub fn calc_e(gens: &Generators, q: Scalar, t: Scalar) -> Scalar {
        // TODO - use a DST?
        let mut e_hash = HashScalar::new(None);
        e_hash.update(&gens.issue_pk.to_uncompressed());
        e_hash.update(&[0]);
        e_hash.update(&gens.revoke_pk.to_uncompressed());
        e_hash.update(&[0]);
        e_hash.update(&q.to_bytes());
        e_hash.update(&[0]);
        e_hash.update(&t.to_bytes());
        e_hash.finalize()
    }

    // FIXME - add serialization
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    issue_pk: PublicKey,
    revoke_pk: PublicKey,
    accum: Accumulator,
    witness: Witness,
    signature: Signature,
    timestamp: u64,
}

impl Token {
    pub fn new(
        gens: &Generators,
        accum: Accumulator,
        witness: Witness,
        signature: Signature,
        timestamp: u64,
    ) -> Self {
        Self {
            issue_pk: PublicKey(gens.issue_pk),
            revoke_pk: PublicKey(gens.revoke_pk),
            accum,
            witness,
            signature,
            timestamp,
        }
    }

    pub fn generators(&self) -> Generators {
        Generators::new(&self.issue_pk, &self.revoke_pk)
    }

    pub fn extract<A: MemberDataAccess>(
        member_data: &A,
        revoked_indices: &[usize],
        member_index: usize,
        issue_pk: PublicKey,
        signature: Signature,
        timestamp: u64,
    ) -> Self {
        let (witness, accum) =
            prover_calc_witness_accum(member_data, revoked_indices, member_index);
        Self {
            issue_pk,
            revoke_pk: member_data.public_key(),
            accum,
            witness,
            signature,
            timestamp,
        }
    }

    pub fn verify(&self, block: BlockValue, member: MemberValue) -> bool {
        let gens = self.generators();
        let t = Scalar::from(self.timestamp);
        self.signature.verify(&gens, self.accum, block, t)
            && self
                .accum
                .check_witness(member, self.witness, self.revoke_pk)
    }

    pub fn prepare_proof(
        &self,
        gens: &Generators,
        block: BlockValue,
        member: MemberValue,
        mut rng: impl CryptoRng + Rng,
    ) -> PreparedProof {
        let r1 = random_scalar(&mut rng);
        let r2 = r1.invert().unwrap();
        let t = Scalar::from(self.timestamp);
        let b = Signature::calc_b(&gens, self.accum, block, t);

        // revealed
        let a_prime = self.signature.a * r1;
        let w_prime = self.witness.0 * r1;
        let w_prime_m = w_prime * member.0;
        let b_r1 = b * r1;
        let d = b_r1 - w_prime_m;
        let a_bar = b_r1 - (a_prime * self.signature.e);
        let w_bar = self.accum.0 * r1 - w_prime_m;

        // blindings
        let e_b = random_scalar(&mut rng);
        let q_b = random_scalar(&mut rng);
        let m_b = random_scalar(&mut rng);
        let r2_b = random_scalar(&mut rng);

        let mut c_vals = [G1Affine::identity(); 5];
        G1Projective::batch_normalize(&[a_prime, a_bar, w_prime, w_bar, d], &mut c_vals);
        PreparedProof {
            c_vals: ChallengeValues {
                a_prime: c_vals[0],
                a_bar: c_vals[1],
                w_prime: c_vals[2],
                w_bar: c_vals[3],
                d: c_vals[4],
            },
            h0: gens.h0,
            e: self.signature.e,
            q: block.0,
            m: member.0,
            r2,
            e_b,
            q_b,
            m_b,
            r2_b,
        }
    }

    // FIXME - add serialization
}

#[derive(Clone, Copy, Debug)]
struct ChallengeValues {
    a_prime: G1Affine,
    a_bar: G1Affine,
    w_prime: G1Affine,
    w_bar: G1Affine,
    d: G1Affine,
}

impl ChallengeValues {
    // TODO challenge would likely never be used on its own,
    // only contributed to a multi-proof challenge value
    pub fn hash(&self, c1: &G1Affine, c2: &G1Affine) -> Scalar {
        let mut hash_c = HashScalar::new(None);
        hash_c.update(&self.a_prime.to_uncompressed());
        hash_c.update(&self.a_bar.to_uncompressed());
        hash_c.update(&self.w_prime.to_uncompressed());
        hash_c.update(&self.w_bar.to_uncompressed());
        hash_c.update(&self.d.to_uncompressed());
        hash_c.update(&c1.to_uncompressed());
        hash_c.update(&c2.to_uncompressed());
        hash_c.finalize()
    }
}

#[derive(Clone, Debug)]
pub struct PreparedProof {
    c_vals: ChallengeValues,
    h0: G1Projective,
    e: Scalar,
    q: Scalar,
    m: Scalar,
    r2: Scalar,
    e_b: Scalar,
    q_b: Scalar,
    m_b: Scalar,
    r2_b: Scalar,
}

impl PreparedProof {
    // TODO challenge would likely never be used on its own,
    // only contributed to a multi-proof challenge value
    pub fn create_challenge(&self) -> Scalar {
        let ChallengeValues {
            a_prime,
            w_prime,
            w_bar,
            d,
            ..
        } = self.c_vals;
        let c1 = a_prime * self.e_b + w_prime * self.m_b;
        let c2 = (G1Projective::from(d) - w_bar) * self.r2_b - self.h0 * self.q_b;
        let mut c = [G1Affine::identity(); 2];
        G1Projective::batch_normalize(&[c1, c2], &mut c);
        self.c_vals.hash(&c[0], &c[1])
    }

    pub fn complete(&self, c: Scalar) -> MembershipProof {
        let e_hat = self.e_b + c * self.e;
        let q_hat = self.q_b - c * self.q;
        let m_hat = self.m_b - c * self.m;
        let r2_hat = self.r2_b - c * self.r2;
        MembershipProof {
            c_vals: self.c_vals,
            e_hat,
            q_hat,
            m_hat,
            r2_hat,
        }
    }
}

#[derive(Clone, Debug)]
pub struct MembershipProof {
    c_vals: ChallengeValues,
    e_hat: Scalar,
    q_hat: Scalar,
    m_hat: Scalar,
    r2_hat: Scalar,
}

impl MembershipProof {
    // TODO challenge would likely never be used on its own,
    // only contributed to a multi-proof challenge value
    pub fn create_challenge(&self, gens: &Generators, c: Scalar, timestamp: u64) -> Scalar {
        let ChallengeValues {
            a_prime,
            a_bar,
            w_prime,
            w_bar,
            d,
        } = self.c_vals;
        let c1 = a_prime * self.e_hat + w_prime * self.m_hat + (G1Projective::from(a_bar) - d) * c;
        let c2 = (G1Projective::from(d) - w_bar) * self.r2_hat - gens.h0 * self.q_hat
            + (G1Projective::generator() + gens.h1 * Scalar::from(timestamp)) * c;
        let mut c = [G1Affine::identity(); 2];
        G1Projective::batch_normalize(&[c1, c2], &mut c);
        self.c_vals.hash(&c[0], &c[1])
    }

    pub fn verify(&self, issue_pk: &PublicKey, revoke_pk: &PublicKey) -> bool {
        let ChallengeValues {
            a_prime,
            a_bar,
            w_prime,
            w_bar,
            ..
        } = self.c_vals;
        let zero = a_prime.is_identity() | w_prime.is_identity();
        let aw_bar = (G1Projective::from(a_bar) + w_bar).to_affine();
        // optimized pairing:
        // e(A', P_2k) = e(A_bar, P_2) /\ e(W', P_2z) = e(W_bar, P_2)
        // -> e(A', P_2k) + e(W', P_2z) = e(A_bar + W_bar, P_2)
        let pair = (pairing(&a_prime, &issue_pk.0) + pairing(&w_prime, &revoke_pk.0))
            .ct_eq(&pairing(&aw_bar, &G2Affine::generator()));
        (!zero & pair).into()
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
    pub fn digest(input: impl AsRef<[u8]>, dst: Option<&[u8]>) -> Scalar {
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

    /// Finalize the hasher and return a single Scalar
    pub fn finalize(self) -> Scalar {
        self.read().next()
    }
}

/// The output of a HashScalar, allowing for multiple Scalar values to be read
pub struct HashScalarRead(Sha3XofReader);

impl HashScalarRead {
    /// Read the next non-zero Scalar value from the extensible hash output
    pub fn next(&mut self) -> Scalar {
        let mut buf = [0u8; 64];
        let mut s;
        loop {
            self.0.read(&mut buf);
            s = Scalar::from_bytes_wide(&buf);
            if !bool::from(s.ct_eq(&Scalar::zero())) {
                break s;
            }
        }
    }
}
