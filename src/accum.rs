use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use group::{Curve, Group, Wnaf};
use rand::{CryptoRng, RngCore};
use subtle::{Choice, ConstantTimeEq};

use crate::{common::NonZeroScalar, HashScalar};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct AccumSecretKey(NonZeroScalar);

impl AccumSecretKey {
    pub fn random(rng: impl CryptoRng + RngCore) -> Self {
        Self(NonZeroScalar::random(rng))
    }

    pub fn public_key(&self) -> AccumPublicKey {
        AccumPublicKey((G2Projective::generator() * self.0 .0).to_affine())
    }

    pub fn new_keypair(rng: impl CryptoRng + RngCore) -> (Self, AccumPublicKey) {
        let sk = Self::random(rng);
        (sk, sk.public_key())
    }

    pub(crate) const fn scalar(&self) -> Scalar {
        (self.0).0
    }
}

impl From<NonZeroScalar> for AccumSecretKey {
    fn from(s: NonZeroScalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct AccumPublicKey(pub(crate) G2Affine);

impl From<G2Affine> for AccumPublicKey {
    fn from(p: G2Affine) -> Self {
        Self(p)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct MemberValue(pub(crate) NonZeroScalar);

impl MemberValue {
    pub fn random(rng: impl CryptoRng + RngCore) -> Self {
        Self(NonZeroScalar::random(rng))
    }

    pub(crate) const fn scalar(&self) -> Scalar {
        (self.0).0
    }
}

impl From<NonZeroScalar> for MemberValue {
    fn from(s: NonZeroScalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct BlockValue(pub(crate) NonZeroScalar);

impl BlockValue {
    pub fn new(reg_id: &str, block_index: u32) -> Self {
        let mut hash_q = HashScalar::new(None);
        hash_q.update(reg_id);
        hash_q.update(&[0]);
        hash_q.update(block_index.to_be_bytes());
        Self(hash_q.finalize())
    }

    pub(crate) const fn scalar(&self) -> Scalar {
        (self.0).0
    }
}

impl From<NonZeroScalar> for BlockValue {
    fn from(s: NonZeroScalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Accumulator(pub(crate) G1Affine);

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
    pub fn random(rng: impl CryptoRng + RngCore) -> Self {
        Self(G1Projective::random(rng).into())
    }

    pub fn issuer_update(
        &self,
        members: impl IntoIterator<Item = MemberValue>,
        revoke_sk: &AccumSecretKey,
        add: bool,
    ) -> Self {
        let mut members = members.into_iter();
        let acc = match members.next() {
            Some(m) => {
                let mut acc = members.fold(m.scalar() + revoke_sk.scalar(), |acc, m| {
                    acc * (m.scalar() + revoke_sk.scalar())
                });
                if !add {
                    acc = acc.invert().unwrap();
                }
                (self.0 * acc).into()
            }
            None => self.0,
        };
        Self(acc)
    }

    pub fn issuer_create_witness(
        &self,
        revoke_sk: &AccumSecretKey,
        member: MemberValue,
    ) -> Witness {
        Witness::from(self.0 * (member.scalar() + revoke_sk.scalar()).invert().unwrap())
    }

    pub fn check_witness(
        &self,
        member: MemberValue,
        witness: Witness,
        public_key: AccumPublicKey,
    ) -> Choice {
        pairing(
            &witness.0,
            &(G2Projective::generator() * member.scalar() + public_key.0).to_affine(),
        )
        .ct_eq(&pairing(&self.0, &G2Affine::generator()))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Witness(pub(crate) G1Affine);

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
    fn member_value(&self, index: usize) -> MemberValue;

    fn witness(&self, index: usize) -> Witness;

    fn len(&self) -> usize;
}

pub struct MemberData {
    members: Vec<MemberValue>,
    witness: Vec<G1Affine>,
}

impl MemberData {
    pub fn new(members: Vec<MemberValue>, witness: Vec<G1Affine>) -> Self {
        Self { members, witness }
    }

    pub fn create(
        revoke_sk: &AccumSecretKey,
        size: usize,
        mut rng: impl CryptoRng + RngCore,
    ) -> (Accumulator, Self) {
        let accum = Accumulator::random(&mut rng);
        let members: Vec<_> = (0..size).map(|_| MemberValue::random(&mut rng)).collect();

        let mut wnaf = Wnaf::new();
        let mut acc_wnaf = wnaf.base(accum.0.into(), 4);
        let witness_proj: Vec<_> = members
            .iter()
            .map(|m| acc_wnaf.scalar(&(m.scalar() + revoke_sk.scalar()).invert().unwrap()))
            .collect();
        let mut witness = vec![G1Affine::identity(); size];
        G1Projective::batch_normalize(&witness_proj, &mut witness);

        (accum, Self { members, witness })
    }
}

impl MemberDataAccess for MemberData {
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

// pub(crate) fn prover_calc_witness<A: MemberDataAccess>(
//     member_data: &A,
//     revoked_indices: &[usize],
//     member_index: usize,
// ) -> Witness {
//     if revoked_indices.is_empty() {
//         return member_data.witness(member_index);
//     }
//     let index_count = revoked_indices.len() + 1;
//     let mut scalars = vec![Scalar::one(); index_count];
//     let mut factors = Vec::with_capacity(index_count);
//     for (pos_i, idx) in revoked_indices
//         .iter()
//         .copied()
//         .chain([member_index])
//         .enumerate()
//     {
//         for (pos_j, jdx) in revoked_indices.iter().take(pos_i).copied().enumerate() {
//             let s = member_data.member_value(jdx).scalar() - member_data.member_value(idx).scalar();
//             scalars[pos_i] *= s;
//             scalars[pos_j] *= -s;
//         }
//         factors.push(member_data.witness(idx).0);
//     }
//     // TODO: sum-of-products
//     let wit = scalars
//         .into_iter()
//         .zip(factors)
//         .fold(G1Projective::identity(), |wit, (s, f)| {
//             wit + f * s.invert().unwrap()
//         });
//     wit.to_affine().into()
// }

pub(crate) fn prover_calc_witness_accum<A: MemberDataAccess>(
    accum: Accumulator,
    member_data: &A,
    revoked_indices: &[usize],
    member_index: usize,
) -> (Witness, Accumulator) {
    if revoked_indices.is_empty() {
        return (member_data.witness(member_index), accum);
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
            let s = member_data.member_value(jdx).scalar() - member_data.member_value(idx).scalar();
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
        scalars[pos] *= member_data.member_value(idx).scalar();
    }
    factors[index_count - 1] =
        (wit - factors[index_count - 1] * scalars[index_count - 1]).to_affine();
    scalars[index_count - 1] = -member_data.member_value(member_index).scalar();
    // TODO: sum-of-products
    let accum = scalars
        .into_iter()
        .zip(factors)
        .fold(G1Projective::identity(), |acc, (s, f)| acc + f * s);
    let mut ret = [G1Affine::identity(); 2];
    G1Projective::batch_normalize(&[wit, -accum], &mut ret);
    (ret[0].into(), ret[1].into())
}
