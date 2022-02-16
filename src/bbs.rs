use bls12_381::{
    hash_to_curve::*, pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar,
};
use group::Curve;
use rand::{CryptoRng, RngCore};
use sha3::Shake256;
use subtle::{Choice, ConstantTimeEq};

use crate::{
    accum::{
        prover_calc_witness_accum, AccumPublicKey, Accumulator, BlockValue, MemberDataAccess,
        MemberValue, Witness,
    },
    common::{HashScalar, NonZeroScalar},
};

const G2_UNCOMPRESSED_SIZE: usize = 192;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct BbsSecretKey(NonZeroScalar);

impl BbsSecretKey {
    pub fn random(rng: impl CryptoRng + RngCore) -> Self {
        Self(NonZeroScalar::random(rng))
    }

    pub fn public_key(&self) -> BbsPublicKey {
        BbsPublicKey((G2Projective::generator() * self.0 .0).to_affine())
    }

    pub fn new_keypair(rng: impl CryptoRng + RngCore) -> (Self, BbsPublicKey) {
        let sk = Self::random(rng);
        (sk, sk.public_key())
    }

    const fn scalar(&self) -> Scalar {
        (self.0).0
    }
}

impl From<NonZeroScalar> for BbsSecretKey {
    fn from(s: NonZeroScalar) -> Self {
        Self(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct BbsPublicKey(G2Affine);

impl From<G2Affine> for BbsPublicKey {
    fn from(p: G2Affine) -> Self {
        Self(p)
    }
}

fn hash_to_g1(input: &[u8]) -> G1Projective {
    const DST: &[u8] = b"bbs-registry;v=1";
    <G1Projective as HashToCurve<ExpandMsgXof<Shake256>>>::hash_to_curve(input, DST)
}

#[derive(Clone, Copy, Debug)]
pub struct BbsGenerators {
    issue_pk: G2Affine,
    revoke_pk: G2Affine,
    h0: G1Projective,
    h1: G1Projective,
}

impl BbsGenerators {
    pub fn new(issue_pk: &BbsPublicKey, revoke_pk: &AccumPublicKey) -> Self {
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

    // TODO - add serialization
    // add accessors for public keys
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BbsSignature {
    a: G1Affine,
    e: NonZeroScalar,
}

impl BbsSignature {
    pub fn new(
        issue_sk: &BbsSecretKey,
        gens: &BbsGenerators,
        accum: Accumulator,
        block: BlockValue,
        timestamp: u64,
    ) -> Self {
        // TODO add Timestamp type and require as input
        let t = NonZeroScalar(Scalar::from(timestamp));
        let e = Self::calc_e(&gens, block.0, t);
        Self::new_raw(issue_sk, gens, accum, block, t, e)
    }

    fn new_raw(
        issue_sk: &BbsSecretKey,
        gens: &BbsGenerators,
        accum: Accumulator,
        block: BlockValue,
        t: NonZeroScalar,
        e: NonZeroScalar,
    ) -> Self {
        let b = Self::calc_b(gens, accum, block, t);
        let a = (b * (issue_sk.scalar() + e.0).invert().unwrap()).to_affine();
        Self { a, e }
    }

    pub fn verify(
        &self,
        gens: &BbsGenerators,
        accum: Accumulator,
        block: BlockValue,
        timestamp: u64,
    ) -> Choice {
        // TODO add Timestamp type and require as input
        let t = NonZeroScalar(Scalar::from(timestamp));
        let b = Self::calc_b(gens, accum, block, t);
        pairing(
            &self.a,
            &(G2Projective::generator() * self.e.0 + gens.issue_pk).to_affine(),
        )
        .ct_eq(&pairing(&b.to_affine(), &G2Affine::generator()))
    }

    #[inline]
    pub(crate) fn calc_b(
        gens: &BbsGenerators,
        accum: Accumulator,
        block: BlockValue,
        t: NonZeroScalar,
    ) -> G1Projective {
        // TODO: sum-of-products
        G1Projective::generator() + gens.h0 * block.scalar() + gens.h1 * t.0 + accum.0
    }

    #[inline]
    pub fn calc_e(gens: &BbsGenerators, q: NonZeroScalar, t: NonZeroScalar) -> NonZeroScalar {
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

    // TODO - add serialization
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BbsToken {
    issue_pk: BbsPublicKey,
    revoke_pk: AccumPublicKey,
    accum: Accumulator,
    witness: Witness,
    signature: BbsSignature,
    timestamp: u64,
}

impl BbsToken {
    pub fn new(
        gens: &BbsGenerators,
        accum: Accumulator,
        revoke_pk: AccumPublicKey,
        witness: Witness,
        signature: BbsSignature,
        timestamp: u64,
    ) -> Self {
        Self {
            issue_pk: BbsPublicKey(gens.issue_pk),
            revoke_pk,
            accum,
            witness,
            signature,
            timestamp,
        }
    }

    pub fn generators(&self) -> BbsGenerators {
        BbsGenerators::new(&self.issue_pk, &self.revoke_pk)
    }

    pub fn extract<A: MemberDataAccess>(
        member_data: &A,
        revoked_indices: &[usize],
        member_index: usize,
        issue_pk: BbsPublicKey,
        signature: BbsSignature,
        accum: Accumulator,
        revoke_pk: AccumPublicKey,
        timestamp: u64,
    ) -> Self {
        let (witness, accum) =
            prover_calc_witness_accum(accum, member_data, revoked_indices, member_index);
        Self {
            issue_pk,
            revoke_pk,
            accum,
            witness,
            signature,
            timestamp,
        }
    }

    pub fn verify(&self, block: BlockValue, member: MemberValue) -> Choice {
        let gens = self.generators();
        self.signature
            .verify(&gens, self.accum, block, self.timestamp)
            & self
                .accum
                .check_witness(member, self.witness, self.revoke_pk)
    }

    pub fn prepare_proof(
        &self,
        gens: &BbsGenerators,
        block: BlockValue,
        member: MemberValue,
        mut rng: impl CryptoRng + RngCore,
    ) -> BbsPreparedProof {
        let r1 = NonZeroScalar::random(&mut rng);
        let r2 = r1.invert();
        // TODO add Timestamp type
        let t = NonZeroScalar(Scalar::from(self.timestamp));
        let b = BbsSignature::calc_b(&gens, self.accum, block, t);

        // revealed
        let a_prime = self.signature.a * r1.0;
        let w_prime = self.witness.0 * r1.0;
        let w_prime_m = w_prime * member.scalar();
        let b_r1 = b * r1.0;
        let d = b_r1 - w_prime_m;
        let a_bar = b_r1 - (a_prime * self.signature.e.0);
        let w_bar = self.accum.0 * r1.0 - w_prime_m;

        // blindings
        let e_b = NonZeroScalar::random(&mut rng);
        let q_b = NonZeroScalar::random(&mut rng);
        let m_b = NonZeroScalar::random(&mut rng);
        let r2_b = NonZeroScalar::random(&mut rng);

        let mut c_vals = [G1Affine::identity(); 5];
        G1Projective::batch_normalize(&[a_prime, a_bar, w_prime, w_bar, d], &mut c_vals);
        BbsPreparedProof {
            c_vals: BbsChallengeValues {
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

    // TODO - add serialization
}

#[derive(Clone, Copy, Debug)]
struct BbsChallengeValues {
    a_prime: G1Affine,
    a_bar: G1Affine,
    w_prime: G1Affine,
    w_bar: G1Affine,
    d: G1Affine,
}

impl BbsChallengeValues {
    // TODO challenge would likely never be used on its own,
    // only contributed to a multi-proof challenge value
    pub fn hash(&self, c1: &G1Affine, c2: &G1Affine) -> NonZeroScalar {
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
pub struct BbsPreparedProof {
    c_vals: BbsChallengeValues,
    h0: G1Projective,
    e: NonZeroScalar,
    q: NonZeroScalar,
    m: NonZeroScalar,
    r2: NonZeroScalar,
    e_b: NonZeroScalar,
    q_b: NonZeroScalar,
    m_b: NonZeroScalar,
    r2_b: NonZeroScalar,
}

impl BbsPreparedProof {
    // TODO challenge would likely never be used on its own,
    // only contributed to a multi-proof challenge value
    pub fn create_challenge(&self) -> NonZeroScalar {
        let BbsChallengeValues {
            a_prime,
            w_prime,
            w_bar,
            d,
            ..
        } = self.c_vals;
        // TODO sum-of-products
        let c1 = a_prime * self.e_b.0 + w_prime * self.m_b.0;
        let c2 = (G1Projective::from(d) - w_bar) * self.r2_b.0 - self.h0 * self.q_b.0;
        let mut c = [G1Affine::identity(); 2];
        G1Projective::batch_normalize(&[c1, c2], &mut c);
        self.c_vals.hash(&c[0], &c[1])
    }

    pub fn complete(&self, c: NonZeroScalar) -> BbsMembershipProof {
        let e_hat = NonZeroScalar(self.e_b.0 + c.0 * self.e.0);
        let q_hat = NonZeroScalar(self.q_b.0 - c.0 * self.q.0);
        let m_hat = NonZeroScalar(self.m_b.0 - c.0 * self.m.0);
        let r2_hat = NonZeroScalar(self.r2_b.0 - c.0 * self.r2.0);
        BbsMembershipProof {
            c_vals: self.c_vals,
            e_hat,
            q_hat,
            m_hat,
            r2_hat,
        }
    }
}

#[derive(Clone, Debug)]
pub struct BbsMembershipProof {
    c_vals: BbsChallengeValues,
    e_hat: NonZeroScalar,
    q_hat: NonZeroScalar,
    m_hat: NonZeroScalar,
    r2_hat: NonZeroScalar,
}

impl BbsMembershipProof {
    // TODO challenge would likely never be used on its own,
    // only contributed to a multi-proof challenge value
    pub fn create_challenge(
        &self,
        gens: &BbsGenerators,
        c: NonZeroScalar,
        timestamp: u64,
    ) -> NonZeroScalar {
        let BbsChallengeValues {
            a_prime,
            a_bar,
            w_prime,
            w_bar,
            d,
        } = self.c_vals;
        // TODO sum-of-products
        let c1 =
            a_prime * self.e_hat.0 + w_prime * self.m_hat.0 + (G1Projective::from(a_bar) - d) * c.0;
        let c2 = (G1Projective::from(d) - w_bar) * self.r2_hat.0 - gens.h0 * self.q_hat.0
            + (G1Projective::generator() + gens.h1 * Scalar::from(timestamp)) * c.0;
        let mut c_norm = [G1Affine::identity(); 2];
        G1Projective::batch_normalize(&[c1, c2], &mut c_norm);
        self.c_vals.hash(&c_norm[0], &c_norm[1])
    }

    pub fn verify(&self, issue_pk: &BbsPublicKey, revoke_pk: &AccumPublicKey) -> bool {
        let BbsChallengeValues {
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
