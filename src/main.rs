use std::time::Instant;

use blake2::{
    crypto_mac::generic_array::{typenum::Unsigned, GenericArray},
    digest::{Update, VariableOutput},
    Blake2b, VarBlake2b,
};
use bls12_381::{hash_to_curve::*, *};
use ff::Field;
use group::{Curve, Wnaf};
use rand::rngs::OsRng;

const G2_UNCOMPRESSED_SIZE: usize = 192;

pub fn isser_create_accum(rk: &Scalar, members: &[Scalar]) -> G1Projective {
    isser_update_accum(rk, G1Projective::generator(), members, true)
}

pub fn isser_update_accum(
    rk: &Scalar,
    base: G1Projective,
    members: &[Scalar],
    add: bool,
) -> G1Projective {
    if members.is_empty() {
        base
    } else {
        let mut acc = members[0] + rk;
        for x in &members[1..] {
            acc *= x + rk;
        }
        if !add {
            acc = acc.invert().unwrap();
        }
        base * acc
    }
}

pub fn check_witness(member: Scalar, witness: &G1Affine, accum: &G1Affine, h: &G2Affine) -> bool {
    pairing(
        witness,
        &(G2Projective::generator() * member + h).to_affine(),
    ) == pairing(accum, &G2Affine::generator())
}

pub fn prover_combine_witness(
    members: &[Scalar],
    witness: &[G1Affine],
    indices: &[usize],
) -> G1Affine {
    if indices.is_empty() {
        panic!("No members for witness");
    } else if indices.len() == 1 {
        return witness[indices[0]];
    }
    let mut scalars = vec![Scalar::one(); indices.len()];
    let mut factors = Vec::with_capacity(indices.len());
    for (pos_i, idx) in indices.iter().copied().enumerate() {
        for (pos_j, jdx) in indices.iter().copied().enumerate() {
            if pos_i < pos_j {
                let s = members[jdx] - members[idx];
                scalars[pos_i] *= s;
                scalars[pos_j] *= -s;
            }
        }
        factors.push(witness[idx]);
    }
    // TODO: sum-of-products
    let mut wit = G1Projective::identity();
    for (s, f) in scalars.into_iter().zip(factors) {
        wit += f * s.invert().unwrap();
    }
    wit.to_affine()
}

pub fn prover_combine_witness_accum(
    members: &[Scalar],
    witness: &[G1Affine],
    indices: &[usize],
    member_index: usize,
) -> (G1Affine, G1Affine) {
    if indices.len() < 2 {
        panic!("Invalid usage");
    }
    let mut scalars = vec![Scalar::one(); indices.len()];
    let mut factors = Vec::with_capacity(indices.len());
    for (pos_i, idx) in indices.iter().copied().enumerate() {
        for (pos_j, jdx) in indices.iter().copied().enumerate() {
            if pos_i < pos_j {
                let s = members[jdx] - members[idx];
                scalars[pos_i] *= s;
                scalars[pos_j] *= -s;
            }
        }
        factors.push(witness[idx]);
    }
    for s in scalars.iter_mut() {
        *s = s.invert().unwrap();
    }
    // TODO: sum-of-products
    let mut wit = G1Projective::identity();
    for (s, f) in scalars.iter().zip(factors.iter()) {
        wit += f * s;
    }
    for (pos, idx) in indices.iter().copied().enumerate() {
        if idx == member_index {
            factors[pos] = (wit - factors[pos] * scalars[pos]).to_affine();
            scalars[pos] = -members[idx];
        } else {
            scalars[pos] *= members[idx];
        }
    }
    // TODO: sum-of-products
    let mut accum = G1Projective::identity();
    for (s, f) in scalars.iter().zip(factors.iter()) {
        accum += f * s;
    }
    (wit.to_affine(), -accum.to_affine())
}

fn hash_to_g1(input: &[u8]) -> G1Projective {
    const DST: &[u8] = b"bbs-registry;v=1";
    <G1Projective as HashToCurve<ExpandMsgXmd<Blake2b>>>::hash_to_curve(input, DST)
}

#[derive(Clone, Copy, Debug)]
pub struct Generators {
    pk: G2Affine,
    h: G2Affine,
    h0: G1Projective,
    h1: G1Projective,
}

impl Generators {
    pub fn new(pk: &G2Affine, h: &G2Affine) -> Self {
        let mut buf = [0u8; G2_UNCOMPRESSED_SIZE * 2 + 2 + 4];
        buf[..G2_UNCOMPRESSED_SIZE].copy_from_slice(&pk.to_uncompressed()[..]);
        buf[G2_UNCOMPRESSED_SIZE + 1..(G2_UNCOMPRESSED_SIZE * 2 + 1)]
            .copy_from_slice(&pk.to_uncompressed());
        buf[G2_UNCOMPRESSED_SIZE + 1..(G2_UNCOMPRESSED_SIZE * 2 + 1)]
            .copy_from_slice(&h.to_uncompressed());
        let h0 = hash_to_g1(&buf);
        buf[G2_UNCOMPRESSED_SIZE * 2 + 2..].copy_from_slice(&1u32.to_be_bytes());
        let h1 = hash_to_g1(&buf);
        Self {
            pk: *pk,
            h: *h,
            h0,
            h1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Signature {
    a: G1Affine,
    e: Scalar,
}

impl Signature {
    pub fn new(
        sk: &Scalar,
        gens: &Generators,
        q: Scalar,
        timestamp: u64,
        accum: &G1Affine,
    ) -> Self {
        let t = Scalar::from(timestamp);
        let mut e_hash = HashScalar::new();
        e_hash.update(&q.to_bytes());
        e_hash.update(&t.to_bytes());
        let e = e_hash.finalize();
        let b = Self::calc_b(gens, q, t, accum);
        let a = (b * (sk + e).invert().unwrap()).to_affine();
        Self { a, e }
    }

    pub fn verify(&self, gens: &Generators, q: Scalar, timestamp: u64, accum: &G1Affine) -> bool {
        let t = Scalar::from(timestamp);
        let b = Self::calc_b(gens, q, t, accum);
        pairing(
            &self.a,
            &(G2Projective::generator() * self.e + gens.pk).to_affine(),
        ) == pairing(&b.to_affine(), &G2Affine::generator())
    }

    #[inline]
    pub(crate) fn calc_b(
        gens: &Generators,
        q: Scalar,
        timestamp: Scalar,
        accum: &G1Affine,
    ) -> G1Projective {
        // TODO - sum-of-products
        gens.h0 * q + gens.h1 * timestamp + accum
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Token {
    pk: G2Affine,
    h: G2Affine,
    timestamp: u64,
    accum: G1Affine,
    witness: G1Affine,
    sig: Signature,
}

impl Token {
    pub fn new(
        gens: &Generators,
        timestamp: u64,
        accum: &G1Affine,
        witness: &G1Affine,
        sig: Signature,
    ) -> Self {
        Self {
            pk: gens.pk,
            h: gens.h,
            timestamp,
            accum: *accum,
            witness: *witness,
            sig,
        }
    }

    pub fn create_q(reg_id: &str, block: u32) -> Scalar {
        let mut hash_q = HashScalar::new();
        hash_q.update(reg_id);
        hash_q.update(b"0");
        hash_q.update(block.to_be_bytes());
        hash_q.finalize()
    }

    pub fn generators(&self) -> Generators {
        Generators::new(&self.pk, &self.h)
    }

    pub fn verify(&self, q: Scalar, m: Scalar) -> bool {
        let gens = self.generators();
        self.sig.verify(&gens, q, self.timestamp, &self.accum)
            && check_witness(m, &self.witness, &self.accum, &self.h)
    }

    pub fn prepare_proof(&self, q: Scalar, m: Scalar) -> PreparedProof {
        let gens = self.generators();
        let r1 = Scalar::random(OsRng); // could ensure not zero
        let r2 = r1.invert().unwrap();
        let t = Scalar::from(self.timestamp);
        let b = Signature::calc_b(&gens, q, t, &self.accum);

        // revealed
        let a_prime = self.sig.a * r1;
        let w_prime = self.witness * r1;
        let w_prime_m = w_prime * m;
        let b_r1 = b * r1;
        let d = b_r1 - w_prime_m;
        let a_bar = b_r1 - (a_prime * self.sig.e);
        let w_bar = self.accum * r1 - w_prime_m;

        // blindings
        let e_b = Scalar::random(OsRng);
        let q_b = Scalar::random(OsRng);
        let m_b = Scalar::random(OsRng);
        let r2_b = Scalar::random(OsRng);

        // commitments
        let c1 = a_prime * e_b + w_prime * m_b;
        let c2 = (d - w_bar) * r2_b - gens.h0 * q_b;

        // TODO - batch normalize
        PreparedProof {
            c_vals: ChallengeValues {
                a_prime: a_prime.into(),
                a_bar: a_bar.into(),
                w_prime: w_prime.into(),
                w_bar: w_bar.into(),
                d: d.into(),
            },
            c1: c1.into(),
            c2: c2.into(),
            e_b,
            q_b,
            m_b,
            r2_b,
            e: self.sig.e,
            q,
            m,
            r2,
        }
    }
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
    // TODO challenge would never be used on its own, only write the bytes somewhere
    pub fn hash(&self, c1: &G1Affine, c2: &G1Affine) -> Scalar {
        let mut hash_c = HashScalar::new();
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
    c1: G1Affine,
    c2: G1Affine,
    e_b: Scalar,
    q_b: Scalar,
    m_b: Scalar,
    r2_b: Scalar,
    // not shared:
    e: Scalar,
    q: Scalar,
    m: Scalar,
    r2: Scalar,
}

impl PreparedProof {
    // TODO challenge would never be used on its own, only write bytes somewhere
    pub fn create_challenge(&self) -> Scalar {
        self.c_vals.hash(&self.c1, &self.c2)
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
    // TODO challenge would never be used on its own, only write bytes somewhere
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
            + (gens.h1 * Scalar::from(timestamp) * c);
        // TODO batch normalize
        let (c1, c2) = (c1.to_affine(), c2.to_affine());
        self.c_vals.hash(&c1, &c2)
    }

    pub fn verify(&self, pk: &G2Affine, h: &G2Affine) -> bool {
        let ChallengeValues {
            a_prime,
            a_bar,
            w_prime,
            w_bar,
            ..
        } = self.c_vals;
        let pair_a = pairing(&a_prime, pk) == pairing(&a_bar, &G2Affine::generator());
        let pair_w = pairing(&w_prime, h) == pairing(&w_bar, &G2Affine::generator());
        pair_a && pair_w
    }
}

#[derive(Debug)]
pub struct HashScalar {
    hasher: VarBlake2b,
}

impl HashScalar {
    pub fn new() -> Self {
        Self {
            hasher: VarBlake2b::new(<Scalar as HashToField>::InputLength::USIZE)
                .expect("Invalid hasher output size"),
        }
    }

    #[inline]
    pub fn digest(input: impl AsRef<[u8]>) -> Scalar {
        let mut state = Self::new();
        state.update(input.as_ref());
        state.finalize()
    }

    pub fn update(&mut self, input: impl AsRef<[u8]>) {
        self.hasher.update(input.as_ref());
    }

    pub fn finalize(self) -> Scalar {
        let mut buf = GenericArray::default();
        self.hasher.finalize_variable(|hash| {
            buf.copy_from_slice(hash);
        });
        Scalar::from_okm(&buf)
    }
}

fn main() {
    let size = 1024;
    let members: Vec<_> = (0..size).map(|_| Scalar::random(OsRng)).collect();
    let rk = Scalar::random(OsRng);
    let start = Instant::now();
    let acc = isser_create_accum(&rk, &members);
    println!("create accum: {:?}", start.elapsed());

    let start = Instant::now();
    let mut wnaf = Wnaf::new();
    let mut acc_wnaf = wnaf.base(acc, 4);
    let witness_proj: Vec<_> = members
        .iter()
        .map(|m| acc_wnaf.scalar(&(m + rk).invert().unwrap()))
        .collect();
    let mut witness = vec![G1Affine::identity(); size];
    G1Projective::batch_normalize(&witness_proj, &mut witness);
    println!("create witnesses: {:?}", start.elapsed());

    let acc = acc.to_affine();
    let h = (G2Projective::generator() * rk).to_affine();

    let start = Instant::now();
    for (mem, wit) in members.iter().zip(&witness) {
        assert!(check_witness(*mem, wit, &acc, &h));
    }
    println!("check witnesses: {:?}", start.elapsed());

    let start = Instant::now();
    let rem_from = size / 2;
    let acc1 = isser_update_accum(&rk, acc.into(), &members[rem_from..], false).to_affine();
    println!("update accum: {:?}", start.elapsed());

    let start = Instant::now();
    let mut removed = Vec::new();
    removed.extend(rem_from..size); // members that were removed
    removed.push(0); // creating witness for member 0
    let (wit, check_accum) = prover_combine_witness_accum(&members, &witness, &removed[..], 0);
    println!("combine witness: {:?}", start.elapsed());
    // check the derived accumulator matches
    assert_eq!(check_accum, acc1);
    // members[0] is in the accum but not the witness:
    // specifically, accum = witness * (members[0] + rk)
    assert!(check_witness(members[0], &wit, &acc1, &h));
    // members[1] is in both the accum and the witness
    assert!(!check_witness(members[1], &acc1, &wit, &h));
    // members[rem_from] is not in the accum or the witness
    assert!(!check_witness(members[rem_from], &wit, &acc1, &h));

    let sk = Scalar::random(OsRng);
    let pk = (G2Projective::generator() * sk).to_affine();
    let reg_id = "registry-id";
    let block = 10001;
    let timestamp = 9992595252;
    let q = Token::create_q(reg_id, block);
    let gens = Generators::new(&pk, &h);
    let start = Instant::now();
    let sig = Signature::new(&sk, &gens, q, timestamp, &acc1);
    let token = Token::new(&gens, timestamp, &acc1, &wit, sig);
    println!("create token: {:?}", start.elapsed());

    let start = Instant::now();
    assert!(token.verify(q, members[0]));
    println!("verify token: {:?}", start.elapsed());

    let start = Instant::now();
    let prepared = token.prepare_proof(q, members[0]);
    println!("prepare proof: {:?}", start.elapsed());
    let c = prepared.create_challenge();
    let proof = prepared.complete(c);
    let start = Instant::now();
    let c2 = proof.create_challenge(&gens, c, timestamp);
    assert!(c == c2);
    assert!(proof.verify(&pk, &h));
    println!("verify proof: {:?}", start.elapsed());
}

#[test]
fn test_combine_witness() {
    // check that for two witnesses, prover_combine_witness(..) = 1/(b-a)*(Wa - Wb)
    // based on:
    // Wa = Acc/(a + k), Wb = Acc/(b + k)
    // Wab = (Wa - Wb)/(b - a)
    //     = [Acc/(a + k) - Acc/(b + k)]/(b - a)
    //     = Acc*[1/(a + k) - 1/(b + k)]/(b - a)
    //     = Acc*[(b + k) - (a + k)]/[(a + k)(b + k)]/(b - a)
    //     = Acc*(b - a)/[(a + k)(b + k)]/(b - a)
    //     = Acc/[(a + k)(b + k)]

    use group::Group;

    let members: Vec<_> = (0..2).map(|_| Scalar::random(OsRng)).collect();
    let witness: Vec<_> = (0..2)
        .map(|_| G1Projective::random(OsRng).to_affine())
        .collect();
    let comb = prover_combine_witness(&members, &witness, &[0, 1]);
    let cmp = ((G1Projective::from(witness[0]) - witness[1])
        * (members[1] - members[0]).invert().unwrap())
    .to_affine();
    assert_eq!(comb, cmp);
}
