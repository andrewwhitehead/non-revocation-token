use std::time::Instant;

use blake2::{
    crypto_mac::generic_array::{typenum::Unsigned, GenericArray},
    digest::{Update, VariableOutput},
    Blake2b, VarBlake2b,
};
use bls12_381::{hash_to_curve::*, *};
use ff::Field;
use group::{Curve, Group, Wnaf};
use rand::{thread_rng, CryptoRng, Rng};
use subtle::ConstantTimeEq;

const G2_UNCOMPRESSED_SIZE: usize = 192;

fn random_scalar(mut rng: impl CryptoRng + Rng) -> Scalar {
    loop {
        let s = Scalar::random(&mut rng);
        if !s.is_zero() {
            break s;
        }
    }
}

pub fn issuer_update_accum(
    secret: &Scalar,
    base: impl Into<G1Projective>,
    members: impl IntoIterator<Item = Scalar>,
    add: bool,
) -> G1Projective {
    let mut members = members.into_iter();
    match members.next() {
        Some(m) => {
            let mut acc = members.fold(m + secret, |acc, m| acc * (m + secret));
            if !add {
                acc = acc.invert().unwrap();
            }
            base.into() * acc
        }
        None => base.into(),
    }
}

pub fn check_witness(
    member: Scalar,
    witness: &G1Affine,
    accum: &G1Affine,
    public_key: &G2Affine,
) -> bool {
    pairing(
        witness,
        &(G2Projective::generator() * member + public_key).to_affine(),
    ) == pairing(accum, &G2Affine::generator())
}

pub trait MemberDataAccess {
    fn get_accum(&self) -> G1Affine;

    fn get_public_key(&self) -> G2Affine;

    fn get_member(&self, index: usize) -> Scalar;

    fn get_witness(&self, index: usize) -> G1Affine;

    fn len(&self) -> usize;
}

pub struct MemberData {
    accum: G1Affine,
    public_key: G2Affine,
    members: Vec<Scalar>,
    witness: Vec<G1Affine>,
}

impl MemberData {
    pub fn new(
        accum: G1Affine,
        public_key: G2Affine,
        members: Vec<Scalar>,
        witness: Vec<G1Affine>,
    ) -> Self {
        Self {
            accum,
            public_key,
            members,
            witness,
        }
    }

    pub fn create(size: usize, secret: &Scalar, mut rng: impl CryptoRng + Rng) -> Self {
        let accum = G1Projective::random(&mut rng);
        let public_key = (G2Projective::generator() * secret).to_affine();
        let members: Vec<_> = (0..size).map(|_| random_scalar(&mut rng)).collect();

        let mut wnaf = Wnaf::new();
        let mut acc_wnaf = wnaf.base(accum, 4);
        let witness_proj: Vec<_> = members
            .iter()
            .map(|m| acc_wnaf.scalar(&(m + secret).invert().unwrap()))
            .collect();
        let mut witness = vec![G1Affine::identity(); size];
        G1Projective::batch_normalize(&witness_proj, &mut witness);

        Self {
            accum: accum.to_affine(),
            public_key,
            members,
            witness,
        }
    }
}

impl MemberDataAccess for MemberData {
    fn get_accum(&self) -> G1Affine {
        self.accum
    }

    fn get_public_key(&self) -> G2Affine {
        self.public_key
    }

    fn get_member(&self, index: usize) -> Scalar {
        self.members[index]
    }

    fn get_witness(&self, index: usize) -> G1Affine {
        self.witness[index]
    }

    fn len(&self) -> usize {
        self.members.len()
    }
}

pub fn prover_combine_witness<A: MemberDataAccess>(member_data: &A, indices: &[usize]) -> G1Affine {
    if indices.is_empty() {
        panic!("No members for witness");
    } else if indices.len() == 1 {
        return member_data.get_witness(indices[0]);
    }
    let mut scalars = vec![Scalar::one(); indices.len()];
    let mut factors = Vec::with_capacity(indices.len());
    for (pos_i, idx) in indices.iter().copied().enumerate() {
        for (pos_j, jdx) in indices.iter().copied().enumerate() {
            if pos_i < pos_j {
                let s = member_data.get_member(jdx) - member_data.get_member(idx);
                scalars[pos_i] *= s;
                scalars[pos_j] *= -s;
            }
        }
        factors.push(member_data.get_witness(idx));
    }
    // TODO: sum-of-products
    let wit = scalars
        .into_iter()
        .zip(factors)
        .fold(G1Projective::identity(), |wit, (s, f)| {
            wit + f * s.invert().unwrap()
        });
    wit.to_affine()
}

pub fn prover_combine_witness_accum<A: MemberDataAccess>(
    member_data: &A,
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
                let s = member_data.get_member(jdx) - member_data.get_member(idx);
                scalars[pos_i] *= s;
                scalars[pos_j] *= -s;
            }
        }
        factors.push(member_data.get_witness(idx));
    }
    scalars.iter_mut().for_each(|s| {
        *s = s.invert().unwrap();
    });
    // TODO: sum-of-products
    let wit = scalars
        .iter()
        .zip(factors.iter())
        .fold(G1Projective::identity(), |wit, (s, f)| wit + f * s);
    for (pos, idx) in indices.iter().copied().enumerate() {
        if idx == member_index {
            factors[pos] = (wit - factors[pos] * scalars[pos]).to_affine();
            scalars[pos] = -member_data.get_member(idx);
        } else {
            scalars[pos] *= member_data.get_member(idx);
        }
    }
    // TODO: sum-of-products
    let accum = scalars
        .into_iter()
        .zip(factors)
        .fold(G1Projective::identity(), |acc, (s, f)| acc + f * s);
    let mut ret = [G1Affine::identity(); 2];
    G1Projective::batch_normalize(&[wit, -accum], &mut ret);
    (ret[0], ret[1])
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
        // TODO: sum-of-products
        G1Projective::generator() + gens.h0 * q + gens.h1 * timestamp + accum
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

    pub fn prepare_proof(
        &self,
        gens: &Generators,
        q: Scalar,
        m: Scalar,
        mut rng: impl CryptoRng + Rng,
    ) -> PreparedProof {
        let r1 = random_scalar(&mut rng);
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
            e: self.sig.e,
            q,
            m,
            r2,
            e_b,
            q_b,
            m_b,
            r2_b,
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
    // TODO challenge would never be used on its own, only write bytes somewhere
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
            + (G1Projective::generator() + gens.h1 * Scalar::from(timestamp)) * c;
        let mut c = [G1Affine::identity(); 2];
        G1Projective::batch_normalize(&[c1, c2], &mut c);
        self.c_vals.hash(&c[0], &c[1])
    }

    pub fn verify(&self, pk: &G2Affine, h: &G2Affine) -> bool {
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
        let pair = (pairing(&a_prime, pk) + pairing(&w_prime, h))
            .ct_eq(&pairing(&aw_bar, &G2Affine::generator()));
        (!zero & pair).into()
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
    let rng = thread_rng();
    let secret = random_scalar(rng.clone());
    let start = Instant::now();
    let member_data = MemberData::create(size, &secret, rng.clone());
    println!("create member data: {:.2?}", start.elapsed());

    let start = Instant::now();
    let max_check = member_data.len().min(10);
    for idx in 0..max_check {
        assert!(check_witness(
            member_data.get_member(idx),
            &member_data.get_witness(idx),
            &member_data.get_accum(),
            &member_data.get_public_key()
        ));
    }
    println!(
        "verify witnesses: {:.2?} each",
        start.elapsed() / max_check as u32
    );

    let start = Instant::now();
    let rem_from = size / 2;
    let acc1 = issuer_update_accum(
        &secret,
        member_data.get_accum(),
        (rem_from..size).map(|idx| member_data.get_member(idx)),
        false,
    )
    .to_affine();
    println!("update accum: {:.2?}", start.elapsed());

    let start = Instant::now();
    let mut removed = Vec::new();
    removed.extend(rem_from..size); // members that were removed
    removed.push(0); // creating witness for member 0
    let (wit, check_accum) = prover_combine_witness_accum(&member_data, &removed[..], 0);
    println!("derive witness and accum: {:.2?}", start.elapsed());

    // check the derived accumulator matches
    assert_eq!(check_accum, acc1);
    let accum_pk = member_data.get_public_key();
    // accum = witness * (members[0] + secret)
    assert!(check_witness(
        member_data.get_member(0),
        &wit,
        &acc1,
        &accum_pk
    ));
    // accum != witness * (members[1] + secret)
    assert!(!check_witness(
        member_data.get_member(1),
        &acc1,
        &wit,
        &accum_pk
    ));

    let issuer_sk = random_scalar(rng.clone());
    let issuer_pk = (G2Projective::generator() * issuer_sk).to_affine();
    let reg_id = "registry-id";
    let block = 10001;
    let timestamp = 9992595252;
    let q = Token::create_q(reg_id, block);
    let gens = Generators::new(&issuer_pk, &accum_pk);
    let start = Instant::now();
    let sig = Signature::new(&issuer_sk, &gens, q, timestamp, &acc1);
    let token = Token::new(&gens, timestamp, &acc1, &wit, sig);
    println!("create token: {:.2?}", start.elapsed());

    let start = Instant::now();
    assert!(token.verify(q, member_data.get_member(0)));
    println!("verify token: {:.2?}", start.elapsed());

    let start = Instant::now();
    let prepared = token.prepare_proof(&gens, q, member_data.get_member(0), rng.clone());
    println!("prepare proof: {:.2?}", start.elapsed());
    let c = prepared.create_challenge();
    let proof = prepared.complete(c);
    let start = Instant::now();
    let c2 = proof.create_challenge(&gens, c, timestamp);
    assert!(c == c2);
    assert!(proof.verify(&issuer_pk, &accum_pk));
    println!("verify proof: {:.2?}", start.elapsed());
}
