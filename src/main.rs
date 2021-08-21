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

fn hash_to_g1(input: &[u8]) -> G1Projective {
    const DST: &[u8] = b"bbs-registry;v=1";
    <G1Projective as HashToCurve<ExpandMsgXmd<Blake2b>>>::hash_to_curve(input, DST)
}

fn create_generators(pk: &G2Affine, h: &G2Affine) -> (G1Projective, G1Projective) {
    let mut buf = [0u8; G2_UNCOMPRESSED_SIZE * 2 + 2 + 4];
    buf[..G2_UNCOMPRESSED_SIZE].copy_from_slice(&pk.to_uncompressed()[..]);
    buf[G2_UNCOMPRESSED_SIZE + 1..(G2_UNCOMPRESSED_SIZE * 2 + 1)]
        .copy_from_slice(&pk.to_uncompressed());
    buf[G2_UNCOMPRESSED_SIZE + 1..(G2_UNCOMPRESSED_SIZE * 2 + 1)]
        .copy_from_slice(&h.to_uncompressed());
    let h0 = hash_to_g1(&buf);
    buf[G2_UNCOMPRESSED_SIZE * 2 + 2..].copy_from_slice(&1u32.to_be_bytes());
    let h1 = hash_to_g1(&buf);
    (h0, h1)
}

pub struct Token {
    pk: G2Affine,
    h: G2Affine,
    timestamp: u64,
    accum: G1Affine,
    witness: G1Affine,
    sig: G1Affine,
    e: Scalar,
}

impl Token {
    pub fn new(
        sk: &Scalar,
        pk: &G2Affine,
        h: &G2Affine,
        q: Scalar,
        timestamp: u64,
        accum: &G1Affine,
        witness: &G1Affine,
    ) -> Self {
        let (h0, h1) = create_generators(pk, h);
        let e = Scalar::random(OsRng); // will be deterministic
        let b = h0 * q + h1 * Scalar::from(timestamp) + accum;
        let sig = (b * (sk + e).invert().unwrap()).to_affine();
        Self {
            pk: *pk,
            h: *h,
            timestamp,
            accum: *accum,
            witness: *witness,
            sig,
            e,
        }
    }

    pub fn create_q(reg_id: &str, block: u32) -> Scalar {
        let mut hash_q = VarBlake2b::new(<Scalar as HashToField>::InputLength::USIZE).unwrap();
        hash_q.update(reg_id);
        hash_q.update(b"0");
        hash_q.update(block.to_be_bytes());
        let mut buf = GenericArray::default();
        hash_q.finalize_variable(|hash| {
            buf.copy_from_slice(hash);
        });
        Scalar::from_okm(&buf)
    }

    pub fn verify(&self, q: Scalar, member: Scalar) -> bool {
        let (h0, h1) = create_generators(&self.pk, &self.h);
        let b = h0 * q + h1 * Scalar::from(self.timestamp) + self.accum;
        pairing(
            &self.sig,
            &(G2Projective::generator() * self.e + self.pk).to_affine(),
        ) == pairing(&b.to_affine(), &G2Affine::generator())
            && check_witness(member, &self.witness, &self.accum, &self.h)
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
    let wit = prover_combine_witness(&members, &witness, &removed[..]);
    println!("combine witness: {:?}", start.elapsed());
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
    let token = Token::new(&sk, &pk, &h, q, timestamp, &acc1, &wit);
    assert!(token.verify(q, members[0]));
    println!("done");
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
