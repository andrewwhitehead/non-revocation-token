use std::time::Instant;

use bls12_381::*;
use ff::Field;
use group::{Curve, Wnaf};
use rand::rngs::OsRng;

pub fn isser_create_accum(sk: &Scalar, members: &[Scalar]) -> G1Projective {
    isser_update_accum(sk, G1Projective::generator(), members, true)
}

pub fn isser_update_accum(
    sk: &Scalar,
    base: G1Projective,
    members: &[Scalar],
    add: bool,
) -> G1Projective {
    if members.is_empty() {
        base
    } else {
        let mut acc = members[0] + sk;
        for x in &members[1..] {
            acc *= x + sk;
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

fn main() {
    let size = 1024;
    let members: Vec<_> = (0..size).map(|_| Scalar::random(OsRng)).collect();
    let sk = Scalar::random(OsRng);
    let start = Instant::now();
    let acc = isser_create_accum(&sk, &members);
    println!("create accum: {:?}", start.elapsed());

    let start = Instant::now();
    let mut wnaf = Wnaf::new();
    let mut acc_wnaf = wnaf.base(acc, 4);
    let witness_proj: Vec<_> = members
        .iter()
        .map(|m| acc_wnaf.scalar(&(m + sk).invert().unwrap()))
        .collect();
    let mut witness = vec![G1Affine::identity(); size];
    G1Projective::batch_normalize(&witness_proj, &mut witness);
    println!("create witnesses: {:?}", start.elapsed());

    let acc = acc.to_affine();
    let h = (G2Projective::generator() * sk).to_affine();

    let start = Instant::now();
    for (mem, wit) in members.iter().zip(&witness) {
        assert!(check_witness(*mem, wit, &acc, &h));
    }
    println!("check witnesses: {:?}", start.elapsed());

    let start = Instant::now();
    let rem_from = size / 2;
    let acc1 = isser_update_accum(&sk, acc.into(), &members[rem_from..], false).to_affine();
    println!("update accum: {:?}", start.elapsed());

    let start = Instant::now();
    let mut removed = Vec::new();
    removed.extend(rem_from..size); // members that were removed
    removed.push(0); // creating witness for member 0
    let wit = prover_combine_witness(&members, &witness, &removed[..]);
    println!("combine witness: {:?}", start.elapsed());
    // members[0] is in the accum but not the witness:
    // specifically, accum = witness * (members[0] + sk)
    assert!(check_witness(members[0], &wit, &acc1, &h));
    // members[1] is in both the accum and the witness
    assert!(!check_witness(members[1], &acc1, &wit, &h));
    // members[rem_from] is not in the accum or the witness
    assert!(!check_witness(members[rem_from], &wit, &acc1, &h));
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
