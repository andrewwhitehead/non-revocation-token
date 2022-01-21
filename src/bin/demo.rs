use std::time::Instant;

use rand::thread_rng;

use non_revocation_token::{
    BlockValue, Generators, MemberData, MemberDataAccess, SecretKey, Signature, Token,
};

fn main() {
    // issuer setup
    let mut rng = thread_rng();
    let (issue_sk, issue_pk) = SecretKey::keypair(&mut rng);

    // initialize the registry
    let size = 1024;
    let revoke_sk = SecretKey::random(&mut rng);
    let start = Instant::now();
    let member_data = MemberData::create(&revoke_sk, size, &mut rng);
    let revoke_pk = member_data.public_key();
    println!("issuer perform setup: {:.2?}", start.elapsed());

    // verify the witnesses (for testing purposes only)
    let start = Instant::now();
    let max_check = member_data.len().min(10);
    for idx in 0..max_check {
        assert!(member_data.accumulator().check_witness(
            member_data.member_value(idx),
            member_data.witness(idx),
            member_data.public_key()
        ));
    }
    println!(
        "(test) verify a member witness: {:.2?}",
        start.elapsed() / max_check as u32
    );

    // perform revocation for a number of members
    let start = Instant::now();
    let rem_from = size / 2;
    let accum = member_data.accumulator().issuer_update(
        (rem_from..size).map(|idx| member_data.member_value(idx)),
        &revoke_sk,
        false,
    );
    println!(
        "issuer derive a new block accumulator value (half of members): {:.2?}",
        start.elapsed()
    );

    // prepare for publishing
    let gens = Generators::new(&issue_pk, &revoke_pk);
    let reg_id = "registry-id";
    let timestamp = 9992595252;

    // generate a single sample token (usually only the signature is published)
    let start = Instant::now();
    let block_index = 10001;
    let block = BlockValue::new(reg_id, block_index);
    let member_index = 0;
    let member = member_data.member_value(member_index);
    let witness = accum.issuer_create_witness(&revoke_sk, member);
    let signature = Signature::new(&issue_sk, &gens, accum, block, timestamp);
    println!("issuer create a token signature: {:.2?}", start.elapsed());

    // assemble token from issuer-known values for later comparison (testing purposes only)
    let cmp_token = Token::new(&gens, accum, witness, signature, timestamp);

    // extract a token from a published registry
    // does not currently include any parsing
    let start = Instant::now();
    let mut revoked_indices = Vec::with_capacity(size);
    revoked_indices.extend(rem_from..size); // members that were removed
    let token = Token::extract(
        &member_data,
        &revoked_indices[..],
        member_index,
        issue_pk,
        signature,
        timestamp,
    );
    println!("prover extract own token: {:.2?}", start.elapsed());
    assert_eq!(token, cmp_token);

    let start = Instant::now();
    assert!(token.verify(block, member_data.member_value(0)));
    println!("(test) verify a token: {:.2?}", start.elapsed());

    let start = Instant::now();
    let prepared = token.prepare_proof(&gens, block, member_data.member_value(0), &mut rng);
    println!(
        "prover prepare a token proof of knowledge: {:.2?}",
        start.elapsed()
    );
    let c = prepared.create_challenge();
    let proof = prepared.complete(c);
    let start = Instant::now();
    let c2 = proof.create_challenge(&gens, c, timestamp);
    assert!(c == c2);
    assert!(proof.verify(&issue_pk, &revoke_pk));
    println!("verify a token proof of knowledge: {:.2?}", start.elapsed());
}
