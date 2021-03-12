pub mod adaptor;
pub mod cs;
// pub mod generator;
// pub mod prover;
// pub mod verifier;
// pub mod tester;
pub mod polynomials;
pub mod domains;
pub mod fft;
pub mod utils;
pub mod transparent_engine;

pub mod redshift;

pub mod plonk;

pub mod commitments;

pub mod better_cs;

pub use self::better_cs::adaptor::{TranspilationVariant, Transpiler, Adaptor, AdaptorCircuit};
pub use self::better_cs::keys::{SetupPolynomials, SetupPolynomialsPrecomputations, VerificationKey, Proof};

use crate::pairing::Engine;
use crate::{SynthesisError, Circuit};
use crate::multicore::Worker;
use crate::kate_commitment::*;
use self::better_cs::cs::{PlonkCsWidth4WithNextStepParams, PlonkConstraintSystemParams};
use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::*;

use std::time::Duration;
//1
pub fn transpile<E: Engine, C: crate::Circuit<E>>(circuit: C) -> Result<Vec<(usize, TranspilationVariant)>, SynthesisError> {
    let mut transpiler = Transpiler::<E, PlonkCsWidth4WithNextStepParams>::new();

    circuit.synthesize(&mut transpiler).expect("sythesize into traspilation must succeed");

    let hints = transpiler.into_hints();

    Ok(hints)
}

pub fn transpile_with_gates_count<E: Engine, C: crate::Circuit<E>>(circuit: C) -> Result<(usize, Vec<(usize, TranspilationVariant)>), SynthesisError> {
    let mut transpiler = Transpiler::<E, PlonkCsWidth4WithNextStepParams>::new();

    circuit.synthesize(&mut transpiler).expect("sythesize into traspilation must succeed");

    let (n, hints) = transpiler.into_hints_and_num_gates();

    Ok((n, hints))
}

pub fn is_satisfied<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<(), SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::test_assembly::TestAssembly::new();

    adapted_curcuit.synthesize(&mut assembly)
}

pub fn is_satisfied_using_one_shot_check<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<(), SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::one_shot_test_assembly::OneShotTestAssembly::new();

    adapted_curcuit.synthesize(&mut assembly)?;

    let valid = assembly.is_satisfied(false);

    if valid {
        return Ok(());
    } else {
        return Err(SynthesisError::Unsatisfiable);
    }
}
//2
pub fn setup<E: Engine, C: crate::Circuit<E>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>
) -> Result<SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::generator::GeneratorAssembly::<E, PlonkCsWidth4WithNextStepParams>::new();

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();//电路门数补到2^n

    let worker = Worker::new();

    assembly.setup(&worker)//计算selector多项式和置换多项式
}

pub fn make_verification_key<E: Engine, P: PlonkConstraintSystemParams<E>>(
    setup: &SetupPolynomials<E, P>,
    crs: &Crs<E, CrsForMonomialForm>
) -> Result<VerificationKey<E, P>, SynthesisError> {
    let worker = Worker::new();

    let verification_key = VerificationKey::from_setup(
        &setup, 
        &worker, 
        &crs
    )?;

    Ok(verification_key)
}

pub fn make_precomputations<E: Engine, P: PlonkConstraintSystemParams<E>>(
    setup: &SetupPolynomials<E, P>
) -> Result<SetupPolynomialsPrecomputations<E, P>, SynthesisError> {
    let worker = Worker::new();

    let precomputations = SetupPolynomialsPrecomputations::from_setup(
        &setup, 
        &worker, 
    )?;

    Ok(precomputations)
}

pub fn prove_by_steps_wrapped<E: Engine, C: crate::Circuit<E>, T: Transcript<E::Fr>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>,
    setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
    setup_precomputations: Option<&SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>>,
    csr_mon_basis: &Crs<E, CrsForMonomialForm>,
) -> Result<Duration, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;
    use crate::plonk::better_cs::utils::{commit_point_as_xy};
    use crate::plonk::better_cs::prover::prove_steps::{FirstVerifierMessage, SecondVerifierMessage, ThirdVerifierMessage, FourthVerifierMessage};

    use std::time::Instant;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);
    // TODO: num_aux ?= setup.n
    let mut assembly = self::better_cs::prover::ProverAssembly::new_with_size_hints(setup.num_inputs, setup.n);

    let subtime = Instant::now();

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    println!("Synthesis taken {:?}", subtime.elapsed());

    let worker = Worker::new();

    let now = Instant::now();

    let mut transcript = T::new();

    let mut precomputed_omegas = crate::plonk::better_cs::prover::prove_steps::PrecomputedOmegas::< E::Fr, BitReversedOmegas<E::Fr> >::None;
    let mut precomputed_omegas_inv = crate::plonk::better_cs::prover::prove_steps::PrecomputedOmegas::< E::Fr, OmegasInvBitreversed<E::Fr> >::None;

    let mut proof = Proof::<E, PlonkCsWidth4WithNextStepParams>::empty();

    let subtime = Instant::now();
    // 第一个阶段
    let (first_state, first_message) = assembly.first_step_with_monomial_form_key(
        &worker,
        csr_mon_basis,
        &mut precomputed_omegas_inv//none
    )?;

    println!("First step (witness commitment) taken {:?}", subtime.elapsed());

    proof.n = first_message.n;// 门电路个数
    proof.num_inputs = first_message.num_inputs;// 公开输入个数
    proof.input_values = first_message.input_values; // 公开输入值
    proof.wire_commitments = first_message.wire_commitments; // [a(x)][b(x)][c(x)][d(x)]

    for inp in proof.input_values.iter() {
        transcript.commit_field_element(inp); // public inputs value
    }

    for c in proof.wire_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &c);// add point
    }

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    let first_verifier_message = FirstVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        beta,
        gamma,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    // phase 2 start:
    let (second_state, second_message) = self::better_cs::prover::ProverAssembly::second_step_from_first_step(
        first_state,
        first_verifier_message,
        &setup,
        csr_mon_basis,
        &setup_precomputations,
        &mut precomputed_omegas_inv,
        &worker
    )?;

    println!("Second step (grand product commitment) taken {:?}", subtime.elapsed());

    proof.grand_product_commitment = second_message.z_commitment;
    commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

    let alpha = transcript.get_challenge();

    let second_verifier_message = SecondVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        alpha,
        beta,
        gamma,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    // Phase 3 start
    let (third_state, third_message) = self::better_cs::prover::ProverAssembly::third_step_from_second_step(
        second_state,
        second_verifier_message,
        &setup,
        csr_mon_basis,
        &setup_precomputations,
        &mut precomputed_omegas,
        &mut precomputed_omegas_inv,
        &worker
    )?;

    println!("Third step (quotient calculation and commitment) taken {:?}", subtime.elapsed());

    proof.quotient_poly_commitments = third_message.quotient_poly_commitments;

    for c in proof.quotient_poly_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &c);
    }

    let z = transcript.get_challenge();

    let third_verifier_message = ThirdVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        alpha,
        beta,
        gamma,
        z,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    // Phase 4 start
    let (fourth_state, fourth_message) = self::better_cs::prover::ProverAssembly::fourth_step_from_third_step(
        third_state,
        third_verifier_message,
        &setup,
        &worker
    )?;

    println!("Fourth step (openings at z) taken {:?}", subtime.elapsed());

    proof.wire_values_at_z = fourth_message.wire_values_at_z;//a(z),b(z),z(z),d(z)
    proof.wire_values_at_z_omega = fourth_message.wire_values_at_z_omega;//d(z*omega)
    proof.permutation_polynomials_at_z = fourth_message.permutation_polynomials_at_z;//perm_a(z),perm_b(z),perm_c(z)
    proof.grand_product_at_z_omega = fourth_message.grand_product_at_z_omega;//Z(z*omega)
    proof.quotient_polynomial_at_z = fourth_message.quotient_polynomial_at_z;//t(z)
    proof.linearization_polynomial_at_z = fourth_message.linearization_polynomial_at_z;//r(z)

    for el in proof.wire_values_at_z.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.wire_values_at_z_omega.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.permutation_polynomials_at_z.iter() {
        transcript.commit_field_element(el);
    }

    transcript.commit_field_element(&proof.quotient_polynomial_at_z);
    transcript.commit_field_element(&proof.linearization_polynomial_at_z);

    let v = transcript.get_challenge();//没有Z(z*omega)

    let fourth_verifier_message = FourthVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        alpha,
        beta,
        gamma,
        z,
        v,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    /// phase 5 start
    let fifth_message = self::better_cs::prover::ProverAssembly::fifth_step_from_fourth_step(
        fourth_state,
        fourth_verifier_message,
        &setup,
        csr_mon_basis,
        &worker
    )?;

    println!("Fifth step (proving opening at z) taken {:?}", subtime.elapsed());

    proof.opening_at_z_proof = fifth_message.opening_proof_at_z;
    proof.opening_at_z_omega_proof = fifth_message.opening_proof_at_z_omega;

    let proving_time = now.elapsed();
    println!("Proving taken {:?}", proving_time);
    // 11 G1, 11 Fr
    Ok(proving_time)

}
//3
pub fn prove_by_steps<E: Engine, C: crate::Circuit<E>, T: Transcript<E::Fr>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>,
    setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
    setup_precomputations: Option<&SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>>,
    csr_mon_basis: &Crs<E, CrsForMonomialForm>,
) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;
    use crate::plonk::better_cs::utils::{commit_point_as_xy};
    use crate::plonk::better_cs::prover::prove_steps::{FirstVerifierMessage, SecondVerifierMessage, ThirdVerifierMessage, FourthVerifierMessage};

    use std::time::Instant;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);
    // TODO: num_aux ?= setup.n
    let mut assembly = self::better_cs::prover::ProverAssembly::new_with_size_hints(setup.num_inputs, setup.n);

    let subtime = Instant::now();

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    println!("Synthesis taken {:?}", subtime.elapsed());

    let worker = Worker::new();

    let now = Instant::now();

    let mut transcript = T::new();

    let mut precomputed_omegas = crate::plonk::better_cs::prover::prove_steps::PrecomputedOmegas::< E::Fr, BitReversedOmegas<E::Fr> >::None;
    let mut precomputed_omegas_inv = crate::plonk::better_cs::prover::prove_steps::PrecomputedOmegas::< E::Fr, OmegasInvBitreversed<E::Fr> >::None;

    let mut proof = Proof::<E, PlonkCsWidth4WithNextStepParams>::empty();

    let subtime = Instant::now();
    // 第一个阶段
    let (first_state, first_message) = assembly.first_step_with_monomial_form_key(
        &worker,
        csr_mon_basis,
        &mut precomputed_omegas_inv//none
    )?;

    println!("First step (witness commitment) taken {:?}", subtime.elapsed());

    proof.n = first_message.n;// 门电路个数
    proof.num_inputs = first_message.num_inputs;// 公开输入个数
    proof.input_values = first_message.input_values; // 公开输入值
    proof.wire_commitments = first_message.wire_commitments; // [a(x)][b(x)][c(x)][d(x)]

    for inp in proof.input_values.iter() {
        transcript.commit_field_element(inp); // public inputs value
    }

    for c in proof.wire_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &c);// add point
    }

    let beta = transcript.get_challenge();
    let gamma = transcript.get_challenge();

    let first_verifier_message = FirstVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        beta,
        gamma,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    // phase 2 start:
    let (second_state, second_message) = self::better_cs::prover::ProverAssembly::second_step_from_first_step(
        first_state,
        first_verifier_message,
        &setup,
        csr_mon_basis,
        &setup_precomputations,
        &mut precomputed_omegas_inv,
        &worker
    )?;

    println!("Second step (grand product commitment) taken {:?}", subtime.elapsed());

    proof.grand_product_commitment = second_message.z_commitment;
    commit_point_as_xy::<E, _>(&mut transcript, &proof.grand_product_commitment);

    let alpha = transcript.get_challenge();

    let second_verifier_message = SecondVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        alpha,
        beta,
        gamma,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    // Phase 3 start
    let (third_state, third_message) = self::better_cs::prover::ProverAssembly::third_step_from_second_step(
        second_state,
        second_verifier_message,
        &setup,
        csr_mon_basis,
        &setup_precomputations,
        &mut precomputed_omegas,
        &mut precomputed_omegas_inv,
        &worker
    )?;

    println!("Third step (quotient calculation and commitment) taken {:?}", subtime.elapsed());

    proof.quotient_poly_commitments = third_message.quotient_poly_commitments;

    for c in proof.quotient_poly_commitments.iter() {
        commit_point_as_xy::<E, _>(&mut transcript, &c);
    }

    let z = transcript.get_challenge();

    let third_verifier_message = ThirdVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        alpha,
        beta,
        gamma,
        z,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    // Phase 4 start
    let (fourth_state, fourth_message) = self::better_cs::prover::ProverAssembly::fourth_step_from_third_step(
        third_state,
        third_verifier_message,
        &setup,
        &worker
    )?;

    println!("Fourth step (openings at z) taken {:?}", subtime.elapsed());

    proof.wire_values_at_z = fourth_message.wire_values_at_z;//a(z),b(z),z(z),d(z)
    proof.wire_values_at_z_omega = fourth_message.wire_values_at_z_omega;//d(z*omega)
    proof.permutation_polynomials_at_z = fourth_message.permutation_polynomials_at_z;//perm_a(z),perm_b(z),perm_c(z)
    proof.grand_product_at_z_omega = fourth_message.grand_product_at_z_omega;//Z(z*omega)
    proof.quotient_polynomial_at_z = fourth_message.quotient_polynomial_at_z;//t(z)
    proof.linearization_polynomial_at_z = fourth_message.linearization_polynomial_at_z;//r(z)

    for el in proof.wire_values_at_z.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.wire_values_at_z_omega.iter() {
        transcript.commit_field_element(el);
    }

    for el in proof.permutation_polynomials_at_z.iter() {
        transcript.commit_field_element(el);
    }

    transcript.commit_field_element(&proof.quotient_polynomial_at_z);
    transcript.commit_field_element(&proof.linearization_polynomial_at_z);

    let v = transcript.get_challenge();//没有Z(z*omega)

    let fourth_verifier_message = FourthVerifierMessage::<E, PlonkCsWidth4WithNextStepParams> {
        alpha,
        beta,
        gamma,
        z,
        v,

        _marker: std::marker::PhantomData
    };

    let subtime = Instant::now();
    /// phase 5 start
    let fifth_message = self::better_cs::prover::ProverAssembly::fifth_step_from_fourth_step(
        fourth_state,
        fourth_verifier_message,
        &setup,
        csr_mon_basis,
        &worker
    )?;

    println!("Fifth step (proving opening at z) taken {:?}", subtime.elapsed());

    proof.opening_at_z_proof = fifth_message.opening_proof_at_z;
    proof.opening_at_z_omega_proof = fifth_message.opening_proof_at_z_omega;

    println!("Proving taken {:?}", now.elapsed());
    // 11 G1, 11 Fr
    Ok(proof)
}

pub fn prove<E: Engine, C: crate::Circuit<E>, T: Transcript<E::Fr>>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>,
    setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
    csr_mon_basis: &Crs<E, CrsForMonomialForm>,
    crs_lagrange_basis: &Crs<E, CrsForLagrangeForm>
) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let precomputations = make_precomputations(&setup)?;

    // TODO: keep track of num AUX too
    let mut assembly = self::better_cs::prover::ProverAssembly::new_with_size_hints(setup.num_inputs, setup.n);

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let size = setup.n.next_power_of_two();

    let worker = Worker::new();

    let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
    let omegas_inv_bitreversed = <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(size.next_power_of_two());

    use std::time::Instant;
    let now = Instant::now();
    let proof = assembly.prove::<T, _, _>(
        &worker,
        &setup,
        &precomputations,
        &crs_lagrange_basis,
        &csr_mon_basis,
        &omegas_bitreversed,
        &omegas_inv_bitreversed,
    )?;

    println!("Proving taken {:?}", now.elapsed());

    Ok(proof)
}


pub fn prove_from_recomputations<
    E: Engine, 
    C: crate::Circuit<E>, 
    T: Transcript<E::Fr>,
    CP: CTPrecomputations<E::Fr>,
    CPI: CTPrecomputations<E::Fr>,
>(
    circuit: C,
    hints: &Vec<(usize, TranspilationVariant)>,
    setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
    setup_precomputations: &SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>,
    omegas_bitreversed: &CP,
    omegas_inv_bitreversed: &CPI,
    csr_mon_basis: &Crs<E, CrsForMonomialForm>,
    crs_lagrange_basis: &Crs<E, CrsForLagrangeForm>
) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
    use crate::plonk::better_cs::cs::Circuit;

    let adapted_curcuit = AdaptorCircuit::<E, PlonkCsWidth4WithNextStepParams, _>::new(circuit, &hints);

    let mut assembly = self::better_cs::prover::ProverAssembly::new_with_size_hints(setup.num_inputs, setup.n);

    adapted_curcuit.synthesize(&mut assembly)?;
    assembly.finalize();

    let size = setup.n.next_power_of_two();

    assert_eq!(omegas_bitreversed.domain_size(), size);
    assert_eq!(omegas_inv_bitreversed.domain_size(), size);

    let worker = Worker::new();

    use std::time::Instant;
    let now = Instant::now();
    let proof = assembly.prove::<T, _, _>(
        &worker,
        &setup,
        &setup_precomputations,
        &crs_lagrange_basis,
        &csr_mon_basis,
        omegas_bitreversed,
        omegas_inv_bitreversed,
    )?;

    println!("Proving taken {:?}", now.elapsed());

    Ok(proof)
}
// 验证
pub fn verify<E: Engine, T: Transcript<E::Fr>>(
    proof: &Proof<E, PlonkCsWidth4WithNextStepParams>,
    verification_key: &VerificationKey<E, PlonkCsWidth4WithNextStepParams>
) -> Result<bool, SynthesisError> {
    self::better_cs::verifier::verify::<E, PlonkCsWidth4WithNextStepParams, T>(&proof, &verification_key)
}