use std::convert::TryFrom;
// For benchmarking
use std::time::{Duration, Instant};

// For randomness (during paramgen and proof generation)
use rand::{Rng, thread_rng};

// We'll use these interfaces to construct our circuit.
use bellman_ce::{
    Circuit,
    ConstraintSystem,
    SynthesisError,
};
// We're going to use the Groth16 proving system.
use bellman_ce::groth16::{
    create_random_proof,
    generate_random_parameters,
    prepare_verifying_key,
    Proof,
    verify_proof,
};
// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use bellman_ce::pairing::bls12_381::Bls12;
use bellman_ce::pairing::bn256::Bn256;
// Bring in some tools for using pairing-friendly curves
use bellman_ce::pairing::Engine;
use bellman_ce::pairing::ff::{
    Field, PrimeField, ScalarEngine,
};

const MAX_DEGREE: u32 = 10_000_000;

// x^MAX_DEGREE + 2*x + 1 = y
fn equation<E: Engine>(
    mut x: E::Fr,
) -> E::Fr
{
    let mut b = MAX_DEGREE;
    let mut res = E::Fr::one();
    let mut a = x.clone();
    while b > 0 {
        if b & 1 == 1 {
            res.mul_assign(&a);
        }
        a.square();
        b >>= 1;
    }
    // x^MAX_DEGREE + 2*x + 1
    x.double();
    res.add_assign(&x);
    res.add_assign(&E::Fr::one());

    res
}

#[test]
fn test_eq() {
    let x = <Bls12 as ScalarEngine>::Fr::from_str("5").unwrap();
    let y = <Bls12 as ScalarEngine>::Fr::from_str("16640001250008279398557033819890332315468391304350385661936705702440740593305").unwrap();

    let expected_y = equation::<Bls12>(x);
    assert_eq!(y, expected_y);
}

// Prover knows <x,y> s.t.
// x^MAX_DEGREE + 2*x + 1 = y
// x: secret
// y: public
#[derive(Clone)]
struct equationDemo<E: Engine> {
    x: Option<E::Fr>,
}

// (x^{MAX_DEGREE - 1} + 2) * x = y -1
impl<E: Engine> Circuit<E> for equationDemo<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError>
    {
        assert!(MAX_DEGREE > 1, "should do");
        // Allocate x.
        let x_value = self.x.clone();
        let x = cs.alloc(|| "x", || {
            x_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut a = x.clone();
        let mut a_value = self.x;

        let mut res = cs.alloc(|| "res", || {
            Ok(E::Fr::one())
        })?;
        let mut res_value = Some(E::Fr::one());

        let mut b = MAX_DEGREE - 1;
        while b > 0 {
            // x^{MAX_DEGREE - 1}
            let cs = &mut cs.namespace(|| format!("iter"));

            if b & 1 == 1 {
                // tmp = res * a
                let tmp_value = a_value.map(|mut e| {
                    e.mul_assign(&res_value.unwrap());
                    e
                });

                let tmp = cs.alloc(|| "tmp", || {
                    tmp_value.ok_or(SynthesisError::AssignmentMissing)
                })?;

                cs.enforce(
                    || "tmp = res * a",
                    |lc| lc + res,
                    |lc| lc + a,
                    |lc| lc + tmp,
                );

                res = tmp;
                res_value = tmp_value;
            }
            let a2_value = a_value.map(|mut e| {
                e.square();
                e
            });

            let a2 = cs.alloc(|| "a2", || {
                a2_value.ok_or(SynthesisError::AssignmentMissing)
            })?;

            cs.enforce(
                || "a2 = a * a",
                |lc| lc + a,
                |lc| lc + a,
                |lc| lc + a2,
            );

            a = a2;
            a_value = a2_value;

            b = b >> 1;
        }

        let two = E::Fr::from_str("2").unwrap();
        //(x^{MAX_DEGREE - 1} + 2) * x = y -1
        let y_value = res_value.map(|mut e| {
            e.add_assign(&two);
            e.mul_assign(&x_value.unwrap());
            e.add_assign(&E::Fr::one());

            e
        });
        let y = cs.alloc_input(|| "y", || {
            y_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let mut minus_one = E::Fr::one();
        minus_one.negate();

        cs.enforce(
            || "(x^{MAX_DEGREE - 1} + 2) * x = y -1",
            |lc| lc + res + (two, CS::one()),
            |lc| lc + x,
            |lc| lc + y + (minus_one, CS::one()),
        );


        Ok(())
    }
}

#[test]
fn test_eq_bls12() {
    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let rng = &mut thread_rng();

    // Generate the MiMC round constants

    println!("Creating parameters...");

    // Create parameters for our circuit
    let params = {
        let c = equationDemo::<Bls12> {
            x: None,
        };

        generate_random_parameters(c, rng).unwrap()
    };

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    // Let's benchmark stuff!
    const SAMPLES: u32 = 100;
    let mut total_proving = Duration::new(0, 0);
    let mut total_verifying = Duration::new(0, 0);

    // Just a place to put the proof data, so we can
    // benchmark deserialization.
    let mut proof_vec = vec![];

    for _ in 0..SAMPLES {
        // Generate a random preimage and compute the image
        // let xl = rng.gen();
        let x = rng.gen();
        let y = equation::<Bls12>(x);
        proof_vec.truncate(0);

        let start = Instant::now();
        {
            // Create an instance of our circuit (with the
            // witness)
            let c = equationDemo {
                x: Some(x)
            };

            // Create a groth16 proof with our parameters.
            let proof = create_random_proof(c, &params, rng).unwrap();

            proof.write(&mut proof_vec).unwrap();
        }

        total_proving += start.elapsed();

        let start = Instant::now();
        let proof = Proof::read(&proof_vec[..]).unwrap();
        // Check the proof
        assert!(verify_proof(
            &pvk,
            &proof,
            &[y],
        ).unwrap());
        total_verifying += start.elapsed();
    }
    let proving_avg = total_proving / SAMPLES;
    let proving_avg = proving_avg.subsec_nanos() as f64 / 1_000_000_000f64
        + (proving_avg.as_secs() as f64);

    let verifying_avg = total_verifying / SAMPLES;
    let verifying_avg = verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64
        + (verifying_avg.as_secs() as f64);

    println!("Average proving time: {:?} seconds", proving_avg);
    println!("Average verifying time: {:?} seconds", verifying_avg);
}
//
// #[test]
// fn test_mimc_bn256() {
//     // This may not be cryptographically safe, use
//     // `OsRng` (for example) in production software.
//     let rng = &mut thread_rng();
//
//     // Generate the MiMC round constants
//     let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
//
//     println!("Creating parameters...");
//
//     // Create parameters for our circuit
//     let params = {
//         let c = MiMCDemo::<Bn256> {
//             xl: None,
//             xr: None,
//             constants: &constants
//         };
//
//         generate_random_parameters(c, rng).unwrap()
//     };
//
//     // Prepare the verification key (for proof verification)
//     let pvk = prepare_verifying_key(&params.vk);
//
//     println!("Creating proofs...");
//
//     // Let's benchmark stuff!
//     // const SAMPLES: u32 = 50;
//     const SAMPLES: u32 = 1;
//     let mut total_proving = Duration::new(0, 0);
//     let mut total_verifying = Duration::new(0, 0);
//
//     // Just a place to put the proof data, so we can
//     // benchmark deserialization.
//     let mut proof_vec = vec![];
//
//     for _ in 0..SAMPLES {
//         // Generate a random preimage and compute the image
//         let xl = rng.gen();
//         let xr = rng.gen();
//         let image = mimc::<Bn256>(xl, xr, &constants);
//
//         proof_vec.truncate(0);
//
//         let start = Instant::now();
//         {
//             // Create an instance of our circuit (with the
//             // witness)
//             let c = MiMCDemo {
//                 xl: Some(xl),
//                 xr: Some(xr),
//                 constants: &constants
//             };
//
//             // Create a groth16 proof with our parameters.
//             let proof = create_random_proof(c, &params, rng).unwrap();
//
//             proof.write(&mut proof_vec).unwrap();
//         }
//
//         total_proving += start.elapsed();
//
//         let start = Instant::now();
//         let proof = Proof::read(&proof_vec[..]).unwrap();
//         // Check the proof
//         assert!(verify_proof(
//             &pvk,
//             &proof,
//             &[image]
//         ).unwrap());
//         total_verifying += start.elapsed();
//     }
//     let proving_avg = total_proving / SAMPLES;
//     let proving_avg = proving_avg.subsec_nanos() as f64 / 1_000_000_000f64
//                       + (proving_avg.as_secs() as f64);
//
//     let verifying_avg = total_verifying / SAMPLES;
//     let verifying_avg = verifying_avg.subsec_nanos() as f64 / 1_000_000_000f64
//                       + (verifying_avg.as_secs() as f64);
//
//     println!("Average proving time: {:?} seconds", proving_avg);
//     println!("Average verifying time: {:?} seconds", verifying_avg);
// }
//
//
// #[cfg(feature = "plonk")]
// #[test]
// fn test_mimc_transpilation_into_plonk() {
//     use bellman_ce::plonk::adaptor::alternative::Transpiler;
//     // This may not be cryptographically safe, use
//     // `OsRng` (for example) in production software.
//     let rng = &mut thread_rng();
//
//     // Generate the MiMC round constants
//     let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
//
//     let c = MiMCDemo::<Bn256> {
//         xl: None,
//         xr: None,
//         constants: &constants
//     };
//
//     let mut transpiler = Transpiler::new();
//
//     c.synthesize(&mut transpiler).unwrap();
// }
