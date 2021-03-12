use crate::pairing::{
    Engine
};

use crate::pairing::ff:: {
    Field,
    PrimeField,
};

pub mod dummy_engine;
use self::dummy_engine::*;

use std::marker::PhantomData;

use crate::{
    Circuit,
    ConstraintSystem,
    SynthesisError
};

#[derive(Clone)]
pub(crate) struct XORDemo<E: Engine> {
    pub(crate) a: Option<bool>,
    pub(crate) b: Option<bool>,
    pub(crate) _marker: PhantomData<E>
}

impl<E: Engine> Circuit<E> for XORDemo<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let a_var = cs.alloc(|| "a", || {
            if self.a.is_some() {
                if self.a.unwrap() {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a_boolean_constraint",
            |lc| lc + CS::one() - a_var,
            |lc| lc + a_var,
            |lc| lc
        );

        let b_var = cs.alloc(|| "b", || {
            if self.b.is_some() {
                if self.b.unwrap() {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "b_boolean_constraint",
            |lc| lc + CS::one() - b_var,
            |lc| lc + b_var,
            |lc| lc
        );

        let c_var = cs.alloc_input(|| "c", || {
            if self.a.is_some() && self.b.is_some() {
                if self.a.unwrap() ^ self.b.unwrap() {
                    Ok(E::Fr::one())
                } else {
                    Ok(E::Fr::zero())
                }
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "c_xor_constraint",
            |lc| lc + a_var + a_var,
            |lc| lc + b_var,
            |lc| lc + a_var + b_var - c_var
        );

        Ok(())
    }
}

#[derive(Clone)]
pub(crate) struct TranspilationTester<E: Engine> {
    pub(crate) a: Option<E::Fr>,
    pub(crate) b: Option<E::Fr>,
}

impl<E: Engine> Circuit<E> for TranspilationTester<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let a_var = cs.alloc(|| "a", || {
            if let Some(a_value) = self.a {
                Ok(a_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a is zero",
            |lc| lc + a_var,
            |lc| lc + CS::one(),
            |lc| lc
        );

        let b_var = cs.alloc(|| "b", || {
            if let Some(b_value) = self.b {
                Ok(b_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "b is one",
            |lc| lc + b_var,
            |lc| lc + CS::one(),
            |lc| lc + CS::one()
        );

        let c_var = cs.alloc_input(|| "c", || {
            if let Some(a_value) = self.a {
                Ok(a_value)
            } else {
                Err(SynthesisError::AssignmentMissing)
            }
        })?;

        cs.enforce(
            || "a is equal to c",
            |lc| lc + a_var,
            |lc| lc + CS::one(),
            |lc| lc + c_var
        );

        Ok(())
    }
}

#[cfg(feature = "plonk")]
#[test]
fn transpile_xor() {
    use crate::pairing::bn256::Bn256;
    use crate::plonk::adaptor::alternative::Transpiler;

    let c = XORDemo::<Bn256> {
        a: None,
        b: None,
        _marker: PhantomData
    };

    let mut transpiler = Transpiler::new();

    c.synthesize(&mut transpiler).unwrap();
}

#[cfg(feature = "plonk")]
#[test]
fn transpile_test_circuit() {
    use crate::pairing::bn256::{Bn256, Fr};
    use crate::plonk::adaptor::alternative::*;
    use crate::plonk::plonk::prover::*;

    let c = TranspilationTester::<Bn256> {
        a: Some(Fr::zero()),
        b: Some(Fr::one()),
    };

    let mut transpiler = Transpiler::new();

    c.clone().synthesize(&mut transpiler).unwrap();

    let hints = transpiler.into_hints();

    let adapted_curcuit = AdaptorCircuit::new(c.clone(), &hints);

    use crate::plonk::cs::Circuit as PlonkCircuit;

    let mut prover = ProvingAssembly::<Bn256>::new();
    adapted_curcuit.synthesize(&mut prover).unwrap();
    prover.finalize();

    println!("Checking if is satisfied");
    assert!(prover.is_satisfied());
}

const MIMC_ROUNDS: usize = 150;

fn mimc<E: Engine>(
    mut xl: E::Fr,
    mut xr: E::Fr,
    constants: &[E::Fr]
) -> E::Fr
{
    assert_eq!(constants.len(), MIMC_ROUNDS);

    for i in 0..MIMC_ROUNDS {
        let mut tmp1 = xl;
        tmp1.add_assign(&constants[i]);
        let mut tmp2 = tmp1;
        tmp2.square();
        tmp2.mul_assign(&tmp1);
        tmp2.add_assign(&xr);
        xr = xl;
        xl = tmp2;
    }

    xl
}

/// This is our demo circuit for proving knowledge of the
/// preimage of a MiMC hash invocation.
#[derive(Clone)]
pub(crate) struct MiMCDemo<'a, E: Engine> {
    pub(crate) xl: Option<E::Fr>,
    pub(crate) xr: Option<E::Fr>,
    pub(crate) constants: &'a [E::Fr]
}

/// Our demo circuit implements this `Circuit` trait which
/// is used during paramgen and proving in order to
/// synthesize the constraint system.
impl<'a, E: Engine> Circuit<E> for MiMCDemo<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        assert_eq!(self.constants.len(), MIMC_ROUNDS);

        // Allocate the first component of the preimage.
        let mut xl_value = self.xl;
        let mut xl = cs.alloc(|| "preimage xl", || {
            xl_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Allocate the second component of the preimage.
        let mut xr_value = self.xr;
        let mut xr = cs.alloc(|| "preimage xr", || {
            xr_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        for i in 0..MIMC_ROUNDS {
            // xL, xR := xR + (xL + Ci)^3, xL
            let cs = &mut cs.namespace(|| format!("round {}", i));

            // tmp = (xL + Ci)^2
            let tmp_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.square();
                e
            });
            let tmp = cs.alloc(|| "tmp", || {
                tmp_value.ok_or(SynthesisError::AssignmentMissing)
            })?;

            cs.enforce(
                || "tmp = (xL + Ci)^2",
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + tmp
            );

            // new_xL = xR + (xL + Ci)^3
            // new_xL = xR + tmp * (xL + Ci)
            // new_xL - xR = tmp * (xL + Ci)
            let new_xl_value = xl_value.map(|mut e| {
                e.add_assign(&self.constants[i]);
                e.mul_assign(&tmp_value.unwrap());
                e.add_assign(&xr_value.unwrap());
                e
            });

            let new_xl = if i == (MIMC_ROUNDS-1) {
                // This is the last round, xL is our image and so
                // we allocate a public input.
                cs.alloc_input(|| "image", || {
                    new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                })?
            } else {
                cs.alloc(|| "new_xl", || {
                    new_xl_value.ok_or(SynthesisError::AssignmentMissing)
                })?
            };

            cs.enforce(
                || "new_xL = xR + (xL + Ci)^3",
                |lc| lc + tmp,
                |lc| lc + xl + (self.constants[i], CS::one()),
                |lc| lc + new_xl - xr
            );

            // xR = xL
            xr = xl;
            xr_value = xl_value;

            // xL = new_xL
            xl = new_xl;
            xl_value = new_xl_value;
        }

        Ok(())
    }
}

