use std::cmp::Ordering;

use crate::float::FloatVar;
use ark_ff::PrimeField;

use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
};
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result},
};

#[derive(Clone)]
pub struct Statement {
    x: f64,
    y: f64,
    r: Ordering,
}

#[derive(Clone)]
pub struct Witness {
    a: f64,
    b: f64,
}

#[derive(Clone)]
pub struct InferenceCircuit {
    pub s: Statement,
    pub w: Witness,
}

impl InferenceCircuit {
    pub fn fake() -> Self {
        Self {
            s: Statement {
                x: 0f64,
                y: 0f64,
                r: Ordering::Equal,
            },
            w: Witness { a: 0f64, b: 0f64 },
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for InferenceCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<()> {
        let Statement { x, y, r } = self.s;
        let Witness { a, b } = self.w;

        let x_var = FloatVar::new_input(ns!(cs, "x"), || Ok(x))?;
        let y_var = FloatVar::new_input(ns!(cs, "y"), || Ok(y))?;
        let r_var = FpVar::new_input(ns!(cs, "r"), || {
            Ok(match r {
                Ordering::Less => F::one().neg(),
                Ordering::Equal => F::zero(),
                Ordering::Greater => F::one(),
            })
        })?;

        let a_var = FloatVar::new_witness(ns!(cs, "a"), || Ok(a))?;
        let b_var = FloatVar::new_witness(ns!(cs, "b"), || Ok(b))?;

        let v_var = FloatVar::add(
            ns!(cs, ""),
            &FloatVar::add(
                ns!(cs, ""),
                &FloatVar::mul(ns!(cs, ""), &a_var, &x_var)?,
                &b_var,
            )?,
            &y_var.neg(),
        )?;

        r_var
            .is_zero()?
            .select(
                &v_var.mantissa.is_eq(&FpVar::zero())?,
                &v_var.sign.is_eq(&r_var)?,
            )?
            .enforce_equal(&Boolean::TRUE)?;
        Ok(())
    }
}

fn infer(a: f64, b: f64, x: f64, y: f64) -> Ordering {
    (a * x + b - y).partial_cmp(&0f64).unwrap()
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::{One, Zero};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use rand::thread_rng;

    use super::*;

    #[test]
    fn test_inference() {
        let rng = &mut thread_rng();
        let params =
            generate_random_parameters::<Bls12_381, _, _>(InferenceCircuit::fake(), rng).unwrap();
        let pvk = prepare_verifying_key(&params.vk);

        let a = -0.5f64;
        let b = 2.625f64;
        let x = 2.75f64;
        let mut y = -2f64;

        let w = Witness { a, b };

        println!("Line: y = ax + b = {}x + {}", a, b);

        while y < 2f64 {
            let r = infer(a, b, x, y);

            let s = Statement { x, y, r };

            let proof =
                create_random_proof(InferenceCircuit { s, w: w.clone() }, &params, rng).unwrap();

            let mut input = [FloatVar::verifier_input(x), FloatVar::verifier_input(y)].concat();

            input.push(match r {
                Ordering::Less => -Fr::one(),
                Ordering::Equal => Fr::zero(),
                Ordering::Greater => Fr::one(),
            });

            assert!(verify_proof(&pvk, &proof, &input).unwrap());
            println!(
                "Point ({}, {}) is {} the line, zk verification is successful",
                x,
                y,
                match r {
                    Ordering::Greater => "below",
                    Ordering::Less => "above",
                    Ordering::Equal => "on",
                },
            );
            y += 0.25;
        }
    }
}
