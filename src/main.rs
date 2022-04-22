use std::{cmp::Ordering};

use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::{One, PrimeField, Zero};
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
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
use float::FloatVar;
use rand::thread_rng;

pub mod float;
pub mod utils;

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
pub struct Circuit {
    pub s: Statement,
    pub w: Witness,
}

impl Circuit {
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

impl<F: PrimeField> ConstraintSynthesizer<F> for Circuit {
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
            FloatVar::add(
                ns!(cs, ""),
                FloatVar::mul(ns!(cs, ""), a_var, x_var)?,
                b_var,
            )?,
            y_var.neg(),
        )?;

        r_var
            .is_zero()?
            .select(&v_var.mantissa.is_eq(&FpVar::zero())?, &v_var.sign.is_eq(&r_var)?)?
            .enforce_equal(&Boolean::TRUE)?;
        Ok(())
    }
}

fn inference(a: f64, b: f64, x: f64, y: f64) -> Ordering {
    (a * x + b - y).partial_cmp(&0f64).unwrap()
}

fn main() {
    let rng = &mut thread_rng();
    let params = generate_random_parameters::<Bls12_381, _, _>(Circuit::fake(), rng).unwrap();

    let a = -0.5f64;
    let b = 2.625f64;
    let x = 2.75f64;
    let mut y = -2f64;

    let w = Witness { a, b };

    println!("Line: y = ax + b = {}x + {}", a, b);

    while y < 2f64 {
        let r = inference(a, b, x, y);

        let s = Statement { x, y, r };

        let pvk = prepare_verifying_key(&params.vk);
        let proof = create_random_proof(Circuit { s, w: w.clone() }, &params, rng).unwrap();

        let mut input = [FloatVar::verifier_input(x), FloatVar::verifier_input(y)].concat();

        input.push(match r {
            Ordering::Less => -Fr::one(),
            Ordering::Equal => Fr::zero(),
            Ordering::Greater => Fr::one(),
        });

        println!(
            "Point ({}, {}) is {} the line, zk verification returns {}",
            x,
            y,
            match r {
                Ordering::Greater => "below",
                Ordering::Less => "above",
                Ordering::Equal => "on",
            },
            verify_proof(&pvk, &proof, &input).unwrap().to_string()
        );
        y += 0.25;
    }
}
