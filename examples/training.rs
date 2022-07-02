use ark_ff::PrimeField;
use ark_r1cs_std::eq::EqGadget;
use r1cs_float::f64::F64Var;

use ark_r1cs_std::alloc::AllocVar;
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result},
};
use num::ToPrimitive;

use ark_bls12_381::Bls12_381;
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use rand::{thread_rng, Rng};

#[derive(Clone)]
pub struct Statement {
    pub a: f64,
    pub b: f64,
}

#[derive(Clone)]
pub struct Witness<const L: usize> {
    pub x: [f64; L],
    pub y: [f64; L],
}

#[derive(Clone)]
pub struct TrainingCircuit<const L: usize> {
    pub s: Statement,
    pub w: Witness<L>,
}

impl<const L: usize> Default for TrainingCircuit<L> {
    fn default() -> Self {
        Self {
            s: Statement { a: 0f64, b: 0f64 },
            w: Witness {
                x: [0f64; L],
                y: [0f64; L],
            },
        }
    }
}

impl<F: PrimeField, const L: usize> ConstraintSynthesizer<F> for TrainingCircuit<L> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<()> {
        let Statement { a, b } = self.s;
        let Witness { x, y } = self.w;

        let l_var = F64Var::new_constant(ns!(cs, "l"), L.to_f64().unwrap())?;

        let x_var = x
            .iter()
            .map(|x| F64Var::new_witness(ns!(cs, "x"), || Ok(x)).unwrap())
            .collect::<Vec<_>>();
        let y_var = y
            .iter()
            .map(|y| F64Var::new_witness(ns!(cs, "y"), || Ok(y)).unwrap())
            .collect::<Vec<_>>();

        let a_var = F64Var::new_input(ns!(cs, "a"), || Ok(a))?;
        let b_var = F64Var::new_input(ns!(cs, "b"), || Ok(b))?;

        let mut x_s = F64Var::new_constant(ns!(cs, "x_s"), 0.)?;
        let mut y_s = F64Var::new_constant(ns!(cs, "y_s"), 0.)?;
        let mut xx_s = F64Var::new_constant(ns!(cs, "xx_s"), 0.)?;
        let mut xy_s = F64Var::new_constant(ns!(cs, "xy_s"), 0.)?;

        for i in 0..L {
            x_s += &x_var[i];
            y_s += &y_var[i];
            xy_s += &x_var[i] * &y_var[i];
            xx_s += &x_var[i] * &x_var[i];
        }

        F64Var::enforce_equal(
            &((&xy_s * &l_var - &x_s * &y_s) / (&xx_s * &l_var - &x_s * &x_s)),
            &a_var,
        )?;

        F64Var::enforce_equal(&((&y_s - &x_s * &a_var) / l_var), &b_var)?;

        Ok(())
    }
}

pub fn train<const L: usize>(x: &[f64; L], y: &[f64; L]) -> (f64, f64) {
    let l = L.to_f64().unwrap();

    let x_s = x.iter().sum::<f64>();
    let y_s = y.iter().sum::<f64>();
    let xx_s = x.iter().map(|x| x * x).sum::<f64>();
    let xy_s = x.iter().zip(y).map(|(x, y)| x * y).sum::<f64>();

    let a = (xy_s * l - x_s * y_s) / (xx_s * l - x_s * x_s);
    let b = (y_s - x_s * a) / l;

    (a, b)
}

fn main() {
    let rng = &mut thread_rng();

    const L: usize = 1000;

    let mut x = [0f64; L];
    rng.fill::<[_]>(&mut x);
    let mut y = [0f64; L];
    rng.fill::<[_]>(&mut y);

    let (a, b) = train(&x, &y);

    let params = generate_random_parameters(TrainingCircuit::<L>::default(), rng).unwrap();
    let pvk = prepare_verifying_key::<Bls12_381>(&params.vk);

    let proof = create_random_proof(
        TrainingCircuit {
            s: Statement { a, b },
            w: Witness { x, y },
        },
        &params,
        rng,
    )
    .unwrap();

    assert!(verify_proof(
        &pvk,
        &proof,
        &[F64Var::input(a), F64Var::input(b)].concat()
    )
    .unwrap());
}
