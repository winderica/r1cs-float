
use crate::float::FloatVar;
use ark_ff::PrimeField;

use ark_r1cs_std::alloc::AllocVar;
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result},
};
use num::ToPrimitive;

#[derive(Clone)]
pub struct Parameters {
    l: usize,
}

#[derive(Clone)]
pub struct Statement {
    a_n: f64,
    a_d: f64,
    b_n: f64,
    b_d: f64,
}

#[derive(Clone)]
pub struct Witness {
    x: Vec<f64>,
    y: Vec<f64>,
}

#[derive(Clone)]
pub struct TrainingCircuit {
    pub pp: Parameters,
    pub s: Statement,
    pub w: Witness,
}

impl TrainingCircuit {
    pub fn fake(l: usize) -> Self {
        Self {
            pp: Parameters { l },
            s: Statement {
                a_n: 0f64,
                a_d: 0f64,
                b_n: 0f64,
                b_d: 0f64,
            },
            w: Witness {
                x: vec![0f64; l],
                y: vec![0f64; l],
            },
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TrainingCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<()> {
        let Parameters { l } = self.pp;
        let Statement { a_n, a_d, b_n, b_d } = self.s;
        let Witness { x, y } = self.w;

        assert_eq!(x.len(), l);
        assert_eq!(y.len(), l);

        let l_var = FloatVar::new_constant(ns!(cs, "l"), l.to_f64().unwrap())?;

        let x_var = x
            .iter()
            .map(|x| FloatVar::new_witness(ns!(cs, "x"), || Ok(x)).unwrap())
            .collect::<Vec<_>>();
        let y_var = y
            .iter()
            .map(|y| FloatVar::new_witness(ns!(cs, "y"), || Ok(y)).unwrap())
            .collect::<Vec<_>>();

        let a_n_var = FloatVar::new_input(ns!(cs, "a"), || Ok(a_n))?;
        let a_d_var = FloatVar::new_input(ns!(cs, "a"), || Ok(a_d))?;
        let b_n_var = FloatVar::new_input(ns!(cs, "b"), || Ok(b_n))?;
        let b_d_var = FloatVar::new_input(ns!(cs, "b"), || Ok(b_d))?;

        let mut x_s = FloatVar::new_constant(ns!(cs, "x_s"), 0.)?;
        let mut y_s = FloatVar::new_constant(ns!(cs, "y_s"), 0.)?;
        let mut xx_s = FloatVar::new_constant(ns!(cs, "xx_s"), 0.)?;
        let mut xy_s = FloatVar::new_constant(ns!(cs, "xy_s"), 0.)?;

        for i in 0..l {
            x_s = FloatVar::add(ns!(cs, ""), &x_s, &x_var[i])?;
            y_s = FloatVar::add(ns!(cs, ""), &y_s, &y_var[i])?;
            xy_s = FloatVar::add(
                ns!(cs, ""),
                &xy_s,
                &FloatVar::mul(ns!(cs, ""), &x_var[i], &y_var[i])?,
            )?;
            xx_s = FloatVar::add(
                ns!(cs, ""),
                &xx_s,
                &FloatVar::mul(ns!(cs, ""), &x_var[i], &x_var[i])?,
            )?;
        }

        FloatVar::equal(
            &FloatVar::add(
                ns!(cs, "a_n"),
                &FloatVar::mul(ns!(cs, ""), &xy_s, &l_var)?,
                &FloatVar::mul(ns!(cs, ""), &x_s, &y_s)?.neg(),
            )?,
            &a_n_var,
        )?;

        FloatVar::equal(
            &FloatVar::add(
                ns!(cs, "a_d"),
                &FloatVar::mul(ns!(cs, ""), &xx_s, &l_var)?,
                &FloatVar::mul(ns!(cs, ""), &x_s, &x_s)?.neg(),
            )?,
            &a_d_var,
        )?;

        FloatVar::equal(
            &FloatVar::add(
                ns!(cs, "b_n"),
                &FloatVar::mul(ns!(cs, ""), &y_s, &a_d_var)?,
                &FloatVar::mul(ns!(cs, ""), &x_s, &a_n_var)?.neg(),
            )?,
            &b_n_var,
        )?;

        FloatVar::equal(&FloatVar::mul(ns!(cs, "b_d"), &l_var, &a_d_var)?, &b_d_var)?;

        Ok(())
    }
}

fn train(x: &Vec<f64>, y: &Vec<f64>, l: usize) -> (f64, f64, f64, f64) {
    assert_eq!(x.len(), l);
    assert_eq!(y.len(), l);

    let l = l.to_f64().unwrap();

    let x_s = x.iter().sum::<f64>();
    let y_s = y.iter().sum::<f64>();
    let xx_s = x.iter().map(|x| x * x).sum::<f64>();
    let xy_s = x.iter().zip(y).map(|(x, y)| x * y).sum::<f64>();

    let a_n = xy_s * l - x_s * y_s;
    let a_d = xx_s * l - x_s * x_s;
    let b_n = y_s * a_d - x_s * a_n;
    let b_d = l * a_d;

    (a_n, a_d, b_n, b_d)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn test_training() {
        let rng = &mut thread_rng();

        let l = 10;

        let params =
            generate_random_parameters::<Bls12_381, _, _>(TrainingCircuit::fake(l), rng).unwrap();
        let pvk = prepare_verifying_key(&params.vk);

        let x = (0..l).map(|_| rng.gen::<f64>()).collect::<Vec<_>>();
        let y = (0..l).map(|_| rng.gen::<f64>()).collect::<Vec<_>>();

        let (a_n, a_d, b_n, b_d) = train(&x, &y, l);

        let proof = create_random_proof(
            TrainingCircuit {
                pp: Parameters { l },
                s: Statement { a_n, a_d, b_n, b_d },
                w: Witness { x, y },
            },
            &params,
            rng,
        )
        .unwrap();

        assert!(verify_proof(
            &pvk,
            &proof,
            &[
                FloatVar::verifier_input(a_n),
                FloatVar::verifier_input(a_d),
                FloatVar::verifier_input(b_n),
                FloatVar::verifier_input(b_d)
            ]
            .concat()
        )
        .unwrap());
    }
}
