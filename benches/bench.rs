use std::cmp::Ordering;

use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::{One, PrimeField, Zero};
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_r1cs_std::alloc::AllocVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::{thread_rng, Rng};
use zk_linear_regression::{
    float::{self, FloatVar},
    inference::{self, infer, InferenceCircuit},
    training::{self, train, TrainingCircuit},
};

pub struct Add {
    x: f64,
    y: f64,
    z: f64,
}

pub struct Mul {
    x: f64,
    y: f64,
    z: f64,
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Add {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = FloatVar::new_witness(cs.clone(), || Ok(self.x))?;
        let y = FloatVar::new_witness(cs.clone(), || Ok(self.y))?;
        let z = FloatVar::new_input(cs.clone(), || Ok(self.z))?;

        FloatVar::equal(&(x + y), &z)?;
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Mul {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = FloatVar::new_witness(cs.clone(), || Ok(self.x))?;
        let y = FloatVar::new_witness(cs.clone(), || Ok(self.y))?;
        let z = FloatVar::new_input(cs.clone(), || Ok(self.z))?;

        FloatVar::equal(&(x * y), &z)?;
        Ok(())
    }
}

pub fn add(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let params = generate_random_parameters::<Bls12_381, _, _>(
        Add {
            x: 0f64,
            y: 0f64,
            z: 0f64,
        },
        rng,
    )
    .unwrap();

    c.bench_function("add#setup", |b| {
        b.iter(|| {
            generate_random_parameters::<Bls12_381, _, _>(
                Add {
                    x: black_box(0f64),
                    y: black_box(0f64),
                    z: black_box(0f64),
                },
                rng,
            )
        })
    });

    let pvk = prepare_verifying_key(&params.vk);

    let x = -rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let y = rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let z = x + y;

    let proof = create_random_proof(Add { x, y, z }, &params, rng).unwrap();

    c.bench_function("add#prove", |b| {
        b.iter(|| {
            create_random_proof(
                Add {
                    x: black_box(x),
                    y: black_box(y),
                    z: black_box(z),
                },
                &params,
                rng,
            )
        })
    });

    c.bench_function("add#verify", |b| {
        let inputs = FloatVar::input(z);
        b.iter(|| verify_proof(&pvk, &proof, black_box(&inputs)))
    });
}

pub fn mul(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let params = generate_random_parameters::<Bls12_381, _, _>(
        Mul {
            x: 0f64,
            y: 0f64,
            z: 0f64,
        },
        rng,
    )
    .unwrap();

    c.bench_function("mul#setup", |b| {
        b.iter(|| {
            generate_random_parameters::<Bls12_381, _, _>(
                Mul {
                    x: black_box(0f64),
                    y: black_box(0f64),
                    z: black_box(0f64),
                },
                rng,
            )
        })
    });

    let pvk = prepare_verifying_key(&params.vk);

    let x = -rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let y = rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let z = x * y;

    let proof = create_random_proof(Mul { x, y, z }, &params, rng).unwrap();

    c.bench_function("mul#prove", |b| {
        b.iter(|| {
            create_random_proof(
                Mul {
                    x: black_box(x),
                    y: black_box(y),
                    z: black_box(z),
                },
                &params,
                rng,
            )
        })
    });

    c.bench_function("mul#verify", |b| {
        let inputs = FloatVar::input(z);
        b.iter(|| verify_proof(&pvk, &proof, black_box(&inputs)))
    });
}

pub fn inference(c: &mut Criterion) {
    let rng = &mut thread_rng();
    let params =
        generate_random_parameters::<Bls12_381, _, _>(InferenceCircuit::fake(), rng).unwrap();

    c.bench_function("inference#setup", |b| {
        b.iter(|| {
            generate_random_parameters::<Bls12_381, _, _>(black_box(InferenceCircuit::fake()), rng)
        })
    });

    let pvk = prepare_verifying_key(&params.vk);

    let a = rng.gen::<f64>();
    let b = rng.gen::<f64>();
    let x = rng.gen::<f64>();
    let y = rng.gen::<f64>();

    let w = inference::Witness { a, b };

    let r = infer(a, b, x, y);

    let s = inference::Statement { x, y, r };

    let proof = create_random_proof(
        InferenceCircuit {
            s: s.clone(),
            w: w.clone(),
        },
        &params,
        rng,
    )
    .unwrap();

    c.bench_function("inference#prove", |b| {
        b.iter(|| {
            create_random_proof(
                InferenceCircuit {
                    s: black_box(s.clone()),
                    w: black_box(w.clone()),
                },
                &params,
                rng,
            )
        })
    });

    let mut input = [FloatVar::input(x), FloatVar::input(y)].concat();

    input.push(match r {
        Ordering::Less => -Fr::one(),
        Ordering::Equal => Fr::zero(),
        Ordering::Greater => Fr::one(),
    });

    c.bench_function("inference#verify", |b| {
        b.iter(|| verify_proof(&pvk, &proof, black_box(&input)))
    });
}

pub fn training(c: &mut Criterion) {
    let rng = &mut thread_rng();

    let l = 10;

    let params =
        generate_random_parameters::<Bls12_381, _, _>(TrainingCircuit::fake(l), rng).unwrap();

    c.bench_function("training#setup", |b| {
        b.iter(|| {
            generate_random_parameters::<Bls12_381, _, _>(black_box(TrainingCircuit::fake(l)), rng)
        })
    });

    let pvk = prepare_verifying_key(&params.vk);

    let x = (0..l).map(|_| rng.gen::<f64>()).collect::<Vec<_>>();
    let y = (0..l).map(|_| rng.gen::<f64>()).collect::<Vec<_>>();

    let (a_n, a_d, b_n, b_d) = train(&x, &y, l);

    let proof = create_random_proof(
        training::TrainingCircuit {
            pp: training::Parameters { l },
            s: training::Statement { a_n, a_d, b_n, b_d },
            w: training::Witness { x: x.clone(), y: y.clone() },
        },
        &params,
        rng,
    )
    .unwrap();

    c.bench_function("training#prove", |b| {
        b.iter(|| {
            create_random_proof(
                training::TrainingCircuit {
                    pp: training::Parameters { l },
                    s: training::Statement { a_n, a_d, b_n, b_d },
                    w: training::Witness { x: x.clone(), y: y.clone() },
                },
                &params,
                rng,
            )
        })
    });

    c.bench_function("training#verify", |b| {
        b.iter(|| {
            verify_proof(
                &pvk,
                &proof,
                &[
                    FloatVar::input(a_n),
                    FloatVar::input(a_d),
                    FloatVar::input(b_n),
                    FloatVar::input(b_d)
                ]
                .concat()
            )
        })
    });
}

criterion_group!(benches, add, mul, inference, training);
criterion_main!(benches);
