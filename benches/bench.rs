use ark_bls12_381::Bls12_381;
use ark_ff::PrimeField;
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::{thread_rng, Rng};
use r1cs_float::{
    f64::F64Var,
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
        let x = F64Var::new_witness(cs.clone(), || Ok(self.x))?;
        let y = F64Var::new_witness(cs.clone(), || Ok(self.y))?;
        let z = F64Var::new_input(cs.clone(), || Ok(self.z))?;

        F64Var::enforce_equal(&(x + y), &z)?;
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Mul {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = F64Var::new_witness(cs.clone(), || Ok(self.x))?;
        let y = F64Var::new_witness(cs.clone(), || Ok(self.y))?;
        let z = F64Var::new_input(cs.clone(), || Ok(self.z))?;

        F64Var::enforce_equal(&(x * y), &z)?;
        Ok(())
    }
}

pub fn add(c: &mut Criterion) {
    let mut group = c.benchmark_group("add");

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

    group.bench_function("setup", |b| {
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

    group.bench_function("prove", |b| {
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

    group.bench_function("verify", |b| {
        let inputs = F64Var::input(z);
        b.iter(|| verify_proof(&pvk, &proof, black_box(&inputs)))
    });
    group.finish();
}

pub fn mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("mul");

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

    group.bench_function("setup", |b| {
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

    group.bench_function("prove", |b| {
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

    group.bench_function("verify", |b| {
        let inputs = F64Var::input(z);
        b.iter(|| verify_proof(&pvk, &proof, black_box(&inputs)))
    });
    group.finish();
}

criterion_group!(benches, add, mul);
criterion_main!(benches);
