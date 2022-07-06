use ark_bls12_381::{Bls12_381, Fr};
use ark_ff::PrimeField;
use ark_groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use criterion::{
    black_box, criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion,
};
use r1cs_float::f64::F64Var;
use rand::{thread_rng, Rng};

#[derive(Default)]
pub struct Add(f64, f64, f64);

#[derive(Default)]
pub struct Sub(f64, f64, f64);

#[derive(Default)]
pub struct Mul(f64, f64, f64);

#[derive(Default)]
pub struct Div(f64, f64, f64);

#[derive(Default)]
pub struct Sqrt(f64, f64);

impl<F: PrimeField> ConstraintSynthesizer<F> for Add {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = F64Var::new_witness(cs.clone(), || Ok(self.0))?;
        let y = F64Var::new_witness(cs.clone(), || Ok(self.1))?;
        let z = F64Var::new_input(cs.clone(), || Ok(self.2))?;

        F64Var::enforce_equal(&(x + y), &z)?;
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Sub {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = F64Var::new_witness(cs.clone(), || Ok(self.0))?;
        let y = F64Var::new_witness(cs.clone(), || Ok(self.1))?;
        let z = F64Var::new_input(cs.clone(), || Ok(self.2))?;

        F64Var::enforce_equal(&(x - y), &z)?;
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Mul {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = F64Var::new_witness(cs.clone(), || Ok(self.0))?;
        let y = F64Var::new_witness(cs.clone(), || Ok(self.1))?;
        let z = F64Var::new_input(cs.clone(), || Ok(self.2))?;

        F64Var::enforce_equal(&(x * y), &z)?;
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Div {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = F64Var::new_witness(cs.clone(), || Ok(self.0))?;
        let y = F64Var::new_witness(cs.clone(), || Ok(self.1))?;
        let z = F64Var::new_input(cs.clone(), || Ok(self.2))?;

        F64Var::enforce_equal(&(x / y), &z)?;
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for Sqrt {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ark_relations::r1cs::Result<()> {
        let x = F64Var::new_witness(cs.clone(), || Ok(self.0))?;
        let y = F64Var::new_input(cs.clone(), || Ok(self.1))?;

        F64Var::enforce_equal(&F64Var::sqrt(&x)?, &y)?;
        Ok(())
    }
}

pub fn unary_op<C: ConstraintSynthesizer<Fr> + Default>(
    group: &mut BenchmarkGroup<WallTime>,
    op: fn(f64) -> f64,
    circuit: fn(f64, f64) -> C,
) {
    let rng = &mut thread_rng();

    let params = generate_random_parameters::<Bls12_381, _, _>(C::default(), rng).unwrap();

    group.bench_function("setup", |b| {
        b.iter(|| generate_random_parameters::<Bls12_381, _, _>(C::default(), rng))
    });

    let pvk = prepare_verifying_key(&params.vk);

    let x = rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let y = op(x);

    let proof = create_random_proof(circuit(x, y), &params, rng).unwrap();

    group.bench_function("prove", |b| {
        b.iter(|| create_random_proof(circuit(x, y), &params, rng))
    });

    let inputs = F64Var::input(y);
    assert!(verify_proof(&pvk, &proof, &inputs).unwrap());

    group.bench_function("verify", |b| {
        b.iter(|| verify_proof(&pvk, &proof, black_box(&inputs)))
    });
}

pub fn binary_op<C: ConstraintSynthesizer<Fr> + Default>(
    group: &mut BenchmarkGroup<WallTime>,
    op: fn(f64, f64) -> f64,
    circuit: fn(f64, f64, f64) -> C,
) {
    let rng = &mut thread_rng();

    let params = generate_random_parameters::<Bls12_381, _, _>(C::default(), rng).unwrap();

    group.bench_function("setup", |b| {
        b.iter(|| generate_random_parameters::<Bls12_381, _, _>(C::default(), rng))
    });

    let pvk = prepare_verifying_key(&params.vk);

    let x = -rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let y = rng.gen::<f64>() * rng.gen::<u32>() as f64;
    let z = op(x, y);

    let proof = create_random_proof(circuit(x, y, z), &params, rng).unwrap();

    group.bench_function("prove", |b| {
        b.iter(|| create_random_proof(circuit(x, y, z), &params, rng))
    });

    let inputs = F64Var::input(z);
    assert!(verify_proof(&pvk, &proof, &inputs).unwrap());

    group.bench_function("verify", |b| {
        b.iter(|| verify_proof(&pvk, &proof, black_box(&inputs)))
    });
}

pub fn add(c: &mut Criterion) {
    let mut group = c.benchmark_group("add");
    binary_op(&mut group, std::ops::Add::add, |a, b, c| Add(a, b, c));
    group.finish();
}

pub fn sub(c: &mut Criterion) {
    let mut group = c.benchmark_group("sub");
    binary_op(&mut group, std::ops::Sub::sub, |a, b, c| Sub(a, b, c));
    group.finish();
}

pub fn mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("mul");
    binary_op(&mut group, std::ops::Mul::mul, |a, b, c| Mul(a, b, c));
    group.finish();
}

pub fn div(c: &mut Criterion) {
    let mut group = c.benchmark_group("div");
    binary_op(&mut group, std::ops::Div::div, |a, b, c| Div(a, b, c));
    group.finish();
}

pub fn sqrt(c: &mut Criterion) {
    let mut group = c.benchmark_group("sqrt");
    unary_op(&mut group, |x| x.sqrt(), |a, b| Sqrt(a, b));
    group.finish();
}

criterion_group!(benches, add, sub, mul, div, sqrt);
criterion_main!(benches);
