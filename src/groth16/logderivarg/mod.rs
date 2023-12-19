use std::collections::HashMap;

use ark_ff::PrimeField;

use crate::{
    lc,
    r1cs::{ConstraintSystemRef, SynthesisError, Variable},
    r1cs_std::{
        fields::fp::{AllocatedFp, FpVar},
        prelude::{AllocVar, EqGadget, FieldVar},
    },
};

pub const LOOKUP_TABLE_BITS: usize = 8;

fn recover_queries<F: PrimeField>(cs: ConstraintSystemRef<F>) -> Vec<FpVar<F>> {
    let num_queries = cs.num_committed_variables();
    let assignments = &cs.borrow().unwrap().committed_assignment;
    (0..num_queries)
        .map(|i| {
            FpVar::Var(AllocatedFp::new(
                assignments.get(i).copied(),
                Variable::Committed(i),
                cs.clone(),
            ))
        })
        .collect::<Vec<_>>()
}

fn build_histo<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    table: &[F],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut histo = table.iter().map(|&v| (v, 0u64)).collect::<HashMap<_, _>>();
    if let Some(cs) = cs.borrow() {
        for &i in &cs.committed_assignment {
            *histo.entry(i).or_default() += 1;
        }
    }
    table
        .iter()
        .map(|v| F::from(histo[v]))
        .map(|v| FpVar::new_committed(cs.clone(), || Ok(v)))
        .collect::<Result<Vec<_>, _>>()
}

fn compute_lhs<F: PrimeField>(
    c: &FpVar<F>,
    table: &[F],
    histo: &[FpVar<F>],
) -> Result<FpVar<F>, SynthesisError> {
    let mut l = FpVar::<F>::zero();
    for (&i, e) in table.iter().zip(histo) {
        l += e.mul_by_inverse_unchecked(&(c - i))?;
    }
    Ok(l)
}

fn compute_rhs<F: PrimeField>(
    c: &FpVar<F>,
    queries: &[FpVar<F>],
) -> Result<FpVar<F>, SynthesisError> {
    let mut cs = ConstraintSystemRef::None;
    let mut value = None;
    let mut new_lc = lc!();

    for i in queries {
        match (c - i).inverse()? {
            FpVar::Constant(_) => unreachable!(),
            FpVar::Var(variable) => {
                cs = cs.or(variable.cs.clone());
                if let Some(v) = variable.value {
                    value = Some(value.unwrap_or_default() + v);
                }
                new_lc = new_lc + variable.variable;
            }
        }
    }

    let variable = cs.new_lc(new_lc).unwrap();

    Ok(AllocatedFp::new(value, variable, cs).into())
}

pub fn generate_commitment<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    mut challenge: impl FnMut(ConstraintSystemRef<F>) -> Option<F>,
) -> Result<(), SynthesisError> {
    if cs.num_committed_variables() == 0 {
        return Ok(());
    }
    let table = (0..(1u64 << LOOKUP_TABLE_BITS))
        .map(F::from)
        .collect::<Vec<_>>();
    let queries = recover_queries(cs.clone());
    let histo = build_histo(cs.clone(), &table)?;

    let c = challenge(cs.clone());

    let c = FpVar::Var(AllocatedFp::new(
        c,
        cs.new_commitment(|| Ok(c.unwrap_or_default()))?,
        cs.clone(),
    ));

    compute_lhs(&c, &table, &histo)?.enforce_equal(&compute_rhs(&c, &queries)?)?;

    Ok(())
}
