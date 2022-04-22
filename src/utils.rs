use ark_ff::PrimeField;
use num::{Signed, BigUint, BigInt};
use std::fmt::Debug;

pub fn signed_to_field<F: PrimeField, S: Signed + TryInto<u64>>(n: S) -> F
where
    S::Error: Debug,
{
    if n.is_negative() {
        -F::from((-n).try_into().unwrap())
    } else {
        F::from(n.try_into().unwrap())
    }
}

pub trait ToBigUint {
    fn to_biguint(&self) -> BigUint;
}

pub trait ToBigint {
    fn to_bigint(&self) -> BigInt;
}
