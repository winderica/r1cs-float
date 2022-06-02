use std::{
    borrow::Borrow,
    cmp,
    fmt::{Debug, Display},
    ops::Neg,
};

use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    R1CSVar,
};
use ark_relations::{
    ns,
    r1cs::{ConstraintSystemRef, Namespace, SynthesisError},
};
use num::{BigUint, ToPrimitive};

#[derive(Clone, Debug)]
pub struct FloatVar<F: PrimeField> {
    cs: ConstraintSystemRef<F>,
    pub sign: FpVar<F>,
    pub exponent: FpVar<F>,
    pub mantissa: FpVar<F>,
}

impl<F: PrimeField> Display for FloatVar<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let e = self.exponent.value().unwrap_or(F::zero());
        let e_ge_0 = e.into_repr() < F::modulus_minus_one_div_two();
        let e: BigUint = if e_ge_0 { e } else { e.neg() }
            .into_repr()
            .try_into()
            .unwrap();
        let m: BigUint = self
            .mantissa
            .value()
            .unwrap_or(F::zero())
            .into_repr()
            .try_into()
            .unwrap();

        let s = if self.sign.value().unwrap_or(F::one()).is_one() {
            1
        } else {
            -1
        };

        write!(
            f,
            "Sign: {}\nExponent: {}{}\nMantissa: {}\n",
            &s,
            if e_ge_0 { "" } else { "-" },
            &e,
            &m
        )
    }
}

impl<F: PrimeField> FloatVar<F> {
    pub fn input(i: f64) -> [F; 3] {
        let i = i.to_bits();
        let sign = i >> 63;
        let mantissa = i & ((1 << 52) - 1);
        let exponent = (i - mantissa - (sign << 63)) >> 52;
        let sign = if sign == 0 { F::one() } else { -F::one() };
        let mantissa = F::from(mantissa)
            + if exponent == 0 {
                F::zero()
            } else {
                F::from(1u64 << 52)
            };
        let exponent = F::from(cmp::max(exponent, 1)) - F::from(1023u64);
        [sign, exponent, mantissa]
    }
}

impl<F: PrimeField> AllocVar<f64, F> for FloatVar<F> {
    fn new_variable<T: Borrow<f64>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let [sign, exponent, mantissa] = Self::input(*f()?.borrow());
        let sign = FpVar::new_variable(ns!(cs, "sign"), || Ok(sign), mode)?;
        let exponent = FpVar::new_variable(ns!(cs, "exponent"), || Ok(exponent), mode)?;
        let mantissa = FpVar::new_variable(ns!(cs, "mantissa"), || Ok(mantissa), mode)?;
        Ok(Self {
            cs,
            sign,
            exponent,
            mantissa,
        })
    }
}

macro_rules! impl_ops {
    (
        $type: ty,
        $trait: ident,
        $fn: ident,
        $assign_trait: ident,
        $assign_fn: ident,
        $impl: expr,
        $($params:tt)*
    ) => {
        impl<'a, $($params)+> core::ops::$trait<&'a $type> for &'a $type
        {
            type Output = $type;

            fn $fn(self, other: &'a $type) -> Self::Output {
                ($impl)(self, other)
            }
        }

        impl<'a, $($params)+> core::ops::$trait<$type> for &'a $type
        {
            type Output = $type;

            fn $fn(self, other: $type) -> Self::Output {
                core::ops::$trait::$fn(self, &other)
            }
        }

        impl<'a, $($params)+> core::ops::$trait<&'a $type> for $type
        {
            type Output = $type;

            fn $fn(self, other: &'a $type) -> Self::Output {
                core::ops::$trait::$fn(&self, other)
            }
        }

        impl<$($params)+> core::ops::$trait<$type> for $type
        {
            type Output = $type;

            fn $fn(self, other: $type) -> Self::Output {
                core::ops::$trait::$fn(&self, &other)
            }
        }

        impl<$($params)+> core::ops::$assign_trait<$type> for $type
        {
            fn $assign_fn(&mut self, other: $type) {
                *self = core::ops::$trait::$fn(&*self, &other);
            }
        }

        impl<'a, $($params)+> core::ops::$assign_trait<&'a $type> for $type
        {
            fn $assign_fn(&mut self, other: &'a $type) {
                *self = core::ops::$trait::$fn(&*self, other);
            }
        }
    };
}

impl<F: PrimeField> Neg for FloatVar<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::neg(&self)
    }
}

impl<F: PrimeField> Neg for &FloatVar<F> {
    type Output = FloatVar<F>;

    fn neg(self) -> Self::Output {
        FloatVar::<F>::neg(self)
    }
}

impl_ops!(
    FloatVar<F>,
    Add,
    add,
    AddAssign,
    add_assign,
    |a, b| { FloatVar::<F>::add(a, b).unwrap() },
    F: PrimeField,
);

impl_ops!(
    FloatVar<F>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |a, b: &'a FloatVar<F>| { FloatVar::<F>::add(a, &-b).unwrap() },
    F: PrimeField,
);

impl_ops!(
    FloatVar<F>,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |a, b| { FloatVar::<F>::mul(a, b).unwrap() },
    F: PrimeField,
);

impl<F: PrimeField> FloatVar<F> {
    pub fn equal(x: &Self, y: &Self) -> Result<(), SynthesisError> {
        x.sign.enforce_equal(&y.sign)?;
        x.exponent.enforce_equal(&y.exponent)?;
        x.mantissa.enforce_equal(&y.mantissa)?;
        Ok(())
    }

    fn new_bits_variable(
        cs: ConstraintSystemRef<F>,
        bits: &[bool],
        mode: AllocationMode,
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        bits.iter()
            .map(|i| Boolean::new_variable(cs.clone(), || Ok(i), mode))
            .collect::<Result<Vec<_>, _>>()
    }

    fn new_bits_witness(
        cs: ConstraintSystemRef<F>,
        bits: &[bool],
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Self::new_bits_variable(cs, bits, AllocationMode::Witness)
    }

    fn to_abs_n_bits(
        x: &FpVar<F>,
        n: usize,
    ) -> Result<(Vec<Boolean<F>>, Boolean<F>), SynthesisError> {
        let cs = x.cs();

        let (abs_bits, is_non_negative) = {
            let x = x.value().unwrap_or(F::zero());
            let is_non_negative = x.into_repr() < F::modulus_minus_one_div_two();

            let abs = if is_non_negative { x } else { x.neg() };

            (
                Self::new_bits_witness(cs.clone(), &abs.into_repr().to_bits_le()[..n])?,
                Boolean::new_witness(cs.clone(), || Ok(is_non_negative))?,
            )
        };

        Boolean::le_bits_to_fp_var(&abs_bits)?
            .enforce_equal(&is_non_negative.select(x, &x.negate()?)?)?;

        Ok((abs_bits, is_non_negative))
    }

    fn neg(&self) -> Self {
        Self {
            cs: self.cs.clone(),
            sign: FpVar::zero() - &self.sign,
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
        }
    }

    fn normalize(
        mantissa: &FpVar<F>,
        mantissa_bit_length: usize,
        exponent: &FpVar<F>,
    ) -> Result<(Vec<Boolean<F>>, FpVar<F>), SynthesisError> {
        let cs = mantissa.cs();

        let one = FpVar::one();
        let two = one.double()?;
        let min_exponent = FpVar::Constant(-F::from(1022u64));

        let (mantissa_bits, l_bits) = {
            let mut bits = mantissa
                .value()
                .unwrap_or(F::zero())
                .into_repr()
                .to_bits_le()[..mantissa_bit_length]
                .to_vec();

            let max_l: BigUint = (exponent.value().unwrap_or(F::zero()) + F::from(1022u64))
                .into_repr()
                .try_into()
                .unwrap();

            let l = cmp::min(
                max_l.to_usize().unwrap_or(0) + 1,
                bits.iter().rev().position(|&i| i).unwrap_or(0),
            );

            bits.rotate_right(l);

            (
                Self::new_bits_witness(cs.clone(), &bits)?,
                Self::new_bits_witness(cs.clone(), &F::BigInt::from(l as u64).to_bits_le()[..7])?,
            )
        };

        Boolean::le_bits_to_fp_var(&mantissa_bits)?
            .enforce_equal(&(mantissa * two.pow_le(&l_bits)?))?;

        let exponent = exponent + one - Boolean::le_bits_to_fp_var(&l_bits)?;

        let (_, exponent_underflow) = Self::to_abs_n_bits(&(&min_exponent - &exponent), 11)?;

        let is_subnormal = exponent_underflow.or(&mantissa.is_zero()?)?;

        let exponent = is_subnormal.select(&min_exponent, &exponent)?;

        is_subnormal
            .or(mantissa_bits.last().unwrap())? // TODO: check this. Malicious prover may cheat.
            .enforce_equal(&Boolean::TRUE)?;

        Ok((mantissa_bits, exponent))
    }

    fn round(mantissa_bits: &[Boolean<F>], w: usize) -> Result<FpVar<F>, SynthesisError> {
        let q = Boolean::le_bits_to_fp_var(&mantissa_bits[w + 1..])?;
        let r = Boolean::le_bits_to_fp_var(&mantissa_bits[..w + 1])?;

        let is_half = r.is_eq(&FpVar::Constant(F::from(1u128 << w)))?;
        let q_lsb = &mantissa_bits[w + 1];
        let r_msb = &mantissa_bits[w];

        let carry = is_half.select(q_lsb, r_msb)?;

        Ok(q + FpVar::from(carry))
    }

    fn fix_overflow(
        mantissa: &FpVar<F>,
        exponent: &FpVar<F>,
    ) -> Result<(FpVar<F>, FpVar<F>), SynthesisError> {
        let one = FpVar::one();
        let overflow = mantissa.is_eq(&FpVar::Constant(F::from(1u128 << 53)))?;

        Ok((
            mantissa * overflow.select(&one.double()?.inverse()?, &one)?,
            exponent + FpVar::from(overflow),
        ))
    }

    fn add(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        const W: usize = 55;

        let cs = x.cs.clone();

        let one = FpVar::one();
        let two = one.double()?;
        let two_to_w = FpVar::Constant(F::from(1u128 << W));

        let (delta_bits, ex_le_ey) = Self::to_abs_n_bits(&(&y.exponent - &x.exponent), 11)?;

        let exponent = ex_le_ey.select(&y.exponent, &x.exponent)?;

        let (delta_bits, delta_le_w) = Self::to_abs_n_bits(
            &(FpVar::Constant(F::from(W as u64)) - Boolean::le_bits_to_fp_var(&delta_bits)?),
            11,
        )?;

        let two_to_delta = delta_le_w.select(&two.pow_le(&delta_bits)?, &one)?;

        let xx = &x.sign * &x.mantissa;
        let yy = &y.sign * &y.mantissa;
        let zz = ex_le_ey.select(&xx, &yy)?;
        let ww = &xx + &yy - &zz;

        let s = zz * two_to_delta + ww * &two_to_w;

        let (s_bits, s_ge_0) = Self::to_abs_n_bits(&s, W + 54)?;

        let s = Boolean::le_bits_to_fp_var(&s_bits)?;

        let sign = x
            .sign
            .is_eq(&y.sign)?
            .select(&x.sign, &(FpVar::from(s_ge_0).double()? - &one))?;

        let (s_bits, exponent) = Self::normalize(&s, W + 54, &exponent)?;

        let mantissa = Self::round(&s_bits, W)?;

        let (mantissa, exponent) = Self::fix_overflow(&mantissa, &exponent)?;

        Ok(Self {
            cs,
            sign,
            exponent,
            mantissa,
        })
    }

    fn mul(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        const W: usize = 55;

        let cs = x.cs.clone();

        let sign = &x.sign * &y.sign;

        let p = &x.mantissa * &y.mantissa;

        let exponent = &x.exponent + &y.exponent + FpVar::Constant(F::from(W as u64));

        let (p_bits, exponent) = Self::normalize(&p, 106 + W, &exponent)?;

        let mantissa = Self::round(&p_bits, 52 + W)?;

        let (mantissa, exponent) = Self::fix_overflow(&mantissa, &exponent)?;

        Ok(Self {
            cs,
            sign,
            exponent,
            mantissa,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::{
        error::Error,
        fs::File,
        io::{BufRead, BufReader},
        panic,
    };

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
    use ark_std::test_rng;
    use rand::thread_rng;

    use super::*;

    #[test]
    fn add_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = FloatVar::new_witness(cs.clone(), || Ok(0.1))?;
        let b = FloatVar::new_witness(cs.clone(), || Ok(0.2))?;

        println!("{}", a + b);

        assert!(cs.is_satisfied()?);
        println!("{}", cs.num_constraints());

        Ok(())
    }

    #[test]
    fn mul_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = FloatVar::new_witness(cs.clone(), || Ok(0.1))?;
        let b = FloatVar::new_witness(cs.clone(), || Ok(0.2))?;

        println!("{}", a * b);

        assert!(cs.is_satisfied()?);
        println!("{}", cs.num_constraints());

        Ok(())
    }

    #[test]
    fn test_add() -> Result<(), Box<dyn Error>> {
        pub struct Circuit {
            a: f64,
            b: f64,
            c: f64,
        }

        impl<F: PrimeField> ConstraintSynthesizer<F> for Circuit {
            fn generate_constraints(
                self,
                cs: ConstraintSystemRef<F>,
            ) -> ark_relations::r1cs::Result<()> {
                let a = FloatVar::new_witness(cs.clone(), || Ok(self.a))?;
                let b = FloatVar::new_witness(cs.clone(), || Ok(self.b))?;
                let c = FloatVar::new_input(cs.clone(), || Ok(self.c))?;
                let d = a + b;

                FloatVar::equal(&d, &c)?;
                Ok(())
            }
        }

        let rng = &mut thread_rng();

        let params = generate_random_parameters::<Bls12_381, _, _>(
            Circuit {
                a: 0f64,
                b: 0f64,
                c: 0f64,
            },
            rng,
        )?;
        let pvk = prepare_verifying_key(&params.vk);

        let test = |a: f64, b: f64| {
            let r = panic::catch_unwind(|| {
                let c = a + b;

                let proof =
                    create_random_proof(Circuit { a, b, c }, &params, &mut test_rng()).unwrap();

                verify_proof(&pvk, &proof, &FloatVar::input(c)).unwrap()
            });
            assert!(r.is_ok() && r.unwrap(), "{} {}", a, b);
        };

        for line in BufReader::new(File::open("tests/add")?).lines() {
            let line = line?;
            let v = line.split(' ').collect::<Vec<_>>();
            let a = f64::from_bits(u64::from_str_radix(v[0], 16)?);
            let b = f64::from_bits(u64::from_str_radix(v[1], 16)?);
            let c = f64::from_bits(u64::from_str_radix(v[2], 16)?);
            if !(a.is_nan()
                || a.is_infinite()
                || b.is_nan()
                || b.is_infinite()
                || c.is_nan()
                || c.is_infinite())
            {
                test(a, b);
            }
        }

        Ok(())
    }

    #[test]
    fn test_mul() -> Result<(), Box<dyn Error>> {
        pub struct Circuit {
            a: f64,
            b: f64,
            c: f64,
        }

        impl<F: PrimeField> ConstraintSynthesizer<F> for Circuit {
            fn generate_constraints(
                self,
                cs: ConstraintSystemRef<F>,
            ) -> ark_relations::r1cs::Result<()> {
                let a = FloatVar::new_witness(cs.clone(), || Ok(self.a))?;
                let b = FloatVar::new_witness(cs.clone(), || Ok(self.b))?;
                let c = FloatVar::new_input(cs.clone(), || Ok(self.c))?;
                let d = a * b;

                FloatVar::equal(&d, &c)?;
                Ok(())
            }
        }

        let rng = &mut thread_rng();

        let params = generate_random_parameters::<Bls12_381, _, _>(
            Circuit {
                a: 0f64,
                b: 0f64,
                c: 0f64,
            },
            rng,
        )?;
        let pvk = prepare_verifying_key(&params.vk);

        let test = |a: f64, b: f64| {
            let r = panic::catch_unwind(|| {
                let c = a * b;

                let proof =
                    create_random_proof(Circuit { a, b, c }, &params, &mut test_rng()).unwrap();

                verify_proof(&pvk, &proof, &FloatVar::input(c)).unwrap()
            });
            assert!(r.is_ok() && r.unwrap(), "{} {}", a, b);
        };

        for line in BufReader::new(File::open("tests/mul")?).lines() {
            let line = line?;
            let v = line.split(' ').collect::<Vec<_>>();
            let a = f64::from_bits(u64::from_str_radix(v[0], 16)?);
            let b = f64::from_bits(u64::from_str_radix(v[1], 16)?);
            let c = f64::from_bits(u64::from_str_radix(v[2], 16)?);
            if !(a.is_nan()
                || a.is_infinite()
                || b.is_nan()
                || b.is_infinite()
                || c.is_nan()
                || c.is_infinite())
            {
                test(a, b);
            }
        }

        Ok(())
    }
}
