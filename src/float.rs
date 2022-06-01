use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
    ops::Neg,
};

use crate::utils::{signed_to_field, ToBigUint};
use ark_ff::{BigInteger, PrimeField, Zero};
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
use num::{BigUint, Float};

#[derive(Clone, Debug)]
pub struct FloatVar<F: PrimeField> {
    cs: ConstraintSystemRef<F>,
    pub sign: FpVar<F>,
    pub exponent: FpVar<F>,
    pub mantissa: FpVar<F>,
}

impl<F: PrimeField> Display for FloatVar<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Sign: {}\nExponent: {}\nMantissa: {}\n",
            &self.sign.value().unwrap_or(F::zero()),
            &self.exponent.value().unwrap_or(F::zero()),
            &self.mantissa.value().unwrap_or(F::zero())
        )
    }
}

impl<F: PrimeField> FloatVar<F> {
    pub fn input(i: f64) -> [F; 3] {
        let (mantissa, exponent, sign) = Float::integer_decode(i);
        let sign = match sign {
            1 => F::one(),
            -1 => -F::one(),
            _ => unreachable!(),
        };
        let mantissa = F::from(mantissa);
        let exponent = signed_to_field::<F, _>(exponent + 52);
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

impl<F: PrimeField> ToBigUint for FpVar<F> {
    fn to_biguint(&self) -> BigUint {
        match self.value() {
            Ok(v) => v.into_repr().into(),
            Err(_) => BigUint::zero(),
        }
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
        (&x.exponent * &x.mantissa).enforce_equal(&(&y.exponent * &y.mantissa))?;
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

    fn to_n_bits(x: &FpVar<F>, n: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = x.cs();

        let bits = Self::new_bits_witness(
            cs,
            &match x.value() {
                Ok(x) => x.into_repr().to_bits_le()[..n].to_vec(),
                Err(_) => vec![false; n],
            },
        )?;

        x.enforce_equal(&Boolean::le_bits_to_fp_var(&bits)?)?;

        Ok(bits)
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

    fn add(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        const W: usize = 54;

        let cs = x.cs.clone();

        let one = FpVar::one();
        let two = one.double()?;
        let two_inv = two.inverse()?;
        let two_to_53 = FpVar::Constant(F::from(1u128 << 53));
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
        let is_zero = s.is_zero()?;

        let (s_bits, s_ge_0) = Self::to_abs_n_bits(&s, W + 54)?;

        let sign = x
            .sign
            .is_eq(&y.sign)?
            .select(&x.sign, &(FpVar::from(s_ge_0).double()? - &one))?;

        let s = Boolean::le_bits_to_fp_var(&s_bits)?;

        let (new_s_bits, l_bits) = {
            let mut s_bits = s_bits
                .iter()
                .map(|i| i.value().unwrap_or(false))
                .collect::<Vec<_>>();

            let l = s_bits.iter().rev().position(|&i| i).unwrap_or(0);

            s_bits.rotate_right(l);

            (
                Self::new_bits_witness(cs.clone(), &s_bits)?,
                Self::new_bits_witness(cs.clone(), &F::BigInt::from(l as u64).to_bits_le()[..7])?,
            )
        };

        Boolean::le_bits_to_fp_var(&new_s_bits)?.enforce_equal(&(&s * two.pow_le(&l_bits)?))?;

        new_s_bits
            .last()
            .unwrap()
            .or(&is_zero)?
            .enforce_equal(&Boolean::TRUE)?;

        let r = Boolean::le_bits_to_fp_var(&new_s_bits[..W + 1])?;
        let q = Boolean::le_bits_to_fp_var(&new_s_bits[W + 1..])?;

        let is_half = r.is_eq(&two_to_w)?;
        let q_lsb = &new_s_bits[W + 1];
        let r_msb = &new_s_bits[W];

        let q = &q + FpVar::from(is_half.select(q_lsb, r_msb)?);

        let is_overflow = q.is_eq(&two_to_53)?;

        let mantissa = q * is_overflow.select(&two_inv, &one)?;
        let exponent =
            exponent + one - Boolean::le_bits_to_fp_var(&l_bits)? + FpVar::from(is_overflow);

        Ok(FloatVar {
            cs,
            sign,
            exponent,
            mantissa,
        })
    }

    fn mul(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        let cs = x.cs.clone();

        let sign = &x.sign * &y.sign;

        let p = &x.mantissa * &y.mantissa;
        let p_bits = Self::to_n_bits(&p, 106)?;

        let p_msb = &p_bits[105];

        let exponent = &x.exponent + &y.exponent + p_msb.select(&FpVar::one(), &FpVar::zero())?;

        let q = p_msb.select(
            &Boolean::le_bits_to_fp_var(&p_bits[53..106])?,
            &Boolean::le_bits_to_fp_var(&p_bits[52..105])?,
        )?;
        let r = p_msb.select(
            &Boolean::le_bits_to_fp_var(&p_bits[..53])?,
            &Boolean::le_bits_to_fp_var(&p_bits[..52])?.double()?,
        )?;

        let is_half = r.is_eq(&FpVar::Constant(F::from(1u64 << 52)))?;
        let q_lsb = p_msb.select(&p_bits[53], &p_bits[52])?;
        let r_msb = p_msb.select(&p_bits[52], &p_bits[51])?;

        let mantissa = &q + FpVar::from(is_half.select(&q_lsb, &r_msb)?);

        Ok(FloatVar {
            cs,
            sign,
            exponent,
            mantissa,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::panic;

    use ark_bls12_381::{Bls12_381, Fr};
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
    use ark_std::test_rng;
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn add_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = FloatVar::new_witness(cs.clone(), || Ok(0.1)).unwrap();
        let b = FloatVar::new_witness(cs.clone(), || Ok(0.2)).unwrap();

        let _ = a + b;

        assert!(cs.is_satisfied().unwrap());
        println!("{}", cs.num_constraints());
    }

    #[test]
    fn mul_constraints() {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = FloatVar::new_witness(cs.clone(), || Ok(0.1)).unwrap();
        let b = FloatVar::new_witness(cs.clone(), || Ok(0.2)).unwrap();

        let _ = a * b;

        assert!(cs.is_satisfied().unwrap());
        println!("{}", cs.num_constraints());
    }

    #[test]
    fn test_add() {
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
        )
        .unwrap();
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

        for _ in 0..20 {
            test(
                -rng.gen::<f64>() * rng.gen::<u32>() as f64,
                rng.gen::<f64>() * rng.gen::<u32>() as f64,
            );
        }

        for _ in 0..20 {
            test(
                rng.gen::<f64>() * rng.gen::<u32>() as f64,
                rng.gen::<f64>() * rng.gen::<u32>() as f64,
            );
        }

        for _ in 0..20 {
            test(rng.gen::<f64>() * rng.gen::<u32>() as f64, 0.);
        }

        for _ in 0..20 {
            test(rng.gen::<f64>() * rng.gen::<u32>() as f64, -0.);
        }

        test(0.1, 0.2);
        test(0.1, -0.2);
        test(1., 1.);
        test(1., -1.);
        test(1., 0.9999999999999999);
        test(1., -0.9999999999999999);
        test(-1., 0.9999999999999999);
        test(-1., -0.9999999999999999);
        test(4503599627370496., -0.9999999999999999);
        test(4503599627370496., 1.);
        test(4503599627370496., 4503599627370496.);
        test(18014398509481984., -3.99999999999999955591079014994);
        test(0.0, 0.0);
        test(0.0, -0.0);
        test(-0.0, 0.0);
        test(-0.0, -0.0);
    }

    #[test]
    fn test_mul() {
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
        )
        .unwrap();
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

        for _ in 0..20 {
            test(
                -rng.gen::<f64>() * rng.gen::<u32>() as f64,
                rng.gen::<f64>() * rng.gen::<u32>() as f64,
            );
        }

        for _ in 0..20 {
            test(
                rng.gen::<f64>() * rng.gen::<u32>() as f64,
                rng.gen::<f64>() * rng.gen::<u32>() as f64,
            );
        }

        for _ in 0..20 {
            test(rng.gen::<f64>() * rng.gen::<u32>() as f64, 0.);
        }

        for _ in 0..20 {
            test(rng.gen::<f64>() * rng.gen::<u32>() as f64, -0.);
        }

        test(0.1, 0.2);
        test(0.1, -0.2);
        test(1., 1.);
        test(1., -1.);
        test(1., 0.9999999999999999);
        test(1., -0.9999999999999999);
        test(-1., 0.9999999999999999);
        test(-1., -0.9999999999999999);
        test(4503599627370496., -0.9999999999999999);
        test(4503599627370496., 1.);
        test(4503599627370496., 4503599627370496.);
        test(18014398509481984., -3.99999999999999955591079014994);
        test(0.0, 0.0);
        test(0.0, -0.0);
        test(-0.0, 0.0);
        test(-0.0, -0.0);
    }
}
