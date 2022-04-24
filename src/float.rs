use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::{Debug, Display},
    ops::Neg,
};

use crate::utils::{signed_to_field, ToBigUint};
use ark_ff::{One, PrimeField, Zero};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    R1CSVar, ToBitsGadget,
};
use ark_relations::{
    ns,
    r1cs::{ConstraintSystemRef, Namespace, SynthesisError},
};
use num::{BigUint, Float, ToPrimitive};

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
        x.exponent.enforce_equal(&y.exponent)?;
        x.mantissa.enforce_equal(&y.mantissa)?;
        Ok(())
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
        let cs = x.cs.clone();

        let two = FpVar::one().double()?;

        let b = x
            .exponent
            .is_cmp_unchecked(&y.exponent, Ordering::Less, false)?;

        let exponent = b.select(&y.exponent, &x.exponent)?;
        let delta = &exponent + &exponent - &x.exponent - &y.exponent;

        let max = FpVar::new_constant(cs.clone(), F::from(64u64))?;

        let delta = delta
            .is_cmp_unchecked(&max, Ordering::Greater, false)?
            .select(&max, &delta)?;

        let v = two.pow_le(&delta.to_bits_le()?)?;

        let xx = &x.sign * &x.mantissa;
        let yy = &y.sign * &y.mantissa;

        let unchanged = b.select(&xx, &yy)?;
        let changed = (&xx + &yy - &unchanged) * &v;

        let (sign, exponent, mantissa) = {
            let sum = changed + unchanged;

            let sign = sum
                .is_cmp_unchecked(&FpVar::zero(), Ordering::Less, false)?
                .select(&FpVar::one().negate()?, &FpVar::one())?;
            let sum = sum * &sign;

            let (q, e) = {
                let sum = sum.to_biguint();
                let delta = delta.to_biguint().to_i64().unwrap();

                let mut normalized = sum.clone();

                let mut delta_e = 0;
                if !normalized.is_zero() {
                    while normalized >= BigUint::one() << (delta + 53) {
                        delta_e += 1;
                        normalized >>= 1u8;
                    }
                    while normalized < BigUint::one() << (delta + 52) {
                        delta_e -= 1;
                        normalized <<= 1u8;
                    }
                    normalized >>= delta;
                } else {
                    delta_e = match exponent.negate()?.to_biguint().to_i64() {
                        Some(e) => e,
                        None => -exponent.to_biguint().to_i64().unwrap(),
                    } - 1023;
                }
                (
                    FpVar::new_witness(cs.clone(), || match F::BigInt::try_from(normalized) {
                        Ok(q) => Ok(F::from_repr(q).unwrap()),
                        Err(_) => panic!(),
                    })?,
                    FpVar::new_witness(cs.clone(), || Ok(signed_to_field::<F, _>(delta_e)))?,
                )
            };

            let m = FpVar::new_constant(cs.clone(), F::from(1u64 << 52))?;
            let n = m.double()?;

            q.is_zero()?
                .or(&q.is_cmp(&m, Ordering::Greater, true)?.and(&q.is_cmp(
                    &n,
                    Ordering::Less,
                    false,
                )?)?)?
                .enforce_equal(&Boolean::TRUE)?;

            let delta = &delta + &e;
            let b = delta.is_cmp_unchecked(&FpVar::zero(), Ordering::Greater, false)?;

            let r = b.select(
                &(&sum - &q * two.pow_le(&delta.to_bits_le()?)?),
                &FpVar::zero(),
            )?;

            let u = b.select(
                &two.pow_le(&(&delta - FpVar::one()).to_bits_le()?)?,
                &FpVar::one(),
            )?;

            let q = &q
                + r.is_eq(&u)?.select(&q, &(u - r).double()?)?.to_bits_le()?[0]
                    .select(&FpVar::one(), &FpVar::zero())?;

            let overflow = q.is_eq(&n)?;
            let e = e + overflow.select(&FpVar::one(), &FpVar::zero())?;
            let q = q * overflow.select(&two.inverse()?, &FpVar::one())?;

            (sign, exponent + e, q)
        };

        Ok(FloatVar {
            cs,
            sign,
            exponent,
            mantissa,
        })
    }

    fn mul(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        let cs = x.cs.clone();

        let v = FpVar::new_constant(cs.clone(), F::from(1u64 << 52))?;
        let w = v.double()?;

        let sign = &x.sign * &y.sign;
        let (exponent, mantissa) = {
            let p = &x.mantissa * &y.mantissa;
            let b = &p.to_bits_le()?[105];

            let p = b.select(&p, &p.double()?)?;
            let e = &x.exponent + &y.exponent + b.select(&FpVar::one(), &FpVar::zero())?;

            let q = {
                let q = p.to_biguint() >> 53u8;

                FpVar::new_witness(cs.clone(), || match F::BigInt::try_from(q) {
                    Ok(q) => Ok(F::from_repr(q).unwrap()),
                    Err(_) => panic!(),
                })?
            };

            let r = p - &q * &w;
            r.enforce_cmp(&w, Ordering::Less, false)?;

            let q = &q
                + r.is_eq(&v)?.select(&q, &(v - r).double()?)?.to_bits_le()?[0]
                    .select(&FpVar::one(), &FpVar::zero())?;

            (
                q.is_zero()?
                    .select(&FpVar::new_constant(cs.clone(), -F::from(1023u64))?, &e)?,
                q,
            )
        };

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

    use ark_bls12_381::Bls12_381;
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
    use ark_std::test_rng;
    use rand::{thread_rng, Rng};

    use super::*;

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
    }
}
