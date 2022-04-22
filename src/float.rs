use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::Debug,
};

use crate::utils::{signed_to_field, ToBigUint};
use ark_ff::{PrimeField, Zero};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    R1CSVar, ToBitsGadget,
};
use ark_relations::{
    r1cs::{Namespace, SynthesisError},
};
use num::{BigUint, Float, ToPrimitive};

#[derive(Clone)]
pub struct FloatVar<F: PrimeField> {
    pub sign: FpVar<F>,
    pub exponent: FpVar<F>,
    pub mantissa: FpVar<F>,
}

impl<F: PrimeField> Debug for FloatVar<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FloatVar")
            .field("sign", &self.sign.value().unwrap_or(F::zero()))
            .field("exponent", &self.exponent.value().unwrap_or(F::zero()))
            .field("mantissa", &self.mantissa.value().unwrap_or(F::zero()))
            .finish()
    }
}

impl<F: PrimeField> FloatVar<F> {
    pub fn verifier_input(i: f64) -> [F; 3] {
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
        let i = *f()?.borrow();
        let cs = cs.into().cs();
        let (mantissa, exponent, sign) = Float::integer_decode(i);
        let sign = FpVar::new_variable(
            cs.clone(),
            || match sign {
                1 => Ok(F::one()),
                -1 => Ok(-F::one()),
                _ => Err(SynthesisError::AssignmentMissing),
            },
            mode,
        )?;
        let exponent = FpVar::new_variable(
            cs.clone(),
            || Ok(signed_to_field::<F, _>(exponent + 52)),
            mode,
        )?;
        let mantissa = FpVar::new_variable(cs.clone(), || Ok(F::from(mantissa)), mode)?;
        Ok(Self {
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

impl<F: PrimeField> FloatVar<F> {
    pub fn equal(x: &Self, y: &Self) -> Result<(), SynthesisError> {
        x.sign.enforce_equal(&y.sign)?;
        x.exponent.enforce_equal(&y.exponent)?;
        x.mantissa.enforce_equal(&y.mantissa)?;
        Ok(())
    }

    pub fn neg(self) -> Self {
        Self {
            sign: FpVar::zero() - self.sign,
            exponent: self.exponent,
            mantissa: self.mantissa,
        }
    }

    pub fn add(cs: impl Into<Namespace<F>>, x: Self, y: Self) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();

        let two = FpVar::one().double()?;

        let b = x
            .exponent
            .is_cmp_unchecked(&y.exponent, Ordering::Less, false)?;

        let exponent = b.select(&y.exponent, &x.exponent)?;
        let delta = &exponent + &exponent - &x.exponent - &y.exponent;

        let v = two.pow_le(&delta.to_bits_le()?)?;

        let unchanged_sign = b.select(&y.sign, &x.sign)?;
        let unchanged_mantissa = b.select(&y.mantissa, &&x.mantissa)?;

        let changed_sign = &x.sign + &y.sign - &unchanged_sign;
        let changed_mantissa = &x.mantissa + &y.mantissa - &unchanged_mantissa;

        let (changed_mantissa, removed) = {
            let changed = changed_mantissa.to_biguint();
            let delta = delta.to_biguint().to_i64().unwrap();
            let q = &changed >> delta;
            let r = &changed - (&q << delta);
            let q = FpVar::new_witness(cs.clone(), || match F::BigInt::try_from(q) {
                Ok(q) => Ok(F::from_repr(q).unwrap()),
                Err(_) => panic!(),
            })?;
            let r = FpVar::new_witness(cs.clone(), || match F::BigInt::try_from(r) {
                Ok(r) => Ok(F::from_repr(r).unwrap()),
                Err(_) => panic!(),
            })?;
            changed_mantissa.enforce_equal(&(&q * &v + &r))?;
            // TODO: r.enforce_cmp(&v, Ordering::Less, false)?;
            (q, r)
        };

        let (sign, exponent, mantissa) = {
            let sum = changed_mantissa * changed_sign + unchanged_mantissa * unchanged_sign;

            let b = sum.is_cmp_unchecked(&FpVar::zero(), Ordering::Less, false)?;

            let sign = b.select(&FpVar::one().negate()?, &FpVar::one())?;
            let sum = sum * &sign;

            let (q, e, r) = {
                let sum = sum.to_biguint();

                let mut normalized = sum.clone();

                let mut delta_e = 0i64;
                if !normalized.is_zero() {
                    while normalized >= BigUint::from(1u64 << 53) {
                        delta_e += 1;
                        normalized >>= 1u8;
                    }
                    while normalized < BigUint::from(1u64 << 52) {
                        delta_e -= 1;
                        normalized <<= 1u8;
                    }
                } else {
                    delta_e = match exponent.negate()?.to_biguint().to_i64() {
                        Some(e) => e,
                        None => -exponent.to_biguint().to_i64().unwrap(),
                    } - 1023;
                }
                let r = if delta_e <= 0 {
                    BigUint::zero()
                } else {
                    sum - (&normalized << (delta_e))
                };
                (
                    FpVar::new_witness(cs.clone(), || match F::BigInt::try_from(normalized) {
                        Ok(q) => Ok(F::from_repr(q).unwrap()),
                        Err(_) => panic!(),
                    })?,
                    FpVar::new_witness(cs.clone(), || Ok(signed_to_field::<F, _>(delta_e)))?,
                    FpVar::new_witness(cs.clone(), || match F::BigInt::try_from(r) {
                        Ok(r) => Ok(F::from_repr(r).unwrap()),
                        Err(_) => panic!(),
                    })?,
                )
            };

            q.is_zero()?
                .or(&q
                    .is_cmp(
                        &FpVar::new_constant(cs.clone(), F::from(1u64 << 52))?,
                        Ordering::Greater,
                        true,
                    )?
                    .and(&q.is_cmp(
                        &FpVar::new_constant(cs.clone(), F::from(1u64 << 53))?,
                        Ordering::Less,
                        false,
                    )?)?)?
                .enforce_equal(&Boolean::TRUE)?;

            let b = e.is_cmp_unchecked(&FpVar::zero(), Ordering::Less, false)?;
            let m = b.select(&FpVar::zero(), &e)?;
            let n = &m - &e;
            (&sum * two.pow_le(&n.to_bits_le()?)?)
                .enforce_equal(&(&q * two.pow_le(&m.to_bits_le()?)? + &r))?;
            // TODO: constraint on r?

            let g = FpVar::new_constant(cs.clone(), F::from(120u64))?;

            let b = delta.is_cmp_unchecked(&g, Ordering::Greater, false)?;
            
            let delta = b.select(&g, &delta)?;
            let v = two.pow_le(&delta.to_bits_le()?)?;
            let removed = b.select(&FpVar::zero(), &removed)?;

            let u = (&delta + &e)
                .is_cmp_unchecked(&FpVar::zero(), Ordering::Greater, false)?
                .select(
                    &two.pow_le(&(&delta + &e - FpVar::one()).to_bits_le()?)?,
                    &FpVar::zero(),
                )?;

            let r = r * v + removed;

            let q = &q
                + r.is_eq(&u)?.select(&q, &(u - r).double()?)?.to_bits_le()?[0]
                    .select(&FpVar::one(), &FpVar::zero())?;

            (sign, exponent + e, q)
        };

        Ok(FloatVar {
            sign,
            exponent,
            mantissa,
        })
    }

    pub fn mul(cs: impl Into<Namespace<F>>, x: Self, y: Self) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();

        let v = FpVar::new_constant(cs.clone(), F::from(1u64 << 52))?;
        let w = v.double()?;

        let sign = x.sign * y.sign;
        let (exponent, mantissa) = {
            let p = x.mantissa * y.mantissa;
            let b = &p.to_bits_le()?[105];

            let p = b.select(&p, &p.double()?)?;
            let e = x.exponent + y.exponent + b.select(&FpVar::one(), &FpVar::zero())?;

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

            (e, q)
        };

        Ok(FloatVar {
            sign,
            exponent,
            mantissa,
        })
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Bls12_381;
    use ark_groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
    };
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
    use rand::{thread_rng, Rng};

    use super::*;

    #[derive(Clone)]
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
            let d = FloatVar::add(cs, a, b)?;

            FloatVar::equal(&d, &c)?;
            Ok(())
        }
    }

    #[test]
    fn test() {
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

        for _ in 0..100 {
            let a = -rng.gen::<f64>();
            let b = -rng.gen::<f64>();

            println!("{} {}", a, b);
            let c = a + b;

            let proof = create_random_proof(Circuit { a, b, c }, &params, rng).unwrap();

            assert!(verify_proof(&pvk, &proof, &FloatVar::verifier_input(c)).unwrap());
        }
    }
}
