use std::{borrow::Borrow, ops::Neg, fmt::{Display, Formatter}};

use crate::{
    impl_ops,
    r1cs::{Namespace, SynthesisError, ConstraintSystemRef},
    r1cs_std::{
        alloc::{AllocVar, AllocationMode},
        boolean::Boolean,
        fields::{fp::FpVar, FieldVar},
        prelude::EqGadget,
        select::CondSelectGadget,
        R1CSVar,
    },
    traits::BitDecompose,
};
use ark_ff::{BigInteger, One, PrimeField};
use ark_std::Zero;
use num::{BigUint, Integer, traits::float::FloatCore, ToPrimitive};

#[derive(Clone)]
pub struct FloatVar<F: PrimeField, const E: usize, const M: usize> {
    pub sign: Boolean<F>,
    pub exponent: FpVar<F>,
    pub mantissa: FpVar<F>,
    is_abnormal: Boolean<F>,
}

impl<F: PrimeField, const E: usize, const M: usize> Display for FloatVar<F, E, M> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let v = self.value().unwrap();
        if f.alternate() {
            write!(f, "{:0len$x}", v, len = (1 + E + M) / 8)
        } else {
            match 1 + E + M {
                64 => write!(f, "{}", f64::from_bits(v.to_u64().unwrap())),
                32 => write!(f, "{}", f32::from_bits(v.to_u32().unwrap())),
                _ => panic!("Unsupported float length")
            }
        }
    }
}

impl<F: PrimeField, U: FloatCore, const E: usize, const M: usize> AllocVar<U, F>
    for FloatVar<F, E, M>
{
    fn new_variable<T: Borrow<U>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();

        let (m, e, s) = f()?.borrow().integer_decode();

        let s = s == -1;
        let e = (e + ((1 << (E - 1)) - 1 + M) as i16) as u128;
        let m = if e == 0 {
            m >> 1
        } else {
            m - (1 << M)
        } as u128;

        let sign = Boolean::new_variable(cs.clone(), || Ok(s), mode)?;
        let exponent = FpVar::new_variable(cs.clone(), || Ok(F::from(e)), mode)?;
        exponent.enforce_bit_length(E)?;
        let mantissa = FpVar::new_variable(cs.clone(), || Ok(F::from(m)), mode)?;
        mantissa.enforce_bit_length(M)?;

        let exponent_min = -F::from(((1 << (E - 1)) - 1) as u128);
        let exponent_max = F::from((1 << (E - 1)) as u128);

        let exponent = exponent + exponent_min;

        let mantissa_is_zero = mantissa.is_zero()?;
        let exponent_is_min = exponent.is_eq(&FpVar::constant(exponent_min))?;
        let exponent_is_max = exponent.is_eq(&FpVar::constant(exponent_max))?;

        let (l, two_to_l) = {
            let l = mantissa
                .value()
                .unwrap_or_default()
                .into_bigint()
                .to_bits_le()[..M]
                .iter()
                .rev()
                .position(|&i| i)
                .unwrap_or(M);

            (
                FpVar::new_hint(cs.clone(), || Ok(F::from(l as u128)))?,
                FpVar::new_hint(cs.clone(), || Ok(F::from(1u128 << l)))?,
            )
        };
        // TODO: enforce (l, two_to_l) is in lookup table [0, M]

        let shifted_mantissa = &mantissa * &two_to_l;
        (&shifted_mantissa - FpVar::from(mantissa_is_zero.not()) * F::from(1u128 << (M - 1)))
            .enforce_bit_length(M - 1)?;

        let exponent = exponent_is_min.select(&(l.negate()? + exponent_min), &exponent)?;
        let mantissa = exponent_is_min.select(
            &shifted_mantissa.double()?,
            &exponent_is_max
                .and(&mantissa_is_zero.not())?
                .select(&FpVar::zero(), &(&mantissa + F::from(1u128 << M)))?,
        )?;

        Ok(Self {
            sign,
            exponent,
            mantissa,
            is_abnormal: exponent_is_max,
        })
    }
}

impl<F: PrimeField, const E: usize, const M: usize> R1CSVar<F> for FloatVar<F, E, M> {
    type Value = BigUint;

    fn cs(&self) -> ConstraintSystemRef<F> {
        unimplemented!("Call `self.sign.cs()`/`self.exponent.cs()`/`self.mantissa.cs()` instead")
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let s = BigUint::from(self.sign.value()? as u128);
        let e: BigUint = (self.exponent.value()? + F::from(((1 << (E - 1)) - 1 + M) as u128)).into();
        let m: BigUint = self.mantissa.value()?.into();
        let is_abnormal = self.is_abnormal.value()?;

        if e <= BigUint::from(M) {
            assert!(!is_abnormal);
            return Ok((s << (M + E)) + (m >> (M + 1 - e.to_usize().unwrap())));
        } else {
            let e = e - BigUint::from(M);
            assert_eq!(e == BigUint::from((1u128 << E) - 1), is_abnormal);

            let m = if is_abnormal && m.is_zero() {
                BigUint::one()
            } else {
                m - BigUint::from(1u128 << M)
            };
            Ok((s << (M + E)) + (e << M) + m)
        }
    }
}

impl<F: PrimeField, const E: usize, const M: usize> CondSelectGadget<F> for FloatVar<F, E, M> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            sign: cond.select(&true_value.sign, &false_value.sign)?,
            exponent: cond.select(&true_value.exponent, &false_value.exponent)?,
            mantissa: cond.select(&true_value.mantissa, &false_value.mantissa)?,
            is_abnormal: cond.select(&true_value.is_abnormal, &false_value.is_abnormal)?,
        })
    }
}

impl<F: PrimeField, const E: usize, const M: usize> Neg for FloatVar<F, E, M> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::neg(&self)
    }
}

impl<F: PrimeField, const E: usize, const M: usize> Neg for &FloatVar<F, E, M> {
    type Output = FloatVar<F, E, M>;

    fn neg(self) -> Self::Output {
        FloatVar::neg(self)
    }
}

impl_ops!(
    FloatVar<F, E, M>,
    Add,
    add,
    AddAssign,
    add_assign,
    |a, b| { FloatVar::add(a, b).unwrap() },
    F: PrimeField, const E: usize, const M: usize
);

impl_ops!(
    FloatVar<F, E, M>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |a, b: &'a FloatVar<F, E, M>| { FloatVar::add(a, &-b).unwrap() },
    F: PrimeField, const E: usize, const M: usize
);

impl_ops!(
    FloatVar<F, E, M>,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |a, b| { FloatVar::mul(a, b).unwrap() },
    F: PrimeField, const E: usize, const M: usize
);

impl_ops!(
    FloatVar<F, E, M>,
    Div,
    div,
    DivAssign,
    div_assign,
    |a, b| { FloatVar::div(a, b).unwrap() },
    F: PrimeField, const E: usize, const M: usize
);

impl<F: PrimeField, const E: usize, const M: usize> EqGadget<F> for FloatVar<F, E, M> {
    // TODO: check NaN

    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Boolean::TRUE
            .and(&self.sign.is_eq(&other.sign)?)?
            .and(&self.exponent.is_eq(&other.exponent)?)?
            .and(&self.mantissa.is_eq(&other.mantissa)?)?
            .and(&self.is_abnormal.is_eq(&other.is_abnormal)?)
    }

    fn enforce_equal(&self, other: &Self) -> Result<(), SynthesisError> {
        self.sign.enforce_equal(&other.sign)?;
        self.exponent.enforce_equal(&other.exponent)?;
        self.mantissa.enforce_equal(&other.mantissa)?;
        self.is_abnormal.enforce_equal(&other.is_abnormal)?;
        Ok(())
    }
}

impl<F: PrimeField, const E: usize, const M: usize> FloatVar<F, E, M> {
    const E_MAX: u128 = 1 << (E - 1);
    const NEG_E_NORMAL_MIN: u128 = Self::E_MAX - 2;
    const NEG_E_MIN: u128 = Self::E_MAX - 1 + M as u128;

    fn neg(&self) -> Self {
        Self {
            sign: self.sign.not(),
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
            is_abnormal: self.is_abnormal.clone(),
        }
    }

    pub fn abs(&self) -> Self {
        Self {
            sign: Boolean::FALSE,
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
            is_abnormal: self.is_abnormal.clone(),
        }
    }

    fn round(
        mantissa: &FpVar<F>,
        mantissa_bit_length: usize,
        shift: &FpVar<F>,
        shift_max: usize,
        half_flag: &Boolean<F>,
    ) -> Result<FpVar<F>, SynthesisError> {
        let two_to_shift = FpVar::new_hint(shift.cs(), || {
            shift.value().map(|v| F::from(2u8).pow(v.into_bigint()))
        })?;
        // TODO: enforce (u, two_to_u) is in lookup table [0, u_max]

        let r_idx = shift_max + mantissa_bit_length - M - 2;
        let q_idx = r_idx + 1;
        let p_idx = q_idx + 1;
        let p_len = M;
        let s_len = r_idx;

        let (p, q, r, s) = {
            let cs = mantissa.cs().or(two_to_shift.cs());

            let v = mantissa.value().unwrap_or_default() * F::from(1u128 << shift_max)
                / two_to_shift.value().unwrap_or_default();
            let bits = v.into_bigint().to_bits_le();

            let p = F::from(F::BigInt::from_bits_le(&bits[p_idx..]));
            let s = F::from(F::BigInt::from_bits_le(&bits[..r_idx]));

            (
                FpVar::new_hint(cs.clone(), || Ok(p))?,
                Boolean::new_hint(cs.clone(), || Ok(bits[q_idx]))?,
                Boolean::new_hint(cs.clone(), || Ok(bits[r_idx]))?,
                FpVar::new_hint(cs.clone(), || Ok(s))?,
            )
        };

        p.enforce_bit_length(p_len)?;
        s.enforce_bit_length(s_len)?;

        let qq = p.double()? + FpVar::from(q.clone());
        let rr = FpVar::from(r.clone()) * F::from(1u128 << r_idx) + &s;

        (&qq * F::from(1u128 << q_idx) + &rr)
            .mul_equals(&two_to_shift, &(mantissa * F::from(1u128 << shift_max)))?;

        let is_half = rr
            .is_eq(&FpVar::constant(F::from(1u128 << r_idx)))?
            .and(half_flag)?;

        let carry = FpVar::from(is_half.select(&q, &r)?);

        Ok((qq + carry) * &two_to_shift)
    }

    fn fix_overflow(
        mantissa: &FpVar<F>,
        exponent: &FpVar<F>,
        input_is_abnormal: &Boolean<F>,
    ) -> Result<(FpVar<F>, FpVar<F>, Boolean<F>), SynthesisError> {
        let exponent_max = F::from(Self::E_MAX);

        let mantissa_overflow = mantissa.is_eq(&FpVar::Constant(F::from(1u128 << (M + 1))))?;
        let exponent = exponent + FpVar::from(mantissa_overflow.clone());
        let is_abnormal = (&exponent - FpVar::constant(exponent_max))
            .is_positive(E + 1)?
            .or(&input_is_abnormal)?;

        Ok((
            mantissa_overflow
                .or(&is_abnormal)?
                .select(&FpVar::constant(F::from(1u128 << M)), &mantissa)?,
            is_abnormal.select(&FpVar::constant(exponent_max), &exponent)?,
            is_abnormal,
        ))
    }

    fn add(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        let (delta, ex_le_ey) = (&y.exponent - &x.exponent).abs(E + 1)?;

        let exponent = ex_le_ey.select(&y.exponent, &x.exponent)? + FpVar::one();
        let delta = (delta.negate()? + F::from((M + 3) as u128)).max(&FpVar::zero(), E)?;
        let two_to_delta = FpVar::new_hint(delta.cs(), || {
            delta
                .value()
                .map(|delta| F::from(2u8).pow(delta.into_bigint()))
        })?;
        // TODO: enforce (delta, two_to_delta) is in lookup table [0, >=M + 3]

        let xx = x.sign.select(&x.mantissa.negate()?, &x.mantissa)?;
        let yy = y.sign.select(&y.mantissa.negate()?, &y.mantissa)?;
        let zz = ex_le_ey.select(&xx, &yy)?;
        let ww = &xx + &yy - &zz;

        let s = zz * two_to_delta + ww * F::from(1u128 << (M + 3));
        let mantissa_bit_length = (M + 3) + (M + 1) + 1;

        let (mantissa_ge_0, shift, two_to_shift) = {
            let cs = s.cs();
            let mantissa = s.value().unwrap_or_default();
            let mantissa_ge_0 = mantissa.into_bigint() < F::MODULUS_MINUS_ONE_DIV_TWO;

            let bits = if mantissa_ge_0 { mantissa } else { -mantissa }
                .into_bigint()
                .to_bits_le();

            let shift = bits[..mantissa_bit_length]
                .iter()
                .rev()
                .position(|&i| i)
                .unwrap_or(mantissa_bit_length);

            (
                Boolean::new_hint(cs.clone(), || Ok(mantissa_ge_0))?,
                FpVar::new_hint(cs.clone(), || Ok(F::from(shift as u128)))?,
                FpVar::new_hint(cs.clone(), || Ok(F::from(1u128 << shift)))?,
            )
        };
        // TODO: enforce range of shift [0, M + 4]
        // TODO: enforce (shift, two_to_shift) is in lookup table
        let mantissa = mantissa_ge_0.select(&s, &s.negate()?)? * two_to_shift;
        let mantissa_is_zero = mantissa.is_zero()?;
        (&mantissa
            - FpVar::from(mantissa_is_zero.not()) * F::from(1u128 << (mantissa_bit_length - 1)))
        .enforce_bit_length(mantissa_bit_length - 1)?;
        let exponent = mantissa_is_zero.select(
            &FpVar::constant(-F::from(Self::NEG_E_MIN)),
            &(exponent - shift),
        )?;

        let sign = x
            .sign
            .is_eq(&y.sign)?
            .select(&x.sign, &mantissa_ge_0.not())?;

        let mantissa = Self::round(
            &mantissa,
            mantissa_bit_length,
            &FpVar::zero(),
            0,
            &Boolean::TRUE,
        )?;

        let (mantissa, exponent, is_abnormal) =
            Self::fix_overflow(&mantissa, &exponent, &x.is_abnormal.or(&y.is_abnormal)?)?;

        Ok(Self {
            sign,
            exponent,
            mantissa: x.is_abnormal.select(
                &y.is_abnormal
                    .not()
                    .or(&xx.is_eq(&yy)?)?
                    .select(&x.mantissa, &FpVar::zero())?,
                &y.is_abnormal.select(&y.mantissa, &mantissa)?,
            )?,
            is_abnormal,
        })
    }

    fn mul(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        let sign = x.sign.xor(&y.sign)?;

        let mantissa = &x.mantissa * &y.mantissa;
        let mantissa_bit_length = (M + 1) * 2;

        let mantissa_msb = Boolean::new_hint(mantissa.cs(), || {
            mantissa
                .value()
                .map(|v| v.into_bigint().get_bit(mantissa_bit_length - 1))
        })?;
        (&mantissa
            - FpVar::from(mantissa_msb.clone()) * F::from(1u128 << (mantissa_bit_length - 1)))
        .enforce_bit_length(mantissa_bit_length - 1)?;
        let mantissa = &mantissa + mantissa_msb.select(&FpVar::zero(), &mantissa)?;
        let exponent = &x.exponent + &y.exponent + FpVar::from(mantissa_msb);

        let shift_max = M + 2;
        let mantissa = Self::round(
            &mantissa,
            mantissa_bit_length,
            &(exponent.negate()? - F::from(Self::NEG_E_NORMAL_MIN))
                .min(&FpVar::constant(F::from(shift_max as u128)), E + 1)?
                .max(&FpVar::zero(), E + 1)?,
            shift_max,
            &Boolean::TRUE,
        )?;

        let mantissa_is_zero = mantissa.is_zero()?;
        let exponent =
            mantissa_is_zero.select(&FpVar::constant(-F::from(Self::NEG_E_MIN)), &exponent)?;

        let input_is_abnormal = x.is_abnormal.or(&y.is_abnormal)?;

        let (mantissa, exponent, is_abnormal) =
            Self::fix_overflow(&mantissa, &exponent, &input_is_abnormal)?;

        Ok(Self {
            sign,
            exponent,
            mantissa: mantissa_is_zero.select(&FpVar::zero(), &mantissa)?,
            is_abnormal,
        })
    }

    fn div(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        let sign = x.sign.xor(&y.sign)?;

        let x_is_zero = x.mantissa.is_zero()?;
        let y_is_zero = y.mantissa.is_zero()?;

        let y_mantissa = y_is_zero.select(&FpVar::constant(F::from(1u128 << M)), &y.mantissa)?;

        let mantissa_bit_length = (M + 2) + 1;
        let (mantissa, mantissa_msb) = {
            let cs = x.mantissa.cs().or(y_mantissa.cs());
            let x: BigUint = x.mantissa.value().unwrap_or_default().into();
            let y: BigUint = y_mantissa.value().unwrap_or_default().into();
            let mantissa = (x << (M + 2)) / y;
            (
                FpVar::new_hint(cs.clone(), || Ok(F::from(mantissa.clone())))?,
                Boolean::new_hint(cs, || Ok(mantissa.bit(mantissa_bit_length as u64 - 1)))?,
            )
        };
        let remainder = &x.mantissa * F::from(1u128 << (M + 2)) - &mantissa * &y_mantissa;
        remainder.enforce_bit_length(M + 1)?;
        (&y_mantissa - &remainder - FpVar::one()).enforce_bit_length(M + 1)?;
        (&mantissa
            - FpVar::from(mantissa_msb.clone()) * F::from(1u128 << (mantissa_bit_length - 1)))
        .enforce_bit_length(mantissa_bit_length - 1)?;

        let mantissa = &mantissa + mantissa_msb.select(&FpVar::zero(), &mantissa)?;
        let exponent = &x.exponent - &y.exponent - FpVar::from(mantissa_msb.not());

        let shift_max = M + 2;
        let mantissa = Self::round(
            &mantissa,
            mantissa_bit_length,
            &(exponent.negate()? - F::from(Self::NEG_E_NORMAL_MIN))
                .min(&FpVar::constant(F::from(shift_max as u128)), E + 1)?
                .max(&FpVar::zero(), E + 1)?,
            shift_max,
            &remainder.is_zero()?,
        )?;

        let (mantissa, exponent, is_abnormal) =
            Self::fix_overflow(&mantissa, &exponent, &x.is_abnormal.or(&y_is_zero)?)?;

        let mantissa = x_is_zero
            .or(&y.is_abnormal)?
            .select(&FpVar::zero(), &mantissa)?;

        let mantissa_is_zero = mantissa.is_zero()?;
        let exponent = mantissa_is_zero
            .and(&is_abnormal.not())?
            .select(&FpVar::constant(-F::from(Self::NEG_E_MIN)), &exponent)?;

        Ok(Self {
            sign,
            exponent,
            mantissa,
            is_abnormal,
        })
    }

    pub fn sqrt(x: &Self) -> Result<Self, SynthesisError> {
        let e_lsb = Boolean::new_hint(x.exponent.cs(), || {
            x.exponent.value().map(|v| {
                (v + F::from(Self::NEG_E_MIN.next_multiple_of(2)))
                    .into_bigint()
                    .is_odd()
            })
        })?;
        let exponent =
            (&x.exponent - FpVar::from(e_lsb.clone())) * FpVar::one().double()?.inverse()?;
        let _ = exponent.abs(E - 1)?;

        let mantissa_bit_length = M + 3;
        let m = &x.mantissa * F::from(1u128 << (mantissa_bit_length * 2 - (M + 2)));
        let m = e_lsb.select(&m.double()?, &m)?;
        let (n, shift, two_to_shift) = {
            let cs = m.cs();
            let m: BigUint = m.value().unwrap_or_default().into();
            let n = F::from(m.sqrt());
            let bits = n.into_bigint().to_bits_le();

            let shift = bits[..mantissa_bit_length]
                .iter()
                .rev()
                .position(|&i| i)
                .unwrap_or(mantissa_bit_length);
            (
                FpVar::new_hint(cs.clone(), || Ok(n))?,
                FpVar::new_hint(cs.clone(), || Ok(F::from(shift as u128)))?,
                FpVar::new_hint(cs.clone(), || Ok(F::from(1u128 << shift)))?,
            )
        };
        // TODO: enforce range of shift [0, mantissa_bit_length]
        // TODO: enforce (shift, two_to_shift) is in lookup table
        let r = m - n.square()?;
        r.enforce_bit_length(mantissa_bit_length + 1)?; // n^2 <= m  =>  m - n^2 >= 0
        (n.double()? - &r).enforce_bit_length(mantissa_bit_length + 1)?; // (n + 1)^2 > m  =>  n^2 + 2n + 1 - m > 0  =>  n^2 + 2n - m >= 0
        let n_is_zero = n.is_zero()?;
        let n = n * two_to_shift;
        (&n - FpVar::from(n_is_zero.not()) * F::from(1u128 << (mantissa_bit_length - 1)))
            .enforce_bit_length(mantissa_bit_length - 1)?;
        let exponent = n_is_zero.select(
            &FpVar::constant(-F::from(Self::NEG_E_MIN)),
            &(exponent - shift),
        )?;

        let mantissa = Self::round(&n, mantissa_bit_length, &FpVar::zero(), 0, &r.is_zero()?)?;

        let is_abnormal = x.sign.and(&n_is_zero.not())?.or(&x.is_abnormal)?;

        Ok(Self {
            sign: x.sign.clone(), // sqrt(-0.0) = -0.0
            exponent: is_abnormal.select(&FpVar::constant(F::from(Self::E_MAX)), &exponent)?,
            mantissa: x.sign.select(&FpVar::zero(), &mantissa)?,
            is_abnormal,
        })
    }

    fn less(x: &Self, y: &Self, allow_eq: bool) -> Result<Boolean<F>, SynthesisError> {
        let xe_ge_ye = (&x.exponent - &y.exponent).is_positive(E + 1)?;
        let xm_ge_ym = (&x.mantissa - &y.mantissa).is_positive(M + 1)?;

        x.is_abnormal
            .and(&x.mantissa.is_zero()?)?
            .or(&y.is_abnormal.and(&y.mantissa.is_zero()?)?)?
            .select(
                &Boolean::FALSE,
                &x.sign.is_eq(&y.sign)?.select(
                    &x.exponent.is_eq(&y.exponent)?.select(
                        &x.mantissa.is_eq(&y.mantissa)?.select(
                            &Boolean::constant(allow_eq),
                            &x.sign.select(&xm_ge_ym, &xm_ge_ym.not())?,
                        )?,
                        &x.sign.select(&xe_ge_ye, &xe_ge_ye.not())?,
                    )?,
                    &(&x.mantissa + &y.mantissa)
                        .is_zero()?
                        .select(&Boolean::constant(allow_eq), &x.sign)?,
                )?,
            )

        /*
         * Equivalent to:
         * ```
         * if x.sign == y.sign {
         *     if x.exponent == y.exponent {
         *         if x.mantissa == y.mantissa {
         *             return allow_eq;
         *         } else {
         *             if x.sign {
         *                 return x.mantissa > y.mantissa;
         *             } else {
         *                 return x.mantissa < y.mantissa;
         *             }
         *         }
         *     } else {
         *         if x.sign {
         *             return x.exponent > y.exponent;
         *         } else {
         *             return x.exponent < y.exponent;
         *         }
         *     }
         * } else {
         *     if x.mantissa + y.mantissa == 0 {
         *         return allow_eq;
         *     } else {
         *         return x.sign;
         *     }
         * }
         * ```
         */
    }

    pub fn is_lt(x: &Self, y: &Self) -> Result<Boolean<F>, SynthesisError> {
        Self::less(x, y, false)
    }

    pub fn is_le(x: &Self, y: &Self) -> Result<Boolean<F>, SynthesisError> {
        Self::less(x, y, true)
    }

    pub fn is_gt(x: &Self, y: &Self) -> Result<Boolean<F>, SynthesisError> {
        Self::less(y, x, false)
    }

    pub fn is_ge(x: &Self, y: &Self) -> Result<Boolean<F>, SynthesisError> {
        Self::less(y, x, true)
    }

    pub fn trunc(x: &Self) -> Result<Self, SynthesisError> {
        let e_ge_0 = x.exponent.is_positive(E)?;
        let e = e_ge_0.select(&x.exponent, &FpVar::one().negate()?)?;
        let f = (e.negate()? + F::from(M as u128)).max(&FpVar::zero(), E)?;
        let two_to_f = FpVar::new_hint(f.cs(), || {
            f.value().map(|f| F::from(2u8).pow(f.into_bigint()))
        })?;
        // TODO: enforce (f, two_to_f) is in lookup table [0, >=M + 1]
        let m = (&x.mantissa * F::from(1u128 << (M + 1))).mul_by_inverse_unchecked(&two_to_f)?;
        let q = {
            let cs = m.cs();
            let m: BigUint = m.value().unwrap_or_default().into();
            FpVar::new_hint(cs.clone(), || Ok(F::from(m >> (M + 1))))?
        };
        q.enforce_bit_length(M + 1)?;
        (m - &q * F::from(1u128 << (M + 1))).enforce_bit_length(M + 1)?;

        Ok(Self {
            sign: x.sign.clone(),
            exponent: e_ge_0.select(&x.exponent, &FpVar::constant(-F::from(Self::NEG_E_MIN)))?,
            mantissa: q * &two_to_f,
            is_abnormal: x.is_abnormal.clone(),
        })
    }

    pub fn floor(x: &Self) -> Result<Self, SynthesisError> {
        let e_ge_0 = x.exponent.is_positive(E)?;
        let e = e_ge_0.select(&x.exponent, &FpVar::one().negate()?)?;
        let f = (e.negate()? + F::from(M as u128)).max(&FpVar::zero(), E)?;
        let two_to_f = FpVar::new_hint(f.cs(), || {
            f.value().map(|f| F::from(2u8).pow(f.into_bigint()))
        })?;
        // TODO: enforce (f, two_to_f) is in lookup table [0, >=M + 1]
        let m = (&x.mantissa * F::from(1u128 << (M + 1))).mul_by_inverse_unchecked(&two_to_f)?;
        let q = {
            let cs = m.cs().or(x.sign.cs());
            let m: BigUint = m.value().unwrap_or_default().into();
            let s = x.sign.value().unwrap();
            FpVar::new_hint(cs.clone(), || {
                Ok(F::from(if s {
                    m.div_ceil(&(BigUint::one() << (M + 1)))
                } else {
                    m >> (M + 1)
                }))
            })?
        };
        q.enforce_bit_length(M + 1)?;
        x.sign
            .select(
                &(&q * F::from(1u128 << (M + 1)) - &m),
                &(&m - &q * F::from(1u128 << (M + 1))),
            )?
            .enforce_bit_length(M + 1)?;

        let n = q * &two_to_f;
        let (n, e) = {
            let mantissa_overflow = n.is_eq(&FpVar::Constant(F::from(1u128 << (M + 1))))?;

            Ok((
                mantissa_overflow.select(&FpVar::constant(F::from(1u128 << M)), &n)?,
                e + FpVar::from(mantissa_overflow),
            ))
        }?;

        Ok(Self {
            sign: x.sign.clone(),
            exponent: n
                .is_zero()?
                .and(&x.is_abnormal.not())?
                .select(&FpVar::constant(-F::from(Self::NEG_E_MIN)), &e)?,
            mantissa: n,
            is_abnormal: x.is_abnormal.clone(),
        })
    }

    pub fn ceil(x: &Self) -> Result<Self, SynthesisError> {
        Ok(Self::floor(&x.neg())?.neg())
    }
}
