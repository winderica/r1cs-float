use std::{
    borrow::Borrow,
    fmt::{Display, Formatter},
    ops::Neg,
};

use crate::{
    impl_ops,
    r1cs::{ConstraintSystemRef, Namespace, SynthesisError},
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
use num::{traits::float::FloatCore, BigUint, Integer, ToPrimitive};

#[derive(Clone)]
/// `FloatVar` represents a IEEE-754 floating point number in the constraint system,
/// where the number is encoded as a 1-bit sign, an `E`-bit exponent, and an `M`-bit mantissa.
/// In the circuit, we don't store the encoded form, but directly record all the components,
/// together with a flag indicating whether the number is abnormal (NaN or infinity).
pub struct FloatVar<F: PrimeField, const E: usize, const M: usize> {
    /// `sign` is `Boolean::TRUE` if and only if the number is negative.
    pub sign: Boolean<F>,
    /// `exponent` is the unbiased exponent of the number.
    /// The biased exponent is in the range `[0, 2^E - 1]`, and the unbiased exponent should be
    /// in the range `[-2^(E - 1) + 1, 2^(E - 1)]`.
    /// However, to save constraints in subsequent operations, we shift the mantissa of a
    /// subnormal number to the left so that the most significant bit of the mantissa is 1,
    /// and the exponent is decremented accordingly.
    /// Therefore, the minimum exponent is actually `-2^(E - 1) + 1 - M`, and our exponent
    /// is in the range `[-2^(E - 1) + 1 - M, 2^(E - 1)]`.
    pub exponent: FpVar<F>,
    /// `mantissa` is the mantissa of the number with explicit leading 1, and hence is either
    /// 0 or in the range `[2^M, 2^(M + 1) - 1]`.
    /// This is true even for subnormal numbers, where the mantissa is shifted to the left
    /// to make the most significant bit 1.
    /// To save constraints when handling NaN, we set the mantissa of NaN to 0.
    pub mantissa: FpVar<F>,
    /// `is_abnormal` is `Boolean::TRUE` if and only if the number is NaN or infinity.
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
                _ => panic!("Unsupported float length"),
            }
        }
    }
}

impl<F: PrimeField, U: FloatCore, const E: usize, const M: usize> AllocVar<U, F>
    for FloatVar<F, E, M>
{
    /// Allocate a variable in the constraint system from a value.
    /// This function decomposes the value into sign, exponent, and mantissa,
    /// and enforces they are well-formed.
    fn new_variable<T: Borrow<U>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();

        // Extract sign, exponent, and mantissa from the value
        let (sign, exponent, mantissa) = {
            let (m, e, s) = f()?.borrow().integer_decode();

            let s = s == -1;
            let e = (e + ((1 << (E - 1)) - 1 + M) as i16) as u128;
            let m = if e == 0 { m >> 1 } else { m - (1 << M) } as u128;

            (
                Boolean::new_variable(cs.clone(), || Ok(s), mode)?,
                FpVar::new_variable(cs.clone(), || Ok(F::from(e)), mode)?,
                FpVar::new_variable(cs.clone(), || Ok(F::from(m)), mode)?,
            )
        };
        // Enforce the bit length of exponent and mantissa
        exponent.enforce_bit_length(E)?;
        mantissa.enforce_bit_length(M)?;

        let exponent_min = -F::from(((1 << (E - 1)) - 1) as u128);
        let exponent_max = F::from((1 << (E - 1)) as u128);

        // Compute the unbiased exponent
        let exponent = exponent + exponent_min;

        let mantissa_is_zero = mantissa.is_zero()?;
        let exponent_is_min = exponent.is_eq(&FpVar::constant(exponent_min))?;
        let exponent_is_max = exponent.is_eq(&FpVar::constant(exponent_max))?;

        // Find how many bits to shift the mantissa to the left to have the `(M - 1)`-th bit equal to 1
        // and prodive it as a hint to the circuit
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
        // TODO: enforce `(l, two_to_l)` is in lookup table `[0, M]`

        // Compute the shifted mantissa. Multiplication here is safe because we already know that
        // mantissa is less than `2^M`, and `2^l` is less than or equal to `2^M`. If `M` is not too large,
        // overflow should not happen.
        let shifted_mantissa = &mantissa * &two_to_l;
        // Enforce the shifted mantissa, after removing the leading bit, has only `M - 1` bits,
        // where the leading bit is set to 0 if the mantissa is zero, and set to 1 otherwise.
        // This does not bound the value of `l` if the mantissa is zero, but it is fine since
        // `l` is not used in this case.
        // On the other hand, if the mantissa is not zero, then this implies that:
        // 1. `l` is indeed the left shift count that makes the `(M - 1)`-th bit 1, since otherwise,
        // `shifted_mantissa - F::from(1u128 << (M - 1))` will underflow to a negative number, which
        // takes `F::MODULUS_BIT_SIZE > M - 1` bits to represent.
        // 2. `shifted_mantissa` is less than `2^M`, since otherwise,
        // `shifted_mantissa - F::from(1u128 << (M - 1))` will be greater than `2^(M - 1) - 1`, which
        // takes at least `M` bits to represent.
        (&shifted_mantissa - FpVar::from(mantissa_is_zero.not()) * F::from(1u128 << (M - 1)))
            .enforce_bit_length(M - 1)?;

        let exponent = exponent_is_min.select(
            &(&exponent - l), // If subnormal, decrement the exponent by `l`
            &exponent,        // Otherwise, keep the exponent unchanged
        )?;
        let mantissa = exponent_is_min.select(
            &shifted_mantissa.double()?, // If subnormal, shift the mantissa to the left by 1 to make its `M`-th bit 1
            &exponent_is_max.and(&mantissa_is_zero.not())?.select(
                &FpVar::zero(),                     // If NaN, set the mantissa to 0
                &(&mantissa + F::from(1u128 << M)), // Otherwise, add `2^M` to the mantissa to make its `M`-th bit 1
            )?,
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

    /// Get the value of the variable.
    /// Since `f32/f64` in rust does not implement `Eq`, which is required by `Self::Value`,
    /// we use `BigUint` instead of `f32/f64` to represent the value in binary form.
    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let s = BigUint::from(self.sign.value()? as u128);
        let e: BigUint =
            (self.exponent.value()? + F::from(((1 << (E - 1)) - 1 + M) as u128)).into();
        let m: BigUint = self.mantissa.value()?.into();
        let is_abnormal = self.is_abnormal.value()?;

        if e <= BigUint::from(M) {
            assert!(!is_abnormal);
            assert_eq!(e.is_zero(), m.is_zero());
            let delta = M + 1 - e.to_usize().unwrap();
            assert_eq!((&m >> delta) << delta, m);
            return Ok((s << (M + E)) + (m >> delta));
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

    /// Negate the number by flipping the sign.
    fn neg(&self) -> Self {
        Self {
            sign: self.sign.not(),
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
            is_abnormal: self.is_abnormal.clone(),
        }
    }

    /// Compute the absolute value of the number by setting the sign to `Boolean::FALSE`.
    pub fn abs(&self) -> Self {
        Self {
            sign: Boolean::FALSE,
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
            is_abnormal: self.is_abnormal.clone(),
        }
    }

    /// Round the mantissa.
    /// Note that the precision for subnormal numbers should be smaller than normal numbers, but in
    /// our representation, the mantissa of subnormal numbers also has `M + 1` bits, and we have to set
    /// the lower bits of the mantissa to 0 to reduce the precision and make the behavior consistent
    /// with the specification.
    /// For this purpose, we use `shift` to specify how many bits in the mantissa should be set to 0.
    /// If the number is normal or we are confident that the lower bits are already 0, we can set
    /// `shift` to 0.
    /// `max_shift` is the maximum value of `shift` that we allow, and a precise upper bound will help
    /// reduce the number of constraints.
    /// `half_flag` is a flag that indicates whether we should determine the rounding direction according
    /// to the equality between the remainder and 1/2.
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
        // TODO: enforce `(u, two_to_u)` is in lookup table `[0, u_max]`

        let r_idx = shift_max + mantissa_bit_length - M - 2;
        let q_idx = r_idx + 1;
        let p_idx = q_idx + 1;
        let p_len = M;
        let s_len = r_idx;

        // Rewrite the shifted mantissa as `p || q || r || s` (big-endian), where
        // * `p` has `M` bits
        // * `q` and `r` have 1 bit each
        // * `s` has the remaining bits
        // and prodive `p, q, r, s` as hints to the circuit.
        // Instead of right shifting the mantissa by `shift` bits, we left shift the mantissa by
        // `shift_max - shift` bits.
        // In the first case, we need to check `s` has `mantissa_bit_length - M - 2` bits, and the shifted
        // out part (we call it `t`) is greater than or equal to 0 and less than `2^shift`, where the latter
        // is equivalent to checking both `t` and `2^shift - t - 1` have `shift_max` bits.
        // However, in the second case, we only need to check `s` has `shift_max + mantissa_bit_length - M - 2`
        // bits, which costs less than the first case.
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
        // Enforce the bit length of `p` and `s`
        p.enforce_bit_length(p_len)?;
        s.enforce_bit_length(s_len)?;

        // Concatenate `p || q`, `r || s`, and `p || q || r || s`.
        // `p || q` is what we want, i.e., the final mantissa, and `r || s` will be thrown away.
        let pq = p.double()? + FpVar::from(q.clone());
        let rs = FpVar::from(r.clone()) * F::from(1u128 << r_idx) + &s;
        let pqrs = &pq * F::from(1u128 << q_idx) + &rs;

        // Enforce that `(p || q || r || s) << shift` is equal to `mantissa << shift_max`
        // Multiplication here is safe because `p || q || r || s` has `shift_max + mantissa_bit_length` bits,
        // and `2^shift` has at most `shift_max` bits, hence the product has `2 * shift_max + mantissa_bit_length`
        // bits, which (at least for f32 and f64) is less than `F::MODULUS_BIT_SIZE` and will not overflow.
        // This constraint guarantees that `p || q || r || s` is indeed `mantissa << (shift_max - shift)`.
        pqrs.mul_equals(&two_to_shift, &(mantissa * F::from(1u128 << shift_max)))?;

        // Determine whether `r == 1` and `s == 0`. If so, we need to round the mantissa according to `q`,
        // and otherwise, we need to round the mantissa according to `r`.
        // Also, we use `half_flag` to allow the caller to specify the rounding direction.
        let is_half = rs
            .is_eq(&FpVar::constant(F::from(1u128 << r_idx)))?
            .and(half_flag)?;
        let carry = FpVar::from(is_half.select(&q, &r)?);

        // Round the mantissa according to `carry` and shift it back to the original position.
        Ok((pq + carry) * &two_to_shift)
    }

    /// Fix mantissa and exponent overflow.
    fn fix_overflow(
        mantissa: &FpVar<F>,
        mantissa_is_zero: &Boolean<F>,
        exponent: &FpVar<F>,
        input_is_abnormal: &Boolean<F>,
    ) -> Result<(FpVar<F>, FpVar<F>, Boolean<F>), SynthesisError> {
        let exponent_max = F::from(Self::E_MAX);
        let exponent_min = -F::from(Self::NEG_E_MIN);

        // Check if mantissa overflows
        // Since the mantissa without carry is always smaller than `2^(M + 1)`, overflow only happens
        // when the original mantissa is `2^(M + 1) - 1` and the carry is 1. Therefore, the only possible
        // value of mantissa in this case is `2^(M + 1)`.
        let mantissa_overflow = mantissa.is_eq(&FpVar::Constant(F::from(1u128 << (M + 1))))?;
        // If mantissa overflows, we need to increment the exponent
        let exponent = exponent + FpVar::from(mantissa_overflow.clone());
        // Check if exponent overflows. If so, the result is abnormal.
        // Also, if the input is already abnormal, the result is of course abnormal.
        let is_abnormal = (&exponent - FpVar::constant(exponent_max))
            .is_positive(E + 1)?
            .or(&input_is_abnormal)?;

        Ok((
            // If mantissa overflows, we right shift the mantissa by 1 and obtain `2^M`.
            // If the result is abnormal, we set the mantissa to infinity's mantissa.
            // We can combine both cases as inifinity's mantissa is `2^M`.
            // We will adjust the mantissa latter if the result is NaN.
            mantissa_overflow
                .or(&is_abnormal)?
                .select(&FpVar::constant(F::from(1u128 << M)), &mantissa)?,
            is_abnormal.select(
                // If the result is abnormal, we set the exponent to infinity/NaN's exponent.
                &FpVar::constant(exponent_max),
                &mantissa_is_zero.select(
                    // If the result is 0, we set the exponent to 0's exponent.
                    &FpVar::constant(exponent_min),
                    // Otherwise, return the original exponent.
                    &exponent,
                )?,
            )?,
            is_abnormal,
        ))
    }

    /// Add two numbers.
    fn add(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        // Compute `y.exponent - x.exponent`'s absolute value and sign.
        // Since `delta` is the absolute value, `delta >= 0`.
        let (delta, ex_le_ey) = (&y.exponent - &x.exponent).abs(E + 1)?;

        // The exponent of the result is at most `max(x.exponent, y.exponent) + 1`, where 1 is the possible carry.
        let exponent = ex_le_ey.select(&y.exponent, &x.exponent)? + FpVar::one();
        // Then we are going to use `delta` to align the mantissas of `x` and `y`.
        // If `delta` is 0, we don't need to shift the mantissas.
        // Otherwise, we need to shift the mantissa of the number with smaller exponent to the right by `delta` bits.
        // Now we check if `delta >= M + 3`, i.e., if the difference is too large.
        // If so, the mantissa of the number with smaller exponent will be completely shifted out, and hence the
        // effect of shifting by `delta` bits is the same as shifting by `M + 3` bits.
        // Therefore, the actual right shift count is `min(delta, M + 3)`.
        // As discussed in `Self::round`, we can shift left by `M + 3 - min(delta, M + 3) = max(M + 3 - delta, 0)`
        // bits instead of shifting right by `min(delta, M + 3)` bits in order to save constraints.
        let delta = (delta.negate()? + F::from((M + 3) as u128)).max(&FpVar::zero(), E)?;
        let two_to_delta = FpVar::new_hint(delta.cs(), || {
            delta
                .value()
                .map(|delta| F::from(2u8).pow(delta.into_bigint()))
        })?;
        // TODO: enforce `(delta, two_to_delta)` is in lookup table `[0, >=M + 3]`

        // Compute the signed mantissas
        let xx = x.sign.select(&x.mantissa.negate()?, &x.mantissa)?;
        let yy = y.sign.select(&y.mantissa.negate()?, &y.mantissa)?;
        // `zz` is the mantissa of the number with smaller exponent, and `ww` is the mantissa of another number.
        let zz = ex_le_ey.select(&xx, &yy)?;
        let ww = &xx + &yy - &zz;

        // Align `zz` and `ww`.
        // Naively, we can shift `zz` to the right by `delta` bits and keep `ww` unchanged.
        // However, as mentioned above, we left shift `zz` by `M + 3 - min(delta, M + 3)` bits and `ww` by `M + 3`
        // bits instead for circuit efficiency.
        // Also, note that if `exponent` is subnormal and w.l.o.g. `x.exponent < y.exponent`, then `zz` has
        // `E_NORMAL_MIN - x.exponent` trailing 0s, and `ww` has `E_NORMAL_MIN - y.exponent` trailing 0s.
        // Hence, `zz * 2^delta` has `E_NORMAL_MIN - x.exponent + M + 3 - y.exponent + x.exponent` trailing 0s,
        // and `ww << (M + 3)` has `E_NORMAL_MIN - y.exponent + M + 3` trailing 0s.
        // This implies that `s` also has `E_NORMAL_MIN - y.exponent + M + 3` trailing 0s.
        // Generally, `s` should have `max(E_NORMAL_MIN - max(x.exponent, y.exponent), 0) + M + 3` trailing 0s.
        let s = zz * two_to_delta + ww * F::from(1u128 << (M + 3));
        // The shift count is at most `M + 3`, and both `zz` and `ww` have `M + 1` bits, hence the result has at most
        // `(M + 3) + (M + 1) + 1` bits, where 1 is the possible carry.
        let mantissa_bit_length = (M + 3) + (M + 1) + 1;

        // Get the sign of the mantissa and find how many bits to shift the mantissa to the left to have the
        // `mantissa_bit_length - 1`-th bit equal to 1.
        // Prodive these values as hints to the circuit.
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
        // TODO: enforce range of shift `[0, M + 4]`
        // TODO: enforce `(shift, two_to_shift)` is in lookup table

        // Compute the shifted absolute value of mantissa
        let mantissa = mantissa_ge_0.select(&s, &s.negate()?)? * two_to_shift;
        let mantissa_is_zero = mantissa.is_zero()?;
        // Enforce that the MSB of the shifted absolute value of mantissa is 1 unless the mantissa is zero.
        // Soundness holds because
        // * `mantissa` is non-negative. Otherwise, `mantissa - !mantissa_is_zero << (mantissa_bit_length - 1)`
        // will be negative and cannot fit in `mantissa_bit_length - 1` bits.
        // * `mantissa` has at most `mantissa_bit_length` bits. Otherwise,
        // `mantissa - !mantissa_is_zero << (mantissa_bit_length - 1)` will be greater than or equal to
        // `2^(mantissa_bit_length - 1)` and cannot fit in `mantissa_bit_length - 1` bits.
        // * `mantissa`'s MSB is 1 unless `mantissa_is_zero`. Otherwise, `mantissa - 1 << (mantissa_bit_length - 1)`
        // will be negative and cannot fit in `mantissa_bit_length - 1` bits.
        (&mantissa
            - FpVar::from(mantissa_is_zero.not()) * F::from(1u128 << (mantissa_bit_length - 1)))
        .enforce_bit_length(mantissa_bit_length - 1)?;
        // Decrement the exponent by `shift`.
        let exponent = exponent - shift;

        // `mantissa_ge_0` can be directly used to determine the sign of the result, except for the case
        // `-0 + -0`. Therefore, we first check whether the signs of `x` and `y` are the same. If so,
        // we use `x`'s sign as the sign of the result. Otherwise, we use the negation of `mantissa_ge_0`.
        let sign = x
            .sign
            .is_eq(&y.sign)?
            .select(&x.sign, &mantissa_ge_0.not())?;

        let mantissa = Self::round(
            &mantissa,
            mantissa_bit_length,
            // If the result is subnormal, we need to clear the lowest `E_NORMAL_MIN - exponent` bits of rounded
            // mantissa. However, as we are going to show below, the required bits are already 0.
            // Note that `mantissa` is the product of `s` and `2^shift`, where `2^shift` has `shift` trailing 0s,
            // `s` has `E_NORMAL_MIN - max(x.exponent, y.exponent) + M + 3` trailing 0s.
            // In summary, `mantissa` has `E_NORMAL_MIN - max(x.exponent, y.exponent) + M + 3 + shift` trailing 0s
            // and `(M + 3) + (M + 1) + 1` bits in total.
            // After rounding, we choose the `M + 1` MSBs as the rounded mantissa, which should contain at least
            // `E_NORMAL_MIN - max(x.exponent, y.exponent) + shift - 1` trailing 0s.
            // Since `exponent == max(x.exponent, y.exponent) + 1 - shift`, the lowest `E_NORMAL_MIN - exponent`
            // bits of the rounded mantissa should be 0.
            &FpVar::zero(),
            0,
            &Boolean::TRUE,
        )?;

        let (mantissa, exponent, is_abnormal) = Self::fix_overflow(
            &mantissa,
            &mantissa_is_zero,
            &exponent,
            &x.is_abnormal.or(&y.is_abnormal)?,
        )?;

        Ok(Self {
            sign,
            exponent,
            // Rule of addition:
            // |       | +Inf | -Inf | NaN | other |
            // |-------|------|------|-----|-------|
            // | +Inf  | +Inf |   0  | NaN | +Inf  |
            // | -Inf  |   0  | -Inf | NaN | -Inf  |
            // | NaN   |  NaN |  NaN | NaN |  NaN  |
            // | other | +Inf | -Inf | NaN |       |
            mantissa: x.is_abnormal.select(
                // If `x` is abnormal ...
                &y.is_abnormal.not().or(&xx.is_eq(&yy)?)?.select(
                    // If `y` is not abnormal, then the result is `x`.
                    // If `x`'s signed mantissa is equal to `y`'s, then the result is also `x`.
                    &x.mantissa,
                    // Otherwise, the result is 0 or NaN, whose mantissa is 0.
                    &FpVar::zero(),
                )?,
                // If `x` is not abnormal ...
                &y.is_abnormal.select(
                    // If `y` is abnormal, then the result is `y`.
                    &y.mantissa,
                    // Otherwise, the result is our computed mantissa.
                    &mantissa,
                )?,
            )?,
            is_abnormal,
        })
    }

    /// Multiply two numbers.
    fn mul(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        // The result is negative if and only if the signs of x and y are different.
        let sign = x.sign.xor(&y.sign)?;

        let mantissa = &x.mantissa * &y.mantissa;
        // Since both `x.mantissa` and `y.mantissa` are in the range [2^M, 2^(M + 1)), the product is
        // in the range [2^(2M), 2^(2M + 2)) and requires 2M + 2 bits to represent.
        let mantissa_bit_length = (M + 1) * 2;

        // Get the MSB of the mantissa and provide it as a hint to the circuit.
        let mantissa_msb = Boolean::new_hint(mantissa.cs(), || {
            mantissa
                .value()
                .map(|v| v.into_bigint().get_bit(mantissa_bit_length - 1))
        })?;
        // Enforce that `mantissa_msb` is indeed the MSB of the mantissa.
        // Soundness holds because
        // * If `mantissa_msb == 0` but the actual MSB is 1, then the subtraction result will have at least
        // mantissa_bit_length bits.
        // * If `mantissa_msb == 1` but the actual MSB is 0, then the subtraction will underflow to a negative
        // value.
        (&mantissa
            - FpVar::from(mantissa_msb.clone()) * F::from(1u128 << (mantissa_bit_length - 1)))
        .enforce_bit_length(mantissa_bit_length - 1)?;
        // Shift the mantissa to the left to make the MSB 1.
        // Since `mantissa` is in the range `[2^(2M), 2^(2M + 2))`, either the MSB is 1 or the second MSB is 1.
        // Therefore, we can simply double the mantissa if the MSB is 0.
        let mantissa = &mantissa + mantissa_msb.select(&FpVar::zero(), &mantissa)?;
        // Compute the exponent of the result. We should increment the exponent if the multiplication
        // carries, i.e., if the MSB of the mantissa is 1.
        let exponent = &x.exponent + &y.exponent + FpVar::from(mantissa_msb);

        let shift_max = M + 2;
        let mantissa = Self::round(
            &mantissa,
            mantissa_bit_length,
            // If `exponent >= E_NORMAL_MIN`, i.e., the result is normal, we don't need to clear the lower bits.
            // Otherwise, we need to clear `min(E_NORMAL_MIN - exponent, shift_max)` bits of the rounded mantissa.
            &(exponent.negate()? - F::from(Self::NEG_E_NORMAL_MIN))
                .min(&FpVar::constant(F::from(shift_max as u128)), E + 1)?
                .max(&FpVar::zero(), E + 1)?,
            shift_max,
            &Boolean::TRUE,
        )?;

        let mantissa_is_zero = mantissa.is_zero()?;

        let (mantissa, exponent, is_abnormal) = Self::fix_overflow(
            &mantissa,
            &mantissa_is_zero,
            &exponent,
            &x.is_abnormal.or(&y.is_abnormal)?,
        )?;

        Ok(Self {
            sign,
            exponent,
            // If the mantissa before fixing overflow is zero, we reset the final mantissa to 0,
            // as `Self::fix_overflow` incorrectly sets NaN's mantissa to infinity's mantissa.
            mantissa: mantissa_is_zero.select(&FpVar::zero(), &mantissa)?,
            is_abnormal,
        })
    }

    /// Divide two numbers.
    fn div(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        // The result is negative if and only if the signs of `x` and `y` are different.
        let sign = x.sign.xor(&y.sign)?;

        let y_is_zero = y.mantissa.is_zero()?;

        // If the divisor is 0, we increase it to `2^M`, because we cannot represent an infinite value in circuit.
        let y_mantissa = y_is_zero.select(&FpVar::constant(F::from(1u128 << M)), &y.mantissa)?;

        // The result's mantissa is the quotient of `x.mantissa << (M + 2)` and `y_mantissa`.
        // Since both `x.mantissa` and `y_mantissa` are in the range `[2^M, 2^(M + 1))`, the quotient is in the range
        // `(2^(M + 1), 2^(M + 3))` and requires `M + 3` bits to represent.
        let mantissa_bit_length = (M + 2) + 1;
        // Compute `(x.mantissa << (M + 2)) / y_mantissa` and get the MSB of the quotient.
        // Provide the quotient and the MSB as hints to the circuit.
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
        // Compute the remainder `(x.mantissa << (M + 2)) % y_mantissa`.
        let remainder = &x.mantissa * F::from(1u128 << (M + 2)) - &mantissa * &y_mantissa;
        // Enforce that `0 <= remainder < y_mantissa`.
        remainder.enforce_bit_length(M + 1)?;
        (&y_mantissa - &remainder - FpVar::one()).enforce_bit_length(M + 1)?;
        // Enforce that `mantissa_msb` is indeed the MSB of the mantissa.
        // Soundness holds because
        // * If `mantissa_msb == 0` but the actual MSB is 1, then the subtraction result will have at least
        // mantissa_bit_length bits.
        // * If `mantissa_msb == 1` but the actual MSB is 0, then the subtraction will underflow to a negative
        // value.
        (&mantissa
            - FpVar::from(mantissa_msb.clone()) * F::from(1u128 << (mantissa_bit_length - 1)))
        .enforce_bit_length(mantissa_bit_length - 1)?;

        // Since `mantissa` is in the range `[2^(2M), 2^(2M + 2))`, either the MSB is 1 or the second MSB is 1.
        // Therefore, we can simply double the mantissa if the MSB is 0.
        let mantissa = &mantissa + mantissa_msb.select(&FpVar::zero(), &mantissa)?;
        // Compute the exponent of the result. We should decrement the exponent if the division
        // borrows, i.e., if the MSB of the mantissa is 0.
        let exponent = &x.exponent - &y.exponent - FpVar::from(mantissa_msb.not());

        let shift_max = M + 2;
        let mantissa = Self::round(
            &mantissa,
            mantissa_bit_length,
            // If `exponent >= E_NORMAL_MIN`, i.e., the result is normal, we don't need to clear the lower bits.
            // Otherwise, we need to clear `min(E_NORMAL_MIN - exponent, shift_max)` bits of the rounded mantissa.
            &(exponent.negate()? - F::from(Self::NEG_E_NORMAL_MIN))
                .min(&FpVar::constant(F::from(shift_max as u128)), E + 1)?
                .max(&FpVar::zero(), E + 1)?,
            shift_max,
            &remainder.is_zero()?,
        )?;

        // If `y` is infinity, the result is zero.
        // If `y` is NaN, the result is NaN.
        // Since both zero and NaN have mantissa 0, we can combine both cases and set the mantissa to 0
        // when `y` is abnormal.
        let mantissa_is_zero = mantissa.is_zero()?.or(&y.is_abnormal)?;

        let (mantissa, exponent, is_abnormal) = Self::fix_overflow(
            &mantissa,
            &mantissa_is_zero,
            &exponent,
            &x.is_abnormal.or(&y_is_zero)?,
        )?;

        Ok(Self {
            sign,
            exponent,
            // If the mantissa before fixing overflow is zero, we reset the final mantissa to 0,
            // as `Self::fix_overflow` incorrectly sets NaN's mantissa to infinity's mantissa.
            mantissa: mantissa_is_zero.select(&FpVar::zero(), &mantissa)?,
            is_abnormal,
        })
    }

    pub fn sqrt(x: &Self) -> Result<Self, SynthesisError> {
        // Get the LSB of the exponent and provide it as a hint to the circuit.
        let e_lsb = Boolean::new_hint(x.exponent.cs(), || {
            x.exponent.value().map(|v| {
                (v + F::from(Self::NEG_E_MIN.next_multiple_of(&2)))
                    .into_bigint()
                    .is_odd()
            })
        })?;
        // Compute `x.exponent >> 1`
        let exponent =
            (&x.exponent - FpVar::from(e_lsb.clone())) * FpVar::one().double()?.inverse()?;
        // Enforce that `|exponent|` only has `E - 1` bits.
        // This ensures that `e_lsb` is indeed the LSB of the exponent, as otherwise `x.exponent` will be odd,
        // but `x.exponent * 2^(-1)` will not fit in `E - 1` bits for all odd `x.exponent` between `E_MIN` and `E_MAX`.
        let _ = exponent.abs(E - 1)?;

        // TODO: `M + 3` is obtained by empirical analysis. We need to find why it works.
        let mantissa_bit_length = M + 3;
        // We are going to find `n` such that `n^2 <= m < (n + 1)^2`, and `r = m - n^2` decides the rounding direction.
        // To this end, we shift `x.mantissa` to the left to allow a more accurate `r`.
        // TODO: `mantissa_bit_length * 2 - (M + 2)` is obtained by empirical analysis. We need to find why it works.
        let m = &x.mantissa * F::from(1u128 << (mantissa_bit_length * 2 - (M + 2)));
        // `sqrt(2^e * m) == sqrt(2^(e - 1) * 2m)`
        // If `e` is even, then the result is `sqrt(2^e * m) = 2^(e >> 1) * sqrt(m)`.
        // If `e` is odd, then the result is `sqrt(2^(e - 1) * 2m) = 2^(e >> 1) * sqrt(2m)`.
        let m = e_lsb.select(&m.double()?, &m)?;
        // Compute `sqrt(m)` and find how many bits to shift the mantissa to the left to have the
        // `mantissa_bit_length - 1`-th bit equal to 1.
        // Prodive these values as hints to the circuit.
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
        // TODO: enforce range of shift `[0, mantissa_bit_length]`
        // TODO: enforce `(shift, two_to_shift)` is in lookup table

        // Compute the remainder `r = m - n^2`.
        let r = m - n.square()?;
        // Enforce that `n^2 <= m < (n + 1)^2`.
        r.enforce_bit_length(mantissa_bit_length + 1)?; // n^2 <= m  =>  m - n^2 >= 0
        (n.double()? - &r).enforce_bit_length(mantissa_bit_length + 1)?; // (n + 1)^2 > m  =>  n^2 + 2n + 1 - m > 0  =>  n^2 + 2n - m >= 0

        let n_is_zero = n.is_zero()?;
        // Compute the shifted value of `n`
        let n = n * two_to_shift;
        // Enforce that the MSB of the shifted `n` is 1 unless `n` is zero.
        // Soundness holds because
        // * `n` has at most `mantissa_bit_length` bits. Otherwise,
        // `n - !n_is_zero << (mantissa_bit_length - 1)` will be greater than or equal to
        // `2^(mantissa_bit_length - 1)` and cannot fit in `mantissa_bit_length - 1` bits.
        // * `n`'s MSB is 1 unless `n_is_zero`. Otherwise, `n - 1 << (mantissa_bit_length - 1)`
        // will be negative and cannot fit in `mantissa_bit_length - 1` bits.
        (&n - FpVar::from(n_is_zero.not()) * F::from(1u128 << (mantissa_bit_length - 1)))
            .enforce_bit_length(mantissa_bit_length - 1)?;

        // Decrement the exponent by `shift`.
        let exponent = exponent - shift;

        let mantissa = Self::round(
            &n,
            mantissa_bit_length,
            // The result is always normal or 0, as `exponent = (x.exponent >> 1) - shift > E_NORMAL_MIN`.
            // Therefore, we don't need to clear the lower bits.
            &FpVar::zero(),
            0,
            &r.is_zero()?,
        )?;

        // If `x` is negative and `x` is not `-0`, the result is NaN.
        // If `x` is NaN, the result is NaN.
        // If `x` is +infinty, the result is +infinity.
        // Below we combine all these cases.
        let is_abnormal = x.sign.and(&n_is_zero.not())?.or(&x.is_abnormal)?;

        Ok(Self {
            sign: x.sign.clone(), // Edge case: sqrt(-0.0) = -0.0
            exponent: is_abnormal.select(
                // If the result is abnormal, we set the exponent to infinity/NaN's exponent.
                &FpVar::constant(F::from(Self::E_MAX)),
                &n_is_zero.select(
                    // If the result is 0, we set the exponent to 0's exponent.
                    &FpVar::constant(-F::from(Self::NEG_E_MIN)),
                    // Otherwise, return the original exponent.
                    &exponent,
                )?,
            )?,
            mantissa: x.sign.select(
                // If `x` is negative, we set the mantissa to NaN's mantissa.
                &FpVar::zero(),
                &mantissa,
            )?,
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
                // If either `x` or `y` is NaN, the result is always false.
                &Boolean::FALSE,
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
