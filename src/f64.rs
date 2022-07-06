use std::{
    borrow::Borrow,
    fmt::{Debug, Display, Formatter},
    ops::Neg,
};

use ark_ff::{BigInteger, BitIteratorLE, One, PrimeField};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::{fp::FpVar, FieldVar},
    prelude::EqGadget,
    select::CondSelectGadget,
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use num::{BigUint, ToPrimitive};

#[derive(Clone)]
pub struct F64Var<F: PrimeField> {
    pub sign: Boolean<F>,
    pub exponent: FpVar<F>,
    pub mantissa: FpVar<F>,
}

impl<F: PrimeField> Debug for F64Var<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(
                f,
                "Sign: {:?}\nExponent: {:?}\nMantissa: {:?}",
                self.sign, self.exponent, self.mantissa
            )
        } else {
            let s = if self.sign.value().unwrap_or_default() {
                "-"
            } else {
                "+"
            };
            let m: BigUint = self.mantissa.value().unwrap_or_default().into();
            let m = m.to_u64().unwrap();
            let e: BigUint = (self.exponent.value().unwrap_or_default() + F::from(1023u64)).into();
            let e = if m >= 1 << 52 {
                e.to_i64().unwrap() - 1023
            } else {
                0
            };

            write!(f, "Sign: {}\nExponent: {}\nMantissa: {}", s, e, m)
        }
    }
}

impl<F: PrimeField> Display for F64Var<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let v = self.value().unwrap();
        if f.alternate() {
            write!(f, "{:08x}", v)
        } else {
            write!(f, "{}", f64::from_bits(v))
        }
    }
}

impl<F: PrimeField> F64Var<F> {
    pub fn input(i: f64) -> Vec<F> {
        BitIteratorLE::new([i.to_bits()]).map(F::from).collect()
    }
}

impl<F: PrimeField> AllocVar<f64, F> for F64Var<F> {
    fn new_variable<T: Borrow<f64>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();

        let mut bits = BitIteratorLE::new([f()?.borrow().to_bits()])
            .map(|i| Boolean::new_variable(cs.clone(), || Ok(i), mode))
            .collect::<Result<Vec<_>, _>>()?;

        let sign = bits.pop().unwrap();

        let exponent = Boolean::le_bits_to_fp_var(&bits.split_off(52))?;
        // TODO: remove this when ±Infinity and NaNs are supported
        exponent.enforce_not_equal(&FpVar::Constant(F::from(2047u64)))?;

        let is_normal = exponent.is_zero()?.not();
        let exponent = is_normal.select(&exponent, &FpVar::one())? - F::from(1023u64);
        bits.push(is_normal);
        let mantissa = Boolean::le_bits_to_fp_var(&bits)?;

        Ok(Self {
            sign,
            exponent,
            mantissa,
        })
    }
}

impl<F: PrimeField> R1CSVar<F> for F64Var<F> {
    type Value = u64;

    fn cs(&self) -> ConstraintSystemRef<F> {
        unimplemented!("Call `self.sign.cs()`/`self.exponent.cs()`/`self.mantissa.cs()` instead")
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        let s = self.sign.value()? as u64;
        let m: BigUint = self.mantissa.value()?.into();
        let e: BigUint = (self.exponent.value()? + F::from(1023u64)).into();

        let is_normal = m.bit(52);

        let m = m.to_u64().unwrap() & ((1 << 52) - 1);
        let e = if is_normal { e.to_u64().unwrap() } else { 0 };
        Ok((s << 63) + (e << 52) + m)
    }
}

impl<F: PrimeField> CondSelectGadget<F> for F64Var<F> {
    fn conditionally_select(
        cond: &Boolean<F>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            sign: cond.select(&true_value.sign, &false_value.sign)?,
            exponent: cond.select(&true_value.exponent, &false_value.exponent)?,
            mantissa: cond.select(&true_value.mantissa, &false_value.mantissa)?,
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

impl<F: PrimeField> Neg for F64Var<F> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::neg(&self)
    }
}

impl<F: PrimeField> Neg for &F64Var<F> {
    type Output = F64Var<F>;

    fn neg(self) -> Self::Output {
        F64Var::neg(self)
    }
}

impl_ops!(
    F64Var<F>,
    Add,
    add,
    AddAssign,
    add_assign,
    |a, b| { F64Var::add(a, b).unwrap() },
    F: PrimeField,
);

impl_ops!(
    F64Var<F>,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    |a, b: &'a F64Var<F>| { F64Var::add(a, &-b).unwrap() },
    F: PrimeField,
);

impl_ops!(
    F64Var<F>,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    |a, b| { F64Var::mul(a, b).unwrap() },
    F: PrimeField,
);

impl_ops!(
    F64Var<F>,
    Div,
    div,
    DivAssign,
    div_assign,
    |a, b| { F64Var::div(a, b).unwrap() },
    F: PrimeField,
);

impl<F: PrimeField> EqGadget<F> for F64Var<F> {
    fn is_eq(&self, other: &Self) -> Result<Boolean<F>, SynthesisError> {
        Boolean::TRUE
            .and(&self.sign.is_eq(&other.sign)?)?
            .and(&self.exponent.is_eq(&other.exponent)?)?
            .and(&self.mantissa.is_eq(&other.mantissa)?)
    }
}

impl<F: PrimeField> F64Var<F> {
    fn new_bits_variable(
        cs: ConstraintSystemRef<F>,
        bits: &[bool],
        mode: AllocationMode,
    ) -> Result<Vec<Boolean<F>>, SynthesisError> {
        bits.iter()
            .map(|i| Boolean::new_variable(cs.clone(), || Ok(i), mode))
            .collect()
    }

    fn to_bit_array(x: &FpVar<F>, length: usize) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let cs = x.cs();

        let bits = Self::new_bits_variable(
            cs.clone(),
            &x.value().unwrap_or_default().into_repr().to_bits_le()[..length],
            if cs.is_none() {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            },
        )?;

        Boolean::le_bits_to_fp_var(&bits)?.enforce_equal(&x)?;

        Ok(bits)
    }

    fn to_abs_bit_array(
        x: &FpVar<F>,
        length: usize,
    ) -> Result<(Vec<Boolean<F>>, Boolean<F>), SynthesisError> {
        let cs = x.cs();

        let (abs, x_ge_0) = {
            let x = x.value().unwrap_or_default();
            let x_ge_0 = x.into_repr() < F::modulus_minus_one_div_two();

            let abs = if x_ge_0 { x } else { x.neg() };

            let mode = if cs.is_none() {
                AllocationMode::Constant
            } else {
                AllocationMode::Witness
            };
            (
                Self::new_bits_variable(cs.clone(), &abs.into_repr().to_bits_le()[..length], mode)?,
                Boolean::new_variable(cs.clone(), || Ok(x_ge_0), mode)?,
            )
        };

        Boolean::le_bits_to_fp_var(&abs)?.enforce_equal(&x_ge_0.select(x, &x.negate()?)?)?;

        Ok((abs, x_ge_0))
    }

    fn neg(&self) -> Self {
        Self {
            sign: self.sign.not(),
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
        }
    }

    pub fn abs(&self) -> Self {
        Self {
            sign: Boolean::FALSE,
            exponent: self.exponent.clone(),
            mantissa: self.mantissa.clone(),
        }
    }

    fn normalize(
        mantissa: &FpVar<F>,
        mantissa_bit_length: usize,
        exponent: &FpVar<F>,
    ) -> Result<(FpVar<F>, FpVar<F>), SynthesisError> {
        let cs = mantissa.cs();

        let one = FpVar::one();
        let two = one.double()?;
        let min_exponent = FpVar::Constant(-F::from(1022u64));

        let l_bits = {
            let l = mantissa
                .value()
                .unwrap_or_default()
                .into_repr()
                .to_bits_le()[..mantissa_bit_length]
                .iter()
                .rev()
                .position(|&i| i)
                .unwrap_or(0) as u64;

            let l_bit_length = (usize::BITS - mantissa_bit_length.leading_zeros()) as usize;

            Self::new_bits_variable(
                cs.clone(),
                &F::BigInt::from(l).to_bits_le()[..l_bit_length],
                if cs.is_none() {
                    AllocationMode::Constant
                } else {
                    AllocationMode::Witness
                },
            )?
        };
        let l = Boolean::le_bits_to_fp_var(&l_bits)?;

        let is_zero = mantissa.is_zero()?;

        let mantissa_bits =
            Self::to_bit_array(&(mantissa * two.pow_le(&l_bits)?), mantissa_bit_length)?;

        mantissa_bits
            .last()
            .unwrap()
            .or(&is_zero)?
            .enforce_equal(&Boolean::TRUE)?;

        let (m_bits, l_ge_max) = Self::to_abs_bit_array(&(&l - exponent + &min_exponent), 12)?;

        let mantissa = Boolean::le_bits_to_fp_var(&mantissa_bits)?
            * l_ge_max.select(&two.inverse()?.pow_le(&m_bits)?, &FpVar::one())?;

        let exponent = is_zero
            .or(&l_ge_max)?
            .select(&min_exponent, &(exponent - l))?;

        Ok((mantissa, exponent))
    }

    fn round(mantissa: &FpVar<F>, mantissa_bit_length: usize) -> Result<FpVar<F>, SynthesisError> {
        let cs = mantissa.cs();
        let w = mantissa_bit_length - 53;

        let qq = {
            let mut qq = mantissa.value().unwrap_or_default().into_repr();
            qq.divn((w + 1) as u32);

            FpVar::new_variable(
                cs.clone(),
                || Ok(F::from_repr(qq).unwrap()),
                if cs.is_none() {
                    AllocationMode::Constant
                } else {
                    AllocationMode::Witness
                },
            )?
        };

        let rr = mantissa - &qq * F::from(BigUint::one() << (w + 1));
        let rr_bits = Self::to_bit_array(&rr, w + 1)?;

        let q_lsb = FpVar::from(rr_bits[w].clone());
        let r_msb = FpVar::from(rr_bits[w - 1].clone());

        let q = qq.double()? + &q_lsb;
        let r = Boolean::le_bits_to_fp_var(&rr_bits[..w])?;

        let is_half = r.is_eq(&FpVar::Constant(F::from(BigUint::one() << (w - 1))))?;

        let carry = is_half.select(&q_lsb, &r_msb)?;

        Ok(q + carry)
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
        const S_SIZE: usize = 54;
        const R_SIZE: usize = 55;
        let one = FpVar::one();
        let two = FpVar::Constant(F::from(2u64));
        let r_size = FpVar::Constant(F::from(R_SIZE as u64));
        let r_max = FpVar::Constant(F::from(1u128 << R_SIZE));

        let (delta_bits, ex_le_ey) = Self::to_abs_bit_array(&(&y.exponent - &x.exponent), 11)?;

        let exponent = ex_le_ey.select(&y.exponent, &x.exponent)? + &one;

        let (delta_bits, delta_le_w) =
            Self::to_abs_bit_array(&(r_size - Boolean::le_bits_to_fp_var(&delta_bits)?), 11)?;

        let two_to_delta = delta_le_w.select(&two.pow_le(&delta_bits[..6])?, &one)?;

        let xx = x.sign.select(&x.mantissa.negate()?, &x.mantissa)?;
        let yy = y.sign.select(&y.mantissa.negate()?, &y.mantissa)?;
        let zz = ex_le_ey.select(&xx, &yy)?;
        let ww = &xx + &yy - &zz;

        let s = zz * two_to_delta + ww * &r_max;

        let (s_bits, s_ge_0) = Self::to_abs_bit_array(&s, R_SIZE + S_SIZE)?;

        let s = Boolean::le_bits_to_fp_var(&s_bits)?;

        let sign = x.sign.is_eq(&y.sign)?.select(&x.sign, &s_ge_0.not())?;

        let (s, exponent) = Self::normalize(&s, R_SIZE + S_SIZE, &exponent)?;

        let mantissa = Self::round(&s, R_SIZE + S_SIZE)?;

        let (mantissa, exponent) = Self::fix_overflow(&mantissa, &exponent)?;

        Ok(Self {
            sign,
            exponent,
            mantissa,
        })
    }

    fn mul(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        const P_SIZE: usize = 106;
        const R_SIZE: usize = 54;
        let min_exponent = FpVar::Constant(-F::from(1022u64));

        let sign = x.sign.xor(&y.sign)?;

        let p = &x.mantissa * &y.mantissa;

        let exponent = &x.exponent + &y.exponent + F::from((R_SIZE + 1) as u64);

        let (_, e_le_min) = Self::to_abs_bit_array(&(&min_exponent - &exponent), 12)?;
        let exponent = e_le_min.select(&min_exponent, &exponent)?;

        let (p, exponent) = Self::normalize(&p, P_SIZE + R_SIZE, &exponent)?;

        let mantissa = Self::round(&p, P_SIZE + R_SIZE)?;

        let (mantissa, exponent) = Self::fix_overflow(&mantissa, &exponent)?;

        Ok(Self {
            sign,
            exponent,
            mantissa,
        })
    }

    fn div(x: &Self, y: &Self) -> Result<Self, SynthesisError> {
        const Q_SIZE: usize = 159;
        const R_SIZE: usize = 55;
        let min_exponent = FpVar::Constant(-F::from(1022u64));

        let sign = x.sign.xor(&y.sign)?;

        let q = {
            let cs = x.mantissa.cs().or(y.mantissa.cs());
            let x: BigUint = x.mantissa.value().unwrap_or(F::zero()).into();
            let y: BigUint = y.mantissa.value().unwrap_or(F::zero()).into();
            FpVar::new_variable(
                cs.clone(),
                || Ok(F::from((x << Q_SIZE) / y)),
                if cs.is_none() {
                    AllocationMode::Constant
                } else {
                    AllocationMode::Witness
                },
            )?
        };
        let r = &x.mantissa * F::from(BigUint::one() << Q_SIZE) - &q * &y.mantissa;
        Self::to_bit_array(&r, 53)?;
        Self::to_bit_array(&(&y.mantissa - &r - FpVar::one()), 53)?;

        let exponent = &x.exponent - &y.exponent + F::from((R_SIZE - 1) as u64);

        let (_, e_le_min) = Self::to_abs_bit_array(&(&min_exponent - &exponent), 12)?;
        let exponent = e_le_min.select(&min_exponent, &exponent)?;

        let (q, exponent) = Self::normalize(&q, Q_SIZE + R_SIZE, &exponent)?;

        let mantissa = Self::round(&q, Q_SIZE + R_SIZE)?;

        let (mantissa, exponent) = Self::fix_overflow(&mantissa, &exponent)?;

        Ok(Self {
            sign,
            exponent,
            mantissa,
        })
    }

    pub fn sqrt(x: &Self) -> Result<Self, SynthesisError> {
        const L_SIZE: usize = 86;
        const R_SIZE: usize = 54;

        let mut e_bits = Self::to_bit_array(&(&x.exponent + F::from(1024u64)), 11)?;
        let e_lsb = e_bits.remove(0);
        let e = Boolean::le_bits_to_fp_var(&e_bits)? - F::from(512u64);

        let m = &x.mantissa * F::from(BigUint::one() << L_SIZE);
        let m = e_lsb.select(&m.double()?, &m)?;
        let n = {
            let cs = m.cs();
            let m: BigUint = m.value().unwrap_or_default().into();
            FpVar::new_variable(
                cs.clone(),
                || Ok(F::from(m.sqrt())),
                if cs.is_none() {
                    AllocationMode::Constant
                } else {
                    AllocationMode::Witness
                },
            )?
        };
        let nn = n.square()?;
        // n^2 <= m  =>  m - n^2 >= 0
        Self::to_bit_array(&(&m - &nn), L_SIZE + R_SIZE)?;
        // (n + 1)^2 > m  =>  n^2 + 2n + 1 - m > 0  =>  n^2 + 2n - m >= 0
        Self::to_bit_array(&(&nn + n.double()? - &m), L_SIZE + R_SIZE)?;

        let (n, exponent) = Self::normalize(&n, (L_SIZE + R_SIZE) / 2, &e)?;

        let mantissa = Self::round(&n, (L_SIZE + R_SIZE) / 2)?;

        Ok(Self {
            sign: x.sign.clone(),
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
    };

    use ark_bls12_381::Fr;
    use ark_relations::r1cs::ConstraintSystem;
    use rayon::prelude::*;

    use super::*;

    fn num_constraints<F: FnOnce() -> R, R>(cs: &ConstraintSystemRef<Fr>, f: F) -> usize {
        let before = cs.num_constraints();
        f();
        let after = cs.num_constraints();
        after - before
    }

    #[test]
    fn new_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        println!(
            "{}",
            num_constraints(&cs, || F64Var::new_witness(cs.clone(), || Ok(0.1)).unwrap())
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn add_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2))?;

        println!("{}", num_constraints(&cs, || println!("{}", a + b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn sub_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2))?;

        println!("{}", num_constraints(&cs, || println!("{}", a - b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn mul_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2))?;

        println!("{}", num_constraints(&cs, || println!("{}", a * b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn div_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2))?;

        println!("{}", num_constraints(&cs, || println!("{}", a / b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn sqrt_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1))?;

        println!(
            "{}",
            num_constraints(&cs, || println!("{}", F64Var::sqrt(&a).unwrap()))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    fn test_unary_op(
        test_data: File,
        op: fn(F64Var<Fr>) -> F64Var<Fr>,
    ) -> Result<(), Box<dyn Error>> {
        let r = BufReader::new(test_data)
            .lines()
            .collect::<Result<Vec<_>, _>>()?
            .par_iter()
            .map(|line| {
                line.split(' ')
                    .take(2)
                    .map(|i| u64::from_str_radix(i, 16).map(f64::from_bits))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            })
            .filter(|v| v.iter().find(|i| i.is_nan() || i.is_infinite()).is_none())
            .filter(|v| {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = F64Var::new_witness(cs.clone(), || Ok(v[0])).unwrap();
                let b = F64Var::new_witness(cs.clone(), || Ok(v[1])).unwrap();

                F64Var::enforce_equal(&op(a), &b).unwrap();

                !cs.is_satisfied().unwrap()
            })
            .collect::<Vec<_>>();

        assert_eq!(r.len(), 0, "{:#?}", r);

        Ok(())
    }

    fn test_binary_op(
        test_data: File,
        op: fn(F64Var<Fr>, F64Var<Fr>) -> F64Var<Fr>,
    ) -> Result<(), Box<dyn Error>> {
        let r = BufReader::new(test_data)
            .lines()
            .collect::<Result<Vec<_>, _>>()?
            .par_iter()
            .map(|line| {
                line.split(' ')
                    .take(3)
                    .map(|i| u64::from_str_radix(i, 16).map(f64::from_bits))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            })
            .filter(|v| v.iter().find(|i| i.is_nan() || i.is_infinite()).is_none())
            .filter(|v| {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = F64Var::new_witness(cs.clone(), || Ok(v[0])).unwrap();
                let b = F64Var::new_witness(cs.clone(), || Ok(v[1])).unwrap();
                let c = F64Var::new_input(cs.clone(), || Ok(v[2])).unwrap();

                F64Var::enforce_equal(&op(a, b), &c).unwrap();

                !cs.is_satisfied().unwrap()
            })
            .collect::<Vec<_>>();

        assert_eq!(r.len(), 0, "{:#?}", r);

        Ok(())
    }

    #[test]
    fn test_add() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/add")?, std::ops::Add::add)
    }

    #[test]
    fn test_sub() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/sub")?, std::ops::Sub::sub)
    }

    #[test]
    fn test_mul() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/mul")?, std::ops::Mul::mul)
    }

    #[test]
    fn test_div() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/div")?, std::ops::Div::div)
    }

    #[test]
    fn test_sqrt() -> Result<(), Box<dyn Error>> {
        test_unary_op(File::open("data/sqrt")?, |x| F64Var::sqrt(&x).unwrap())
    }
}
