use crate::float::FloatVar;

pub type F64Var<F> = FloatVar<F, 11, 52>;

#[cfg(test)]
mod tests {
    use std::{
        error::Error,
        fmt::Debug,
        fs::File,
        io::{BufRead, BufReader},
    };

    use super::*;
    use crate::{
        r1cs::{ConstraintSystem, ConstraintSystemRef},
        r1cs_std::{
            prelude::{AllocVar, Boolean},
            R1CSVar,
        },
    };
    use ark_bls12_381::Fr;
    use num::ToPrimitive;
    use rayon::prelude::*;

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
            num_constraints(&cs, || F64Var::new_witness(cs.clone(), || Ok(0.1f64)).unwrap())
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn add_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!("{}", num_constraints(&cs, || println!("{}", a + b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn sub_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!("{}", num_constraints(&cs, || println!("{}", a - b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn mul_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!("{}", num_constraints(&cs, || println!("{}", a * b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn div_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!("{}", num_constraints(&cs, || println!("{}", a / b)));

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn sqrt_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!("{}", F64Var::sqrt(&a).unwrap()))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn lt_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!(
                "{}",
                F64Var::is_lt(&a, &b).unwrap().value().unwrap()
            ))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn le_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!(
                "{}",
                F64Var::is_le(&a, &b).unwrap().value().unwrap()
            ))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn gt_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!(
                "{}",
                F64Var::is_gt(&a, &b).unwrap().value().unwrap()
            ))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn ge_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;
        let b = F64Var::new_witness(cs.clone(), || Ok(0.2f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!(
                "{}",
                F64Var::is_ge(&a, &b).unwrap().value().unwrap()
            ))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn trunc_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!("{}", F64Var::trunc(&a).unwrap()))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn floor_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!("{}", F64Var::floor(&a).unwrap()))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    #[test]
    fn ceil_constraints() -> Result<(), Box<dyn Error>> {
        let cs = ConstraintSystem::<Fr>::new_ref();

        let a = F64Var::new_witness(cs.clone(), || Ok(0.1f64))?;

        println!(
            "{}",
            num_constraints(&cs, || println!("{}", F64Var::ceil(&a).unwrap()))
        );

        assert!(cs.is_satisfied()?);

        Ok(())
    }

    fn test_op<
        T: Send + Debug,
        P: FnOnce(&String) -> T + Send + Sync + Copy,
        S: FnOnce(&T) -> bool + Send + Sync + Copy,
        C: FnOnce(&T) -> bool + Send + Sync + Copy,
    >(
        test_data: File,
        parse_line: P,
        is_supported: S,
        is_correct: C,
    ) -> Result<(), Box<dyn Error>> {
        let r = BufReader::new(test_data)
            .lines()
            .collect::<Result<Vec<_>, _>>()?
            .into_par_iter()
            .panic_fuse()
            .map(|line| parse_line(&line))
            .filter(|v| is_supported(v))
            .filter(|v| !is_correct(v))
            .collect::<Vec<_>>();

        assert_eq!(r.len(), 0, "{:#?}", r);

        Ok(())
    }

    fn test_unary_op(
        test_data: File,
        op: fn(F64Var<Fr>) -> F64Var<Fr>,
    ) -> Result<(), Box<dyn Error>> {
        test_op(
            test_data,
            |line| {
                line.split(' ')
                    .take(2)
                    .map(|i| u64::from_str_radix(i, 16).map(f64::from_bits))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            },
            |_| true,
            |v| {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = F64Var::new_witness(cs.clone(), || Ok(v[0])).unwrap();

                let r = op(a).value().unwrap().to_u64().unwrap();

                cs.is_satisfied().unwrap()
                    && ((f64::from_bits(r).is_nan() && v[1].is_nan()) || r == v[1].to_bits())
            },
        )
    }

    fn test_binary_op(
        test_data: File,
        op: fn(F64Var<Fr>, F64Var<Fr>) -> F64Var<Fr>,
    ) -> Result<(), Box<dyn Error>> {
        test_op(
            test_data,
            |line| {
                line.split(' ')
                    .take(3)
                    .map(|i| u64::from_str_radix(i, 16).map(f64::from_bits))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap()
            },
            |_| true,
            |v| {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = F64Var::new_witness(cs.clone(), || Ok(v[0])).unwrap();
                let b = F64Var::new_witness(cs.clone(), || Ok(v[1])).unwrap();

                let r = op(a, b).value().unwrap().to_u64().unwrap();

                cs.is_satisfied().unwrap()
                    && ((f64::from_bits(r).is_nan() && v[2].is_nan()) || r == v[2].to_bits())
            },
        )
    }

    fn test_comparison_op(
        test_data: File,
        op: fn(F64Var<Fr>, F64Var<Fr>) -> Boolean<Fr>,
    ) -> Result<(), Box<dyn Error>> {
        test_op(
            test_data,
            |line| {
                let s = line
                    .split(' ')
                    .take(3)
                    .map(|i| u64::from_str_radix(i, 16))
                    .collect::<Result<Vec<_>, _>>()
                    .unwrap();
                (f64::from_bits(s[0]), f64::from_bits(s[1]), s[2] == 1)
            },
            |_| true,
            |(a, b, c)| {
                let cs = ConstraintSystem::<Fr>::new_ref();
                let a = F64Var::new_witness(cs.clone(), || Ok(*a)).unwrap();
                let b = F64Var::new_witness(cs.clone(), || Ok(*b)).unwrap();

                let r = op(a, b).value().unwrap();

                cs.is_satisfied().unwrap() && r == *c
            },
        )
    }

    #[test]
    fn test_add() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/f64/add")?, std::ops::Add::add)
    }

    #[test]
    fn test_sub() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/f64/sub")?, std::ops::Sub::sub)
    }

    #[test]
    fn test_mul() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/f64/mul")?, std::ops::Mul::mul)
    }

    #[test]
    fn test_div() -> Result<(), Box<dyn Error>> {
        test_binary_op(File::open("data/f64/div")?, std::ops::Div::div)
    }

    #[test]
    fn test_sqrt() -> Result<(), Box<dyn Error>> {
        test_unary_op(File::open("data/f64/sqrt")?, |x| F64Var::sqrt(&x).unwrap())
    }

    #[test]
    fn test_lt() -> Result<(), Box<dyn Error>> {
        test_comparison_op(File::open("data/f64/lt")?, |x, y| {
            F64Var::is_lt(&x, &y).unwrap()
        })
    }

    #[test]
    fn test_le() -> Result<(), Box<dyn Error>> {
        test_comparison_op(File::open("data/f64/le")?, |x, y| {
            F64Var::is_le(&x, &y).unwrap()
        })
    }

    #[test]
    fn test_gt() -> Result<(), Box<dyn Error>> {
        test_comparison_op(File::open("data/f64/lt")?, |x, y| {
            F64Var::is_gt(&y, &x).unwrap()
        })
    }

    #[test]
    fn test_ge() -> Result<(), Box<dyn Error>> {
        test_comparison_op(File::open("data/f64/le")?, |x, y| {
            F64Var::is_ge(&y, &x).unwrap()
        })
    }

    #[test]
    fn test_trunc() -> Result<(), Box<dyn Error>> {
        test_unary_op(File::open("data/f64/trunc")?, |x| {
            F64Var::trunc(&x).unwrap()
        })
    }

    #[test]
    fn test_floor() -> Result<(), Box<dyn Error>> {
        test_unary_op(File::open("data/f64/floor")?, |x| {
            F64Var::floor(&x).unwrap()
        })
    }

    #[test]
    fn test_ceil() -> Result<(), Box<dyn Error>> {
        test_unary_op(File::open("data/f64/ceil")?, |x| F64Var::ceil(&x).unwrap())
    }
}
