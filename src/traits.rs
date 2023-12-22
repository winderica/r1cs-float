use ark_ff::{BigInteger, PrimeField};
use ark_std::One;
use num::{BigUint, Integer};

use crate::{
    groth16::LOOKUP_TABLE_BITS,
    r1cs::SynthesisError,
    r1cs_std::{
        fields::fp::FpVar,
        prelude::{AllocVar, Boolean, EqGadget, FieldVar},
        R1CSVar,
    },
};

pub trait BitDecompose<F: PrimeField>
where
    Self: Sized,
{
    fn enforce_bit_length(&self, length: usize) -> Result<(), SynthesisError>;

    fn abs(&self, length: usize) -> Result<(Self, Boolean<F>), SynthesisError>;

    fn is_positive(&self, length: usize) -> Result<Boolean<F>, SynthesisError> {
        Ok(self.abs(length)?.1)
    }

    fn max(&self, other: &Self, diff_length: usize) -> Result<Self, SynthesisError>;

    fn min(&self, other: &Self, diff_length: usize) -> Result<Self, SynthesisError>;
}

impl<F: PrimeField> BitDecompose<F> for FpVar<F> {
    fn enforce_bit_length(&self, length: usize) -> Result<(), SynthesisError> {
        let cs = self.cs();

        // {
        //     println!("{}", length);
        //     let x: BigUint = self.value().unwrap_or_default().into();
        //     assert!(x < BigUint::one() << length);
        // }

        let extended_length = length.next_multiple_of(&LOOKUP_TABLE_BITS);
        let num_chunks = extended_length / LOOKUP_TABLE_BITS;

        let mut chunks = self
            .value()
            .unwrap_or_default()
            .into_bigint()
            .to_bits_le()
            .chunks(LOOKUP_TABLE_BITS)
            .take(num_chunks)
            .map(|chunk| F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap())
            .collect::<Vec<_>>();

        if extended_length != length {
            chunks[num_chunks - 1] *= F::from(BigUint::one() << (extended_length - length));
        }

        let chunks = if cs.is_none() {
            Vec::<FpVar<_>>::new_constant(cs, chunks)?
        } else {
            Vec::new_committed(cs, || Ok(chunks))?
        };

        if num_chunks > 1 {
            let mut accumulated = FpVar::zero();
            for (i, v) in chunks.iter().enumerate() {
                accumulated = &accumulated
                    + v * if i == num_chunks - 1 {
                        F::from(
                            BigUint::one() << (i * LOOKUP_TABLE_BITS - (extended_length - length)),
                        )
                    } else {
                        F::from(BigUint::one() << (i * LOOKUP_TABLE_BITS))
                    };
            }
            accumulated.enforce_equal(self)?;
        } else {
            chunks[0]
                .enforce_equal(&(self * F::from(BigUint::one() << (extended_length - length))))?;
        }

        Ok(())
    }

    fn abs(&self, length: usize) -> Result<(FpVar<F>, Boolean<F>), SynthesisError> {
        let cs = self.cs();

        let is_positive = Boolean::new_hint(cs.clone(), || {
            self.value()
                .map(|v| v.into_bigint() < F::MODULUS_MINUS_ONE_DIV_TWO)
        })?;
        let abs = is_positive.select(self, &self.negate()?)?;

        abs.enforce_bit_length(length)?;

        Ok((abs, is_positive))
    }

    fn max(&self, other: &Self, diff_length: usize) -> Result<Self, SynthesisError> {
        (self - other).is_positive(diff_length)?.select(self, other)
    }

    fn min(&self, other: &Self, diff_length: usize) -> Result<Self, SynthesisError> {
        (self - other).is_positive(diff_length)?.select(other, self)
    }
}
