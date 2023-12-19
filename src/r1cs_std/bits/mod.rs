use crate::r1cs::SynthesisError;
use crate::r1cs_std::{bits::boolean::Boolean, Vec};
use ark_ff::Field;

/// This module contains `Boolean`, a R1CS equivalent of the `bool` type.
pub mod boolean;

/// Specifies constraints for conversion to a little-endian bit representation
/// of `self`.
pub trait ToBitsGadget<F: Field> {
    /// Outputs the canonical little-endian bit-wise representation of `self`.
    ///
    /// This is the correct default for 99% of use cases.
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError>;

    /// Outputs a possibly non-unique little-endian bit-wise representation of
    /// `self`.
    ///
    /// If you're not absolutely certain that your usecase can get away with a
    /// non-canonical representation, please use `self.to_bits()` instead.
    fn to_non_unique_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.to_bits_le()
    }

    /// Outputs the canonical big-endian bit-wise representation of `self`.
    fn to_bits_be(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut res = self.to_bits_le()?;
        res.reverse();
        Ok(res)
    }

    /// Outputs a possibly non-unique big-endian bit-wise representation of
    /// `self`.
    fn to_non_unique_bits_be(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        let mut res = self.to_non_unique_bits_le()?;
        res.reverse();
        Ok(res)
    }
}

impl<F: Field> ToBitsGadget<F> for Boolean<F> {
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(vec![self.clone()])
    }
}

impl<F: Field> ToBitsGadget<F> for [Boolean<F>] {
    /// Outputs `self`.
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        Ok(self.to_vec())
    }
}

impl<F: Field, T> ToBitsGadget<F> for Vec<T>
where
    [T]: ToBitsGadget<F>,
{
    fn to_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.as_slice().to_bits_le().map(|v| v.to_vec())
    }

    fn to_non_unique_bits_le(&self) -> Result<Vec<Boolean<F>>, SynthesisError> {
        self.as_slice().to_non_unique_bits_le().map(|v| v.to_vec())
    }
}
