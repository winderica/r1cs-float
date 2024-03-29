use crate::r1cs::{Namespace, SynthesisError};
use crate::r1cs_std::Vec;
use ark_ff::Field;
use core::borrow::Borrow;

/// Describes the mode that a variable should be allocated in within
/// a `ConstraintSystem`.
#[derive(Eq, PartialEq, Ord, PartialOrd, Debug, Copy, Clone)]
pub enum AllocationMode {
    /// Indicate to the `ConstraintSystem` that the high-level variable should
    /// be allocated as a constant. That is, no `Variable`s should be
    /// generated.
    Constant = 0,

    /// Indicate to the `ConstraintSystem` that the high-level variable should
    /// be allocated as a public input to the `ConstraintSystem`.
    Input = 1,

    /// Indicate to the `ConstraintSystem` that the high-level variable should
    /// be allocated as a private witness to the `ConstraintSystem`.
    Witness = 2,

    Committed = 3,
}

/// Specifies how variables of type `Self` should be allocated in a
/// `ConstraintSystem`.
pub trait AllocVar<V, F: Field>
where
    Self: Sized,
    V: ?Sized,
{
    /// Allocates a new variable of type `Self` in the `ConstraintSystem` `cs`.
    /// The mode of allocation is decided by `mode`.
    fn new_variable<T: Borrow<V>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError>;

    /// Allocates a new constant of type `Self` in the `ConstraintSystem` `cs`.
    ///
    /// This should *not* allocate any new variables or constraints in `cs`.
    #[tracing::instrument(target = "r1cs", skip(cs, t))]
    fn new_constant(
        cs: impl Into<Namespace<F>>,
        t: impl Borrow<V>,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, || Ok(t), AllocationMode::Constant)
    }

    /// Allocates a new public input of type `Self` in the `ConstraintSystem`
    /// `cs`.
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_input<T: Borrow<V>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, f, AllocationMode::Input)
    }

    /// Allocates a new private witness of type `Self` in the `ConstraintSystem`
    /// `cs`.
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_witness<T: Borrow<V>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, f, AllocationMode::Witness)
    }

    /// Allocates a new private witness of type `Self` in the `ConstraintSystem`
    /// `cs`.
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_hint<T: Borrow<V>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        let ns: Namespace<F> = cs.into();
        let cs = ns.cs();
        let mode = if cs.is_none() {
            AllocationMode::Constant
        } else {
            AllocationMode::Witness
        };
        Self::new_variable(cs, f, mode)
    }

    /// Allocates a new commitment of type `Self` in the `ConstraintSystem`
    /// `cs`.
    #[tracing::instrument(target = "r1cs", skip(cs, f))]
    fn new_committed<T: Borrow<V>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
    ) -> Result<Self, SynthesisError> {
        Self::new_variable(cs, f, AllocationMode::Committed)
    }
}

/// This blanket implementation just allocates variables in `Self`
/// element by element.
impl<I, F: Field, A: AllocVar<I, F>> AllocVar<[I], F> for Vec<A> {
    fn new_variable<T: Borrow<[I]>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let mut vec = Vec::new();
        for value in f()?.borrow().iter() {
            vec.push(A::new_variable(cs.clone(), || Ok(value), mode)?);
        }
        Ok(vec)
    }
}
