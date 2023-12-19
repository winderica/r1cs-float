/// Reduce an R1CS instance to a *Quadratic Arithmetic Program* instance.
pub mod r1cs_to_qap;

/// Data structures used by the prover, verifier, and generator.
pub mod data_structures;

/// Generate public parameters for the Groth16 zkSNARK construction.
pub mod generator;

/// Create proofs for the Groth16 zkSNARK construction.
pub mod prover;

/// Verify proofs for the Groth16 zkSNARK construction.
pub mod verifier;

mod logderivarg;

use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{marker::PhantomData, rand::RngCore, vec::Vec};
use r1cs_to_qap::{LibsnarkReduction, R1CSToQAP};
use rand::CryptoRng;

pub use self::{
    data_structures::*,
    generator::*,
    logderivarg::{generate_commitment, LOOKUP_TABLE_BITS},
    prover::*,
    verifier::*,
};
use crate::r1cs::{ConstraintSynthesizer, SynthesisError};

/// The basic functionality for a SNARK.
pub trait SNARK<F: PrimeField> {
    /// The information required by the prover to produce a proof for a specific
    /// circuit *C*.
    type ProvingKey: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The information required by the verifier to check a proof for a specific
    /// circuit *C*.
    type VerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// The proof output by the prover.
    type Proof: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// This contains the verification key, but preprocessed to enable faster
    /// verification.
    type ProcessedVerifyingKey: Clone + CanonicalSerialize + CanonicalDeserialize;

    /// Errors encountered during setup, proving, or verification.
    type Error: 'static + ark_std::error::Error;

    /// Takes in a description of a computation (specified in R1CS constraints),
    /// and samples proving and verification keys for that circuit.
    fn circuit_specific_setup<C: ConstraintSynthesizer<F>, R: RngCore + CryptoRng>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Self::Error>;

    /// Generates a proof of satisfaction of the arithmetic circuit C (specified
    /// as R1CS constraints).
    fn prove<C: ConstraintSynthesizer<F>, R: RngCore + CryptoRng>(
        circuit_pk: &Self::ProvingKey,
        circuit: C,
        rng: &mut R,
    ) -> Result<Self::Proof, Self::Error>;

    /// Checks that `proof` is a valid proof of the satisfaction of circuit
    /// encoded in `circuit_vk`, with respect to the public input `public_input`,
    /// specified as R1CS constraints.
    fn verify(
        circuit_vk: &Self::VerifyingKey,
        public_input: &[F],
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error> {
        let pvk = Self::process_vk(circuit_vk)?;
        Self::verify_with_processed_vk(&pvk, public_input, proof)
    }

    /// Preprocesses `circuit_vk` to enable faster verification.
    fn process_vk(
        circuit_vk: &Self::VerifyingKey,
    ) -> Result<Self::ProcessedVerifyingKey, Self::Error>;

    /// Checks that `proof` is a valid proof of the satisfaction of circuit
    /// encoded in `circuit_pvk`, with respect to the public input `public_input`,
    /// specified as R1CS constraints.
    fn verify_with_processed_vk(
        circuit_pvk: &Self::ProcessedVerifyingKey,
        public_input: &[F],
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error>;
}

/// A SNARK with (only) circuit-specific setup.
pub trait CircuitSpecificSetupSNARK<F: PrimeField>: SNARK<F> {
    /// The setup algorithm for circuit-specific SNARKs. By default, this
    /// just invokes `<Self as SNARK<F>>::circuit_specific_setup(...)`.
    fn setup<C: ConstraintSynthesizer<F>, R: RngCore + CryptoRng>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Self::Error> {
        <Self as SNARK<F>>::circuit_specific_setup(circuit, rng)
    }
}

/// The SNARK of [[Groth16]](https://eprint.iacr.org/2016/260.pdf).
pub struct Groth16<E: Pairing, QAP: R1CSToQAP = LibsnarkReduction> {
    _p: PhantomData<(E, QAP)>,
}

impl<E: Pairing, QAP: R1CSToQAP> SNARK<E::ScalarField> for Groth16<E, QAP> {
    type ProvingKey = ProvingKey<E>;
    type VerifyingKey = VerifyingKey<E>;
    type Proof = Proof<E>;
    type ProcessedVerifyingKey = PreparedVerifyingKey<E>;
    type Error = SynthesisError;

    fn circuit_specific_setup<C: ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
        circuit: C,
        rng: &mut R,
    ) -> Result<(Self::ProvingKey, Self::VerifyingKey), Self::Error> {
        let pk = Self::generate_random_parameters_with_reduction(circuit, rng)?;
        let vk = pk.vk.clone();

        Ok((pk, vk))
    }

    fn prove<C: ConstraintSynthesizer<E::ScalarField>, R: RngCore>(
        pk: &Self::ProvingKey,
        circuit: C,
        rng: &mut R,
    ) -> Result<Self::Proof, Self::Error> {
        Self::create_random_proof_with_reduction(circuit, pk, rng)
    }

    fn process_vk(
        circuit_vk: &Self::VerifyingKey,
    ) -> Result<Self::ProcessedVerifyingKey, Self::Error> {
        Ok(prepare_verifying_key(circuit_vk))
    }

    fn verify_with_processed_vk(
        circuit_pvk: &Self::ProcessedVerifyingKey,
        x: &[E::ScalarField],
        proof: &Self::Proof,
    ) -> Result<bool, Self::Error> {
        Ok(Self::verify_proof(&circuit_pvk, proof, &x)?)
    }
}

impl<E: Pairing, QAP: R1CSToQAP> CircuitSpecificSetupSNARK<E::ScalarField> for Groth16<E, QAP> {}

#[cfg(test)]
mod tests {
    use crate::{
        r1cs::ConstraintSystemRef,
        r1cs_std::{
            fields::fp::FpVar,
            prelude::{AllocVar, EqGadget, FieldVar},
            R1CSVar,
        },
    };

    use super::*;
    use ark_bls12_381::Bls12_381;
    use ark_ff::BigInteger;
    use ark_std::test_rng;
    use rand::SeedableRng;

    struct MySillyCircuit<F: PrimeField> {
        a: F,
    }

    impl<F: PrimeField> ConstraintSynthesizer<F> for MySillyCircuit<F> {
        fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
            let length = 64usize;

            for i in 0u64..1000 {
                let mut x = FpVar::new_witness(cs.clone(), || Ok(self.a))?;
                x += FpVar::constant(F::from(i));

                let extended_length = length.next_multiple_of(LOOKUP_TABLE_BITS);
                let num_chunks = extended_length / LOOKUP_TABLE_BITS;
                let mut chunks = x
                    .value()
                    .unwrap_or_default()
                    .into_bigint()
                    .to_bits_le()
                    .chunks(LOOKUP_TABLE_BITS)
                    .take(num_chunks)
                    .map(|chunk| F::from_bigint(F::BigInt::from_bits_le(chunk)).unwrap())
                    .collect::<Vec<_>>();

                if extended_length != length {
                    chunks[num_chunks - 1] *= F::from(1u64 << (extended_length - length));
                }

                let chunks = if cs.is_none() {
                    Vec::<FpVar<_>>::new_constant(cs.clone(), chunks)?
                } else {
                    Vec::new_committed(cs.clone(), || Ok(chunks))?
                };

                if num_chunks > 1 {
                    let mut accumulated = FpVar::zero();
                    for (i, v) in chunks.iter().enumerate() {
                        accumulated = &accumulated
                            + v * if i == num_chunks - 1 {
                                F::from(
                                    1u64 << (i * LOOKUP_TABLE_BITS - (extended_length - length)),
                                )
                            } else {
                                F::from(1u64 << (i * LOOKUP_TABLE_BITS))
                            };
                    }
                    accumulated.enforce_equal(&x)?;
                } else {
                    chunks[0].enforce_equal(&(&x * F::from(1u64 << (extended_length - length))))?;
                }
            }

            Ok(())
        }
    }

    fn test_prove_and_verify<E>(n_iters: usize)
    where
        E: Pairing,
    {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

        let (pk, vk) = Groth16::<E>::setup(
            MySillyCircuit {
                a: Default::default(),
            },
            &mut rng,
        )
        .unwrap();
        let pvk = prepare_verifying_key::<E>(&vk);

        for _ in 0..n_iters {
            let a = E::ScalarField::from(10000u64);

            let proof = Groth16::<E>::prove(&pk, MySillyCircuit { a }, &mut rng).unwrap();

            assert!(Groth16::<E>::verify_with_processed_vk(&pvk, &[], &proof).unwrap());
        }
    }

    #[test]
    fn prove_and_verify() {
        test_prove_and_verify::<Bls12_381>(1);
    }
}
