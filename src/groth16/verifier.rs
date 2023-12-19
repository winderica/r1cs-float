use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup};
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::One;
use sha2::Sha256;

use super::{r1cs_to_qap::R1CSToQAP, Groth16};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use crate::r1cs::{Result as R1CSResult, SynthesisError};

use core::ops::{AddAssign, Neg};

/// Prepare the verifying key `vk` for use in proof verification.
pub fn prepare_verifying_key<E: Pairing>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    PreparedVerifyingKey {
        vk: vk.clone(),
        alpha_g1_beta_g2: E::pairing(vk.alpha_g1, vk.beta_g2).0,
        gamma_g2_neg_pc: vk.gamma_g2.into_group().neg().into_affine().into(),
        delta_g2_neg_pc: vk.delta_g2.into_group().neg().into_affine().into(),
    }
}

impl<E: Pairing, QAP: R1CSToQAP> Groth16<E, QAP> {
    /// Prepare proof inputs for use with [`verify_proof_with_prepared_inputs`], wrt the prepared
    /// verification key `pvk` and instance public inputs.
    pub fn prepare_inputs(
        pvk: &PreparedVerifyingKey<E>,
        public_inputs: &[E::ScalarField],
        cm: Option<E::G1Affine>,
    ) -> R1CSResult<E::G1> {
        let public_inputs = if cm.is_none() {
            public_inputs.to_owned()
        } else {
            let mut serialized = vec![0; cm.unwrap().serialized_size(Compress::Yes)];
            cm.unwrap()
                .serialize_compressed(&mut serialized[..])
                .unwrap();
            let hasher = <DefaultFieldHasher<Sha256> as HashToField<E::ScalarField>>::new(&[]);
            let challenge: E::ScalarField = hasher.hash_to_field(&serialized, 1)[0];

            vec![public_inputs, &[challenge]].concat()
        };

        if (public_inputs.len() + 1) != pvk.vk.gamma_abc_g1.len() {
            return Err(SynthesisError::MalformedVerifyingKey);
        }

        let mut g_ic = pvk.vk.gamma_abc_g1[0].into_group();
        for (i, b) in public_inputs.iter().zip(pvk.vk.gamma_abc_g1.iter().skip(1)) {
            g_ic.add_assign(&b.mul_bigint(i.into_bigint()));
        }

        Ok(g_ic)
    }

    /// Verify a Groth16 proof `proof` against the prepared verification key `pvk` and prepared public
    /// inputs. This should be preferred over [`verify_proof`] if the instance's public inputs are
    /// known in advance.
    pub fn verify_proof_with_prepared_inputs(
        pvk: &PreparedVerifyingKey<E>,
        proof: &Proof<E>,
        prepared_inputs: &E::G1,
    ) -> R1CSResult<bool> {
        let qap = E::multi_miller_loop(
            [
                <E::G1Affine as Into<E::G1Prepared>>::into(proof.a),
                prepared_inputs.into_affine().into(),
                proof.c.into(),
            ],
            [
                proof.b.into(),
                pvk.gamma_g2_neg_pc.clone(),
                pvk.delta_g2_neg_pc.clone(),
            ],
        );

        let test = E::final_exponentiation(qap).ok_or(SynthesisError::UnexpectedIdentity)?;

        Ok(test.0 == pvk.alpha_g1_beta_g2)
    }

    /// Verify a Groth16 proof `proof` against the prepared verification key `pvk`,
    /// with respect to the instance `public_inputs`.
    pub fn verify_proof(
        pvk: &PreparedVerifyingKey<E>,
        proof: &Proof<E>,
        public_inputs: &[E::ScalarField],
    ) -> R1CSResult<bool> {
        let mut prepared_inputs = Self::prepare_inputs(pvk, public_inputs, proof.cm)?;
        if proof.cm.is_some() {
            if !E::multi_pairing(
                &[proof.cm.unwrap(), proof.pok.unwrap()],
                &[pvk.vk.pedersen_g, pvk.vk.pedersen_g_inv_neg_sigma],
            )
            .0
            .is_one()
            {
                return Ok(false);
            }
            prepared_inputs.add_assign(&proof.cm.unwrap());
        }

        Self::verify_proof_with_prepared_inputs(pvk, proof, &prepared_inputs)
    }
}
