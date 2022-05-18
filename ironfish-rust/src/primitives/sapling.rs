use std::convert::TryInto;

use blake2s_simd::Params as Blake2sParams;
use byteorder::{LittleEndian, WriteBytesExt};
use group::{cofactor::CofactorGroup, Curve, Group, GroupEncoding};
use rand::{CryptoRng, Rng, RngCore};
use zcash_primitives::{
    constants,
    keys::prf_expand,
    pedersen_hash::{pedersen_hash, Personalization},
    primitives::{Diversifier, Nullifier, Rseed, ViewingKey},
};

use super::asset_type::AssetType;

#[derive(Clone)]
pub struct ValueCommitment {
    pub asset_generator: jubjub::ExtendedPoint,
    pub value: u64,
    pub randomness: jubjub::Fr,
}

impl ValueCommitment {
    pub fn commitment(&self) -> jubjub::SubgroupPoint {
        (CofactorGroup::clear_cofactor(&self.asset_generator) * jubjub::Fr::from(self.value))
            + (constants::VALUE_COMMITMENT_RANDOMNESS_GENERATOR * self.randomness)
    }
}

/// A Sapling payment address.
///
/// # Invariants
///
/// `pk_d` is guaranteed to be prime-order (i.e. in the prime-order subgroup of Jubjub,
/// and not the identity).
#[derive(Clone, Debug)]
pub struct PaymentAddress {
    pk_d: jubjub::SubgroupPoint,
    diversifier: Diversifier,
}

impl PartialEq for PaymentAddress {
    fn eq(&self, other: &Self) -> bool {
        self.pk_d == other.pk_d && self.diversifier == other.diversifier
    }
}

impl PaymentAddress {
    /// Constructs a PaymentAddress from a diversifier and a Jubjub point.
    ///
    /// Returns None if `pk_d` is the identity.
    pub fn from_parts(diversifier: Diversifier, pk_d: jubjub::SubgroupPoint) -> Option<Self> {
        if pk_d.is_identity().into() {
            None
        } else {
            Some(PaymentAddress { pk_d, diversifier })
        }
    }

    /// Constructs a PaymentAddress from a diversifier and a Jubjub point.
    ///
    /// Only for test code, as this explicitly bypasses the invariant.
    #[cfg(test)]
    pub(crate) fn from_parts_unchecked(
        diversifier: Diversifier,
        pk_d: jubjub::SubgroupPoint,
    ) -> Self {
        PaymentAddress { pk_d, diversifier }
    }

    /// Parses a PaymentAddress from bytes.
    pub fn from_bytes(bytes: &[u8; 43]) -> Option<Self> {
        let diversifier = {
            let mut tmp = [0; 11];
            tmp.copy_from_slice(&bytes[0..11]);
            Diversifier(tmp)
        };
        // Check that the diversifier is valid
        diversifier.g_d()?;

        let pk_d = jubjub::SubgroupPoint::from_bytes(bytes[11..43].try_into().unwrap());
        if pk_d.is_some().into() {
            PaymentAddress::from_parts(diversifier, pk_d.unwrap())
        } else {
            None
        }
    }

    /// Returns the byte encoding of this `PaymentAddress`.
    pub fn to_bytes(&self) -> [u8; 43] {
        let mut bytes = [0; 43];
        bytes[0..11].copy_from_slice(&self.diversifier.0);
        bytes[11..].copy_from_slice(&self.pk_d.to_bytes());
        bytes
    }

    /// Returns the [`Diversifier`] for this `PaymentAddress`.
    pub fn diversifier(&self) -> &Diversifier {
        &self.diversifier
    }

    /// Returns `pk_d` for this `PaymentAddress`.
    pub fn pk_d(&self) -> &jubjub::SubgroupPoint {
        &self.pk_d
    }

    pub fn g_d(&self) -> Option<jubjub::SubgroupPoint> {
        self.diversifier.g_d()
    }

    pub fn create_note(&self, asset_type: AssetType, value: u64, rseed: Rseed) -> Option<Note> {
        self.g_d().map(|g_d| Note {
            asset_type,
            value,
            rseed,
            g_d,
            pk_d: self.pk_d,
        })
    }
}

#[derive(Clone, Debug)]
pub struct Note {
    /// The asset type that the note represents
    pub asset_type: AssetType,
    /// The value of the note
    pub value: u64,
    /// The diversified base of the address, GH(d)
    pub g_d: jubjub::SubgroupPoint,
    /// The public key of the address, g_d^ivk
    pub pk_d: jubjub::SubgroupPoint,
    /// rseed
    pub rseed: Rseed,
}

impl PartialEq for Note {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
            && self.asset_type == other.asset_type
            && self.g_d == other.g_d
            && self.pk_d == other.pk_d
            && self.rcm() == other.rcm()
    }
}

impl Note {
    pub fn uncommitted() -> bls12_381::Scalar {
        // The smallest u-coordinate that is not on the curve
        // is one.
        bls12_381::Scalar::one()
    }

    /// Computes the note commitment, returning the full point.
    fn cm_full_point(&self) -> jubjub::SubgroupPoint {
        // Calculate the note contents, as bytes
        let mut note_contents = vec![];

        // Write the asset generator, cofactor not cleared
        note_contents.extend_from_slice(&self.asset_type.asset_generator().to_bytes());

        // Writing the value in little endian
        (&mut note_contents)
            .write_u64::<LittleEndian>(self.value)
            .unwrap();

        // Write g_d
        note_contents.extend_from_slice(&self.g_d.to_bytes());

        // Write pk_d
        note_contents.extend_from_slice(&self.pk_d.to_bytes());

        assert_eq!(note_contents.len(), 32 + 32 + 32 + 8);

        // Compute the Pedersen hash of the note contents
        let hash_of_contents = pedersen_hash(
            Personalization::NoteCommitment,
            note_contents
                .into_iter()
                .flat_map(|byte| (0..8).map(move |i| ((byte >> i) & 1) == 1)),
        );

        // Compute final commitment
        (constants::NOTE_COMMITMENT_RANDOMNESS_GENERATOR * self.rcm()) + hash_of_contents
    }

    /// Computes the nullifier given the viewing key and
    /// note position
    pub fn nf(&self, viewing_key: &ViewingKey, position: u64) -> Nullifier {
        // Compute rho = cm + position.G
        let rho = self.cm_full_point()
            + (constants::NULLIFIER_POSITION_GENERATOR * jubjub::Fr::from(position));

        // Compute nf = BLAKE2s(nk | rho)
        Nullifier::from_slice(
            Blake2sParams::new()
                .hash_length(32)
                .personal(constants::PRF_NF_PERSONALIZATION)
                .to_state()
                .update(&viewing_key.nk.to_bytes())
                .update(&rho.to_bytes())
                .finalize()
                .as_bytes(),
        )
        .unwrap()
    }

    /// Computes the note commitment
    pub fn cmu(&self) -> bls12_381::Scalar {
        // The commitment is in the prime order subgroup, so mapping the
        // commitment to the u-coordinate is an injective encoding.
        jubjub::ExtendedPoint::from(self.cm_full_point())
            .to_affine()
            .get_u()
    }

    pub fn rcm(&self) -> jubjub::Fr {
        match self.rseed {
            Rseed::BeforeZip212(rcm) => rcm,
            Rseed::AfterZip212(rseed) => {
                jubjub::Fr::from_bytes_wide(prf_expand(&rseed, &[0x04]).as_array())
            }
        }
    }

    pub fn generate_or_derive_esk<R: RngCore + CryptoRng>(&self, rng: &mut R) -> jubjub::Fr {
        self.generate_or_derive_esk_internal(rng)
    }

    pub(crate) fn generate_or_derive_esk_internal<R: RngCore>(&self, rng: &mut R) -> jubjub::Fr {
        match self.derive_esk() {
            None => {
                let mut buffer = [0u8; 64];
                rng.fill(&mut buffer[..]);
                jubjub::Fr::from_bytes_wide(&buffer)
            }
            Some(esk) => esk,
        }
    }

    /// Returns the derived `esk` if this note was created after ZIP 212 activated.
    pub fn derive_esk(&self) -> Option<jubjub::Fr> {
        match self.rseed {
            Rseed::BeforeZip212(_) => None,
            Rseed::AfterZip212(rseed) => Some(jubjub::Fr::from_bytes_wide(
                prf_expand(&rseed, &[0x05]).as_array(),
            )),
        }
    }
}
