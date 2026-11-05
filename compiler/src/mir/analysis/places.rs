//! Canonical storage identities used by definite-initialization analysis.
//! Field type annotations are validated separately and do not distinguish
//! storage paths.
use crate::{
    mir::{LocalId, Place, PlaceElem},
    thir::{FieldIndex, VariantIndex},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjectionKey {
    Deref,
    Field(FieldIndex),
    Variant(VariantIndex),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PlaceKey {
    pub local: LocalId,
    pub projection: Vec<ProjectionKey>,
}

impl From<&Place<'_>> for PlaceKey {
    fn from(place: &Place<'_>) -> Self {
        Self {
            local: place.local,
            projection: place
                .projection
                .iter()
                .map(|projection| match projection {
                    PlaceElem::Deref => ProjectionKey::Deref,
                    PlaceElem::Field(index, _) => ProjectionKey::Field(*index),
                    PlaceElem::VariantDowncast { index, .. } => ProjectionKey::Variant(*index),
                })
                .collect(),
        }
    }
}

impl PlaceKey {
    pub fn local(local: LocalId) -> Self {
        Self {
            local,
            projection: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn field_type_annotations_do_not_change_storage_identity() {
        crate::test_support::with_test_gcx(|gcx| {
            let first = Place {
                local: LocalId::from_raw(1),
                projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.int32)],
            };
            let second = Place {
                local: LocalId::from_raw(1),
                projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.uint32)],
            };
            // A wrong annotation must be rejected by type validation, rather
            // than becoming a second supposedly independent storage path.
            assert_eq!(PlaceKey::from(&first), PlaceKey::from(&second));
        });
    }
}
