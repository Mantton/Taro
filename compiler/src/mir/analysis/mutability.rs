//! Writable-place validation is separate from loan conflict checking.
use crate::{
    compile::context::Gcx,
    hir::Mutability,
    mir::{Body, Place, PlaceElem},
    sema::{
        models::{AdtKind, EnumVariantKind, TyKind},
        tycheck::utils::normalize_aliases,
    },
};

/// Requires a structurally checked place. Inline readonly fields constrain all
/// nested inline storage; indirection starts a separate access. A reference
/// always grants write access to its referent, and a `*mut` pointer does too.
pub fn is_place_mutable<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>, place: &Place<'ctx>) -> bool {
    let declaration = &body.locals[place.local];
    let mut ty = declaration.ty;
    let mut mutable = declaration.mutable;
    let mut variant_fields = None;
    for projection in &place.projection {
        ty = normalize_aliases(gcx, ty);
        match projection {
            PlaceElem::Deref => {
                variant_fields = None;
                match ty.kind() {
                    TyKind::Reference(inner) => {
                        mutable = true;
                        ty = inner;
                    }
                    TyKind::Pointer(inner, mode) => {
                        mutable = mode == Mutability::Mutable;
                        ty = inner;
                    }
                    _ => return false,
                }
            }
            PlaceElem::Field(index, field_ty) => {
                if let Some(fields) = variant_fields.take() {
                    let fields: &[crate::sema::models::EnumVariantField<'ctx>] = fields;
                    let Some(field) = fields.get(index.index()) else {
                        return false;
                    };
                    mutable &= field.mutability == Mutability::Mutable;
                } else if let TyKind::Adt(definition, _) = ty.kind() {
                    if definition.kind == AdtKind::Struct {
                        let Some(definition) = gcx.try_get_struct_definition(definition.id) else {
                            return false;
                        };
                        let Some(field) = definition.fields.get(index.index()) else {
                            return false;
                        };
                        mutable &= field.mutability == Mutability::Mutable;
                    }
                }
                ty = *field_ty;
            }
            PlaceElem::VariantDowncast { index, .. } => {
                let TyKind::Adt(definition, arguments) = ty.kind() else {
                    return false;
                };
                if definition.kind != AdtKind::Enum {
                    return false;
                }
                let Some(definition) = gcx.try_get_enum_definition(definition.id) else {
                    return false;
                };
                let Some(variant) = definition.variants.get(index.index()) else {
                    return false;
                };
                variant_fields = match variant.kind {
                    EnumVariantKind::Unit => None,
                    EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => {
                        Some(fields)
                    }
                };
                ty = crate::mir::enum_variant_tuple_ty(
                    gcx,
                    definition.adt_def.id,
                    *index,
                    arguments,
                );
            }
        }
    }
    mutable
}

#[cfg(test)]
mod tests {
    use crate::test_support::analyze_script_mir_diagnostics;

    #[test]
    fn references_to_nested_fields_are_writable() {
        for borrow in ["&outer.inner.count"] {
            let source = format!(
                "struct Inner {{ count: int32 }}\nstruct Outer {{ readonly inner: Inner }}\nfunc edit(_ value: &int32) {{ *value = 3 }}\nfunc main() {{ var outer = Outer {{ inner: Inner {{ count: 1 }} }}; edit({borrow}) }}"
            );
            let diagnostics = analyze_script_mir_diagnostics(&source);
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        }
    }

    #[test]
    fn readonly_reference_slots_are_shallow_and_references_stay_writable() {
        let prefix = "struct Holder { readonly link: &int32 }\nfunc main() { var value: int32 = 1; holder := Holder { link: &value }; ";
        let allowed = format!("{prefix} *holder.link = 2 }}");
        let diagnostics = analyze_script_mir_diagnostics(&allowed);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        let rejected = format!("{prefix} reader := &holder; *reader.link = 2 }}");
        let diagnostics = analyze_script_mir_diagnostics(&rejected);
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }

    #[test]
    fn enum_payload_fields_keep_their_individual_readonly_permissions() {
        use crate::{
            mir::{
                Place, PlaceElem,
                test_support::{minimal_body, push_temp},
            },
            sema::models::{GenericArguments, Ty, TyKind},
            thir::{FieldIndex, VariantIndex},
        };
        crate::test_support::analyze_script(
            "enum State {\ncase frozen(readonly int32)\ncase editable(int32)\n}\nfunc main() {}",
            |package, gcx| {
                let definition = gcx.get_enum_definition(package.root.declarations[0].id);
                let ty = Ty::new(
                    TyKind::Adt(definition.adt_def, GenericArguments::empty()),
                    gcx,
                );
                let mut body = minimal_body(gcx);
                let local = push_temp(&mut body, ty);
                for (index, variant) in definition.variants.iter().enumerate() {
                    let place = Place {
                        local,
                        projection: vec![
                            PlaceElem::VariantDowncast {
                                name: variant.name,
                                index: VariantIndex::from_usize(index),
                            },
                            PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.int32),
                        ],
                    };
                    assert_eq!(super::is_place_mutable(gcx, &body, &place), index == 1);
                }
            },
        );
    }
}
