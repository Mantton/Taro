//! Declared field order shared by named construction, patterns, and lowering.
use super::instantiate::{
    instantiate_enum_definition_with_args, instantiate_struct_definition_with_args,
};
use crate::{
    compile::context::Gcx,
    hir::DefinitionID,
    sema::{
        models::{AdtKind, EnumVariantKind, Ty, TyKind},
        resolve::models::Visibility,
    },
    span::Symbol,
};

pub(crate) struct NamedField<'ctx> {
    pub name: Symbol,
    pub ty: Ty<'ctx>,
    /// Enum payloads inherit the visibility of their variant constructor.
    pub visibility: Option<Visibility>,
    pub default_provider: Option<DefinitionID>,
}

pub(crate) struct NamedFields<'ctx> {
    pub fields: Vec<NamedField<'ctx>>,
    pub variant_index: Option<usize>,
}

pub(crate) fn named_fields<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    constructor: Option<DefinitionID>,
) -> Option<NamedFields<'ctx>> {
    let ty = super::normalize_aliases(gcx, ty);
    let TyKind::Adt(def, args) = ty.kind() else {
        return None;
    };
    match def.kind {
        AdtKind::Struct if constructor.is_none() && !gcx.is_class_type(ty) => {
            let definition = instantiate_struct_definition_with_args(
                gcx,
                gcx.get_struct_definition(def.id),
                args,
            );
            Some(NamedFields {
                fields: definition
                    .fields
                    .iter()
                    .map(|field| NamedField {
                        name: field.name,
                        ty: field.ty,
                        visibility: Some(field.visibility),
                        default_provider: field.default_provider,
                    })
                    .collect(),
                variant_index: None,
            })
        }
        AdtKind::Enum => {
            let definition =
                instantiate_enum_definition_with_args(gcx, &gcx.get_enum_definition(def.id), args);
            let index = definition
                .variants
                .iter()
                .position(|variant| Some(variant.ctor_def_id) == constructor)?;
            let EnumVariantKind::Struct(fields) = definition.variants[index].kind else {
                return None;
            };
            Some(NamedFields {
                fields: fields
                    .iter()
                    .map(|field| {
                        Some(NamedField {
                            name: field.label?,
                            ty: field.ty,
                            visibility: None,
                            default_provider: None,
                        })
                    })
                    .collect::<Option<_>>()?,
                variant_index: Some(index),
            })
        }
        _ => None,
    }
}
