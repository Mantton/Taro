//! Exact declaration shapes required by compiler-lowered address and value
//! operations. Checking these shapes prevents malformed intrinsic calls.

pub(crate) mod atomic;
pub(crate) mod memory;

pub(crate) fn is_borrow_projection(symbol: &str) -> bool {
    matches!(
        symbol,
        "__intrinsic_array_read_unchecked"
            | "__intrinsic_ref_project"
            | "__intrinsic_ref_project_mut"
    )
}

/// Validate the complete unsafe address-projection signature. Bounds and
/// initialization remain the caller's responsibility.
pub(crate) fn projection_signature(
    gcx: crate::compile::context::Gcx<'_>,
    id: crate::hir::DefinitionID,
) -> Option<()> {
    use crate::{
        hir::{Abi, Mutability},
        sema::models::TyKind,
    };
    if let Some(result) = super::erased_access::projection_signature(gcx, id) {
        return Some(result);
    }
    let signature = gcx.get_signature(id);
    if !gcx.definition_is_unsafe(id) {
        return None;
    }
    if signature.abi != Some(Abi::Intrinsic) || signature.is_variadic || signature.inputs.len() != 2
    {
        return None;
    }
    let (mode, array) = match gcx.definition_ident(id).symbol.as_str() {
        "__intrinsic_array_read_unchecked" => (Mutability::Immutable, true),
        "__intrinsic_ref_project" => (Mutability::Immutable, false),
        "__intrinsic_ref_project_mut" => (Mutability::Mutable, false),
        _ => return None,
    };
    let TyKind::Reference(source) = signature.inputs[0].ty.kind() else {
        return None;
    };
    let TyKind::Reference(result) = signature.output.kind() else {
        return None;
    };
    if array {
        let TyKind::Array { element, .. } = source.kind() else {
            return None;
        };
        if element != result || signature.inputs[1].ty != gcx.types.uint {
            return None;
        }
    } else {
        let TyKind::Pointer(element, pointer_mode) = signature.inputs[1].ty.kind() else {
            return None;
        };
        if element != result || pointer_mode != mode {
            return None;
        }
    }

    Some(())
}

/// Validate the value and address operations used by GC-backed std types.
pub(crate) fn value_signature(
    gcx: crate::compile::context::Gcx<'_>,
    id: crate::hir::DefinitionID,
) -> Option<()> {
    if super::statics::referenced_storage(gcx, id).is_some() {
        return Some(());
    }
    if memory::empty_uninit(gcx, id) {
        return Some(());
    }
    if is_class_handle_intrinsic(gcx.definition_ident(id).symbol.as_str())
        && class_handle_signature(gcx, id)
    {
        return Some(());
    }
    if class_field_access_signature(gcx, id) {
        return Some(());
    }
    if let Some(result) = projection_signature(gcx, id) {
        return Some(result);
    }
    if pure_address_result(gcx, id) {
        return Some(());
    }
    use crate::{
        hir::{Abi, Mutability},
        sema::{models::TyKind, tycheck::utils::normalize_aliases},
    };
    let sig = gcx.get_signature(id);
    // Address extraction preserves the reference's pointee and pointer mode.
    if is_reference_address(gcx.definition_ident(id).symbol.as_str()) {
        let mode = if gcx.definition_ident(id).symbol.as_str() == "__intrinsic_mut_ref_to_ptr" {
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };
        if sig.abi != Some(Abi::Intrinsic) || sig.is_variadic || sig.inputs.len() != 1 {
            return None;
        }
        let TyKind::Reference(input) = normalize_aliases(gcx, sig.inputs[0].ty).kind() else {
            return None;
        };
        let TyKind::Pointer(output, output_mode) = normalize_aliases(gcx, sig.output).kind() else {
            return None;
        };
        return (output_mode == mode
            && normalize_aliases(gcx, input) == normalize_aliases(gcx, output))
        .then_some(());
    }
    if sig.abi != Some(Abi::Intrinsic) || sig.is_variadic {
        return None;
    }
    let symbol = gcx.definition_ident(id).symbol;
    let slice = symbol.as_str() == "__intrinsic_string_slice";
    if !matches!(
        symbol.as_str(),
        "__intrinsic_string_len" | "__intrinsic_string_data" | "__intrinsic_string_slice"
    ) || sig.inputs.len() != if slice { 3 } else { 1 }
    {
        return None;
    }
    let TyKind::Reference(inner) = normalize_aliases(gcx, sig.inputs[0].ty).kind() else {
        return None;
    };
    if normalize_aliases(gcx, inner) != gcx.types.string {
        return None;
    }
    let output = normalize_aliases(gcx, sig.output);
    let valid = match symbol.as_str() {
        "__intrinsic_string_len" => output == gcx.types.uint,
        "__intrinsic_string_data" => {
            matches!(output.kind(), TyKind::Pointer(element, Mutability::Immutable) if normalize_aliases(gcx, element) == gcx.types.uint8)
        }
        _ => {
            gcx.definition_is_unsafe(id)
                && output == gcx.types.string
                && sig.inputs[1..]
                    .iter()
                    .all(|p| normalize_aliases(gcx, p.ty) == gcx.types.uint)
        }
    };
    valid.then_some(())
}

pub(crate) fn is_string_borrow(symbol: &str) -> bool {
    matches!(
        symbol,
        "__intrinsic_string_len" | "__intrinsic_string_data" | "__intrinsic_string_slice"
    )
}

/// Reference-address conversions preserve the exact pointee and mode.
pub(crate) fn is_reference_address(symbol: &str) -> bool {
    matches!(
        symbol,
        "__intrinsic_ref_to_ptr" | "__intrinsic_mut_ref_to_ptr"
    )
}

/// Only address calculations/layout queries: no memory reads, writes,
/// callbacks, retained owners or borrowed results. Raw pointer validity remains
/// the caller's obligation; this proof supplies no provenance or data authority.
pub(crate) fn is_pure_address(symbol: &str) -> bool {
    matches!(
        symbol,
        "__intrinsic_ptr_add"
            | "__intrinsic_ptr_sub"
            | "__intrinsic_ptr_offset"
            | "__intrinsic_ptr_byte_add"
            | "__intrinsic_ptr_byte_sub"
            | "__intrinsic_size_of"
            | "__intrinsic_align_of"
    )
}

fn pure_address_result(
    gcx: crate::compile::context::Gcx<'_>,
    id: crate::hir::DefinitionID,
) -> bool {
    use crate::{
        hir::Abi,
        sema::{
            models::{GenericParameterDefinitionKind, TyKind},
            tycheck::utils::normalize_aliases,
        },
    };
    let name = gcx.definition_ident(id).symbol;
    if !is_pure_address(name.as_str()) {
        return false;
    }
    let sig = gcx.get_signature(id);
    let generics = gcx.generics_of(id);
    // The native lowering reads type argument zero. Reject a declaration that
    // promises one pointee but causes codegen to use an unrelated type argument.
    if sig.abi != Some(Abi::Intrinsic)
        || sig.is_variadic
        || generics.parent.is_some()
        || generics.parent_count != 0
        || generics.parameters.len() != 1
        || generics.parameters[0].index != 0
        || !matches!(
            generics.parameters[0].kind,
            GenericParameterDefinitionKind::Type { .. }
        )
    {
        return false;
    }
    if matches!(
        name.as_str(),
        "__intrinsic_size_of" | "__intrinsic_align_of"
    ) {
        return sig.inputs.is_empty() && normalize_aliases(gcx, sig.output) == gcx.types.uint;
    }
    if sig.inputs.len() != 2 {
        return false;
    }
    let input = normalize_aliases(gcx, sig.inputs[0].ty);
    let TyKind::Pointer(element, _) = input.kind() else {
        return false;
    };
    matches!(normalize_aliases(gcx, element).kind(), TyKind::Parameter(parameter) if parameter.index == 0)
        && input == normalize_aliases(gcx, sig.output)
        && normalize_aliases(gcx, sig.inputs[1].ty)
            == if name.as_str() == "__intrinsic_ptr_offset" {
                gcx.types.int
            } else {
                gcx.types.uint
            }
}

/// Instantaneous field accesses copy a value out of, or store one into, a
/// class field within one runtime check. Only the handle slot is borrowed, and
/// only for the call, so the result never depends on an input.
pub(crate) fn is_class_field_access(name: &str) -> bool {
    matches!(
        name,
        "__intrinsic_class_field_reference"
            | "__intrinsic_class_field_read"
            | "__intrinsic_class_field_write"
            | "__intrinsic_class_field_modify"
    )
}

pub(crate) fn class_field_access_signature(
    gcx: crate::compile::context::Gcx<'_>,
    id: crate::hir::DefinitionID,
) -> bool {
    use crate::{
        hir::{Abi, StdItem},
        sema::models::{Constraint, TyKind},
    };
    let name = gcx.definition_ident(id).symbol;
    if !is_class_field_access(name.as_str()) {
        return false;
    }
    // write(slot, path, value) and modify(slot, path, op, rhs) store a value
    // of the field type; read(slot, path) returns one.
    let stored = match name.as_str() {
        "__intrinsic_class_field_write" => Some(2),
        "__intrinsic_class_field_modify" => Some(3),
        _ => None,
    };
    let signature = gcx.get_signature(id);
    let generics = gcx.generics_of(id);
    let field =
        |ty: crate::sema::models::Ty<'_>| matches!(ty.kind(), TyKind::Parameter(p) if p.index == 1);
    if !gcx.definition_is_unsafe(id)
        || signature.abi != Some(Abi::Intrinsic)
        || signature.is_variadic
        || signature.inputs.len() != stored.map_or(2, |index| index + 1)
        || generics.parent.is_some()
        || generics.parameters.len() != 2
        || signature.inputs[1..stored.unwrap_or(2)]
            .iter()
            .any(|input| input.ty != gcx.types.string)
        || !match stored {
            Some(index) => field(signature.inputs[index].ty) && signature.output == gcx.types.void,
            None if name.as_str() == "__intrinsic_class_field_reference" => {
                matches!(signature.output.kind(), TyKind::Reference(inner) if field(inner))
            }
            None => field(signature.output),
        }
    {
        return false;
    }
    let TyKind::Reference(class) = signature.inputs[0].ty.kind() else {
        return false;
    };
    matches!(class.kind(), TyKind::Parameter(p) if p.index == 0)
        && gcx.constraints_of(id).iter().any(|c| matches!(c.value,
            Constraint::Bound { ty, interface } if ty == class && gcx.std_item_def(StdItem::AnyObject) == Some(interface.id)))
}

pub(crate) fn is_class_handle_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "__intrinsic_class_owner"
            | "__intrinsic_class_from_owner"
            | "__intrinsic_class_from_handle"
    )
}

/// These unsafe class-pointer conversions require an explicit class-only bound.
pub(crate) fn class_handle_signature(
    gcx: crate::compile::context::Gcx<'_>,
    id: crate::hir::DefinitionID,
) -> bool {
    use crate::{
        hir::{Abi, Mutability, StdItem},
        sema::{
            models::{Constraint, GenericParameterDefinitionKind, TyKind},
            tycheck::utils::normalize_aliases,
        },
    };
    let signature = gcx.get_signature(id);
    let generics = gcx.generics_of(id);
    if !gcx.definition_is_unsafe(id)
        || signature.abi != Some(Abi::Intrinsic)
        || signature.is_variadic
        || signature.inputs.len() != 1
        || generics.parent.is_some()
        || generics.parent_count != 0
        || generics.parameters.len() != 1
        || generics.parameters[0].index != 0
        || !matches!(
            generics.parameters[0].kind,
            GenericParameterDefinitionKind::Type { .. }
        )
    {
        return false;
    }
    let input = normalize_aliases(gcx, signature.inputs[0].ty);
    let output = normalize_aliases(gcx, signature.output);
    let pointer = |ty: crate::sema::models::Ty<'_>| matches!(ty.kind(), TyKind::Pointer(element, Mutability::Immutable) if element == gcx.types.uint8);
    let parameter = if matches!(
        gcx.definition_ident(id).symbol.as_str(),
        "__intrinsic_class_owner"
    ) {
        let TyKind::Reference(parameter) = input.kind() else {
            return false;
        };
        if !pointer(output) {
            return false;
        }
        parameter
    } else {
        let valid_input = if gcx.definition_ident(id).symbol.as_str()
            == "__intrinsic_class_from_handle"
        {
            matches!(input.kind(), TyKind::Adt(definition, _) if gcx.std_item_def(crate::hir::StdItem::ClassHandle) == Some(definition.id))
        } else {
            pointer(input)
        };
        if !valid_input {
            return false;
        }
        output
    };
    matches!(parameter.kind(), TyKind::Parameter(parameter) if parameter.index == 0)
        && gcx.constraints_of(id).iter().any(|constraint| matches!(constraint.value,
            Constraint::Bound { ty, interface } if ty == parameter && gcx.std_item_def(StdItem::AnyObject) == Some(interface.id)))
}
