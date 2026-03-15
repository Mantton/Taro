//! Derive module for synthesizing interface method implementations.
//!
//! This module provides synthesis of interface methods for types that
//! declare conformance inline.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{
            GenericArgument, GenericArguments, MethodImplementation, MethodWitness,
            SyntheticMethodKind, Ty,
        },
        resolve::models::TypeHead,
    },
    span::Symbol,
};

/// Result of attempting to synthesize a method implementation.
#[derive(Debug)]
pub struct SynthesizedMethod<'ctx> {
    /// The witness entry for this synthesized method.
    pub witness: MethodWitness<'ctx>,
}

/// Information stored for later THIR generation of synthetic methods.
#[derive(Debug, Clone, Copy)]
pub struct SyntheticMethodInfo<'ctx> {
    pub kind: SyntheticMethodKind,
    pub self_ty: Ty<'ctx>,
    pub interface_id: DefinitionID,
    pub interface_args: GenericArguments<'ctx>,
    pub interface_bindings: &'ctx [crate::sema::models::AssociatedTypeBinding<'ctx>],
    pub method_id: DefinitionID,
    pub method_name: Symbol,
    pub syn_id: Option<DefinitionID>,
}

/// Attempt to synthesize an interface method for a given type.
///
/// This is called during conformance checking when no explicit implementation
/// is found for a required method. Returns `Some` if the method can be synthesized.
pub fn try_synthesize_method<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
) -> Option<SynthesizedMethod<'ctx>> {
    // Determine which standard interface this is
    let std_interface = get_std_interface(gcx, interface_id)?;

    // Only synthesize for derivable interfaces with methods
    if !std_interface.is_derivable() || std_interface.is_marker_only() {
        return None;
    }

    match std_interface {
        StdItem::Hashable => try_synthesize_hash(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
        ),
        StdItem::PartialEq | StdItem::Equatable => try_synthesize_partial_eq(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
        ),
        StdItem::Tuple => None,
        StdItem::Iterator | StdItem::Iterable => {
            // Iterator and Iterable are not auto-derivable
            None
        }
        // Operator interfaces are not auto-synthesized; they require explicit impl blocks
        StdItem::Fn
        | StdItem::AsyncFn
        | StdItem::Add
        | StdItem::Sub
        | StdItem::Mul
        | StdItem::Div
        | StdItem::Rem
        | StdItem::Neg
        | StdItem::Not
        | StdItem::BitAnd
        | StdItem::BitOr
        | StdItem::BitXor
        | StdItem::Shl
        | StdItem::Shr
        | StdItem::BitNot
        | StdItem::PartialOrd => None,
        _ => None,
    }
}

/// Get the StdItem variant for a given interface definition ID.
fn get_std_interface(gcx: Gcx<'_>, interface_id: DefinitionID) -> Option<StdItem> {
    for iface in StdItem::ALL_INTERFACES {
        if gcx.std_item_def(iface) == Some(interface_id) {
            return Some(iface);
        }
    }
    None
}

/// Try to synthesize Hashable.hash method.
fn try_synthesize_hash<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
) -> Option<SynthesizedMethod<'ctx>> {
    if !gcx.symbol_eq(&method_name, "hash") {
        return None;
    }

    let mut syn_id = None;
    if let Some(existing) = gcx.get_synthetic_method(type_head, method_id) {
        syn_id = existing.syn_id;
    }

    let info = SyntheticMethodInfo {
        kind: SyntheticMethodKind::MemberwiseHash,
        self_ty,
        interface_id,
        interface_args,
        interface_bindings: &[],
        method_id,
        method_name,
        syn_id,
    };
    gcx.register_synthetic_method(type_head, method_id, method_name, info);

    Some(SynthesizedMethod {
        witness: MethodWitness {
            implementation: MethodImplementation::Synthetic(
                SyntheticMethodKind::MemberwiseHash,
                syn_id,
            ),
            args_template,
        },
    })
}

/// Try to synthesize PartialEq.eq method.
fn try_synthesize_partial_eq<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
) -> Option<SynthesizedMethod<'ctx>> {
    if !gcx.symbol_eq(&method_name, "eq") {
        return None;
    }

    if let Some(GenericArgument::Const(_)) = interface_args.get(1) {
        return None;
    }

    let mut syn_id = None;
    if let Some(existing) = gcx.get_synthetic_method(type_head, method_id) {
        syn_id = existing.syn_id;
    }

    let info = SyntheticMethodInfo {
        kind: SyntheticMethodKind::MemberwiseEquality,
        self_ty,
        interface_id,
        interface_args,
        interface_bindings: &[],
        method_id,
        method_name,
        syn_id,
    };
    gcx.register_synthetic_method(type_head, method_id, method_name, info);

    Some(SynthesizedMethod {
        witness: MethodWitness {
            implementation: MethodImplementation::Synthetic(
                SyntheticMethodKind::MemberwiseEquality,
                syn_id,
            ),
            args_template,
        },
    })
}
