//! Derive module for synthesizing interface method implementations.
//!
//! This module provides synthesis of interface methods for types that
//! declare conformance inline.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{
            GenericArgument, GenericArguments, InterfaceReference, MethodImplementation,
            MethodWitness, SyntheticMethodKind, Ty, TyKind,
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

pub fn synthesize_property_field_accessor<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface: InterfaceReference<'ctx>,
    method_id: DefinitionID,
    kind: SyntheticMethodKind,
) -> MethodWitness<'ctx> {
    let args_template =
        crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(gcx, method_id);
    let existing = gcx.find_synthetic_method(type_head, method_id);
    let syn_id = existing.and_then(|info| info.syn_id);
    let info = SyntheticMethodInfo {
        kind,
        self_ty,
        interface_id: interface.id,
        interface_args: interface.arguments,
        interface_bindings: interface.bindings,
        method_id,
        method_name: gcx.definition_ident(method_id).symbol,
        syn_id,
    };
    if syn_id.is_none() {
        gcx.register_synthetic_method(type_head, method_id, info.method_name, info);
    }
    MethodWitness {
        implementation: MethodImplementation::Synthetic(kind, syn_id),
        args_template,
    }
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

    // Encoding observes an existing object and can use inherited virtual
    // families. Structural equality and fresh fixed-layout copies still need
    // a final class; they cannot promise a subclass's dynamic Self.
    if let Some(class) = gcx.class_info(self_ty) {
        if !class.is_final && !matches!(std_interface, StdItem::Encodable | StdItem::Decodable) {
            return None;
        }
        // Orderings and defaults are value recipes: structs and enums only.
        if is_value_only_derivation(std_interface) {
            return None;
        }
        if std_interface == StdItem::Hashable && !has_structural_equality(gcx, self_ty) {
            return None;
        }
    }

    // Only synthesize for derivable interfaces with methods
    if !std_interface.is_derivable() || std_interface.is_marker_only() {
        return None;
    }

    match std_interface {
        StdItem::Clone => try_synthesize_clone(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
        ),
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
        StdItem::Encodable | StdItem::Decodable => try_synthesize_codec(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
            std_interface,
        ),
        StdItem::PartialOrd => try_synthesize_order(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
            StdItem::PartialOrd,
        ),
        StdItem::Ord => try_synthesize_order(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
            StdItem::Ord,
        ),
        StdItem::Default => try_synthesize_default(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
        ),
        StdItem::Debug => try_synthesize_debug(
            gcx,
            type_head,
            self_ty,
            interface_id,
            interface_args,
            method_name,
            method_id,
            args_template,
        ),
        StdItem::RawValue | StdItem::CaseIterable => {
            let TypeHead::Nominal(owner) = type_head else {
                return None;
            };
            if enum_derivation_obstacle(gcx, owner, std_interface, interface_args).is_some() {
                return None;
            }
            let requirements = gcx.get_interface_requirements(interface_id)?;
            let kind = if requirements
                .properties
                .iter()
                .any(|p| p.getter_id == method_id)
            {
                if std_interface == StdItem::CaseIterable {
                    SyntheticMethodKind::EnumCaseName
                } else {
                    SyntheticMethodKind::EnumRawValue
                }
            } else if std_interface == StdItem::CaseIterable && gcx.symbol_eq(method_name, "caseAt")
            {
                SyntheticMethodKind::EnumCaseAt
            } else if std_interface == StdItem::RawValue && gcx.symbol_eq(method_name, "from") {
                SyntheticMethodKind::EnumFromRawValue
            } else {
                return None;
            };
            Some(register_synthesized(
                gcx,
                type_head,
                self_ty,
                interface_id,
                interface_args,
                method_name,
                method_id,
                args_template,
                kind,
            ))
        }
        StdItem::Tuple => None,
        StdItem::Iterator | StdItem::Iterable | StdItem::AsyncIterator | StdItem::AsyncIterable => {
            // Iterator-like interfaces are not auto-derivable
            None
        }
        // Operator interfaces are not auto-synthesized; they require explicit impl blocks
        StdItem::Fn
        | StdItem::AsyncFn
        | StdItem::Add
        | StdItem::AddAssign
        | StdItem::Sub
        | StdItem::SubAssign
        | StdItem::Mul
        | StdItem::MulAssign
        | StdItem::Div
        | StdItem::DivAssign
        | StdItem::Rem
        | StdItem::RemAssign
        | StdItem::Neg
        | StdItem::Not
        | StdItem::BitAnd
        | StdItem::BitAndAssign
        | StdItem::BitOr
        | StdItem::BitOrAssign
        | StdItem::BitXor
        | StdItem::BitXorAssign
        | StdItem::Shl
        | StdItem::ShlAssign
        | StdItem::Shr
        | StdItem::ShrAssign
        | StdItem::BitNot
        | StdItem::Contains => None,
        _ => None,
    }
}

/// Hash synthesis must use exactly the equality recipe, never guess which
/// fields a custom equality implementation considers significant.
fn has_structural_equality<'ctx>(gcx: Gcx<'ctx>, self_ty: Ty<'ctx>) -> bool {
    let Some(id) = gcx.std_item_def(StdItem::PartialEq) else {
        return false;
    };
    let interface = InterfaceReference {
        id,
        arguments: gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(self_ty),
            GenericArgument::Type(self_ty),
        ]),
        bindings: &[],
    };
    let Some(requirements) = gcx.get_interface_requirements(id) else {
        return false;
    };
    let Some(requirement) = requirements
        .methods
        .iter()
        .find(|method| gcx.symbol_text(method.name).as_str() == "eq")
    else {
        return false;
    };
    if let Some(witness) = super::resolve_conformance_witness(gcx, interface) {
        return witness
            .method_witnesses
            .get(&requirement.id)
            .is_some_and(|method| {
                matches!(
                    method.implementation,
                    MethodImplementation::Synthetic(SyntheticMethodKind::MemberwiseEquality, _)
                )
            });
    }
    // At a generic declaration, component obligations are conditional rather
    // than assumptions on every instantiation. Inspect the declared recipe
    // without asserting those obligations now; ordinary conformance selection
    // still proves them for every concrete use. Explicit equality wins here as
    // in normal witness lookup, including an implementation in an extend block.
    let crate::sema::models::TyKind::Adt(definition, _) = self_ty.kind() else {
        return false;
    };
    if !self_ty.needs_instantiation() {
        return false;
    }
    gcx.conformance_records_for_interface(definition.id.package(), id)
        .into_iter()
        .filter(|record| {
            record.is_inline
                && record.interface.self_ty() == Some(self_ty)
                && equality_rhs(gcx, record.interface.arguments, self_ty) == Some(self_ty)
        })
        .any(|record| {
            crate::sema::impl_engine::find_method_witness(
                gcx,
                record.target,
                requirement,
                &record,
                GenericArguments::empty(),
                &Default::default(),
            )
            .is_some_and(|method| {
                matches!(
                    method.implementation,
                    MethodImplementation::Synthetic(SyntheticMethodKind::MemberwiseEquality, _)
                )
            })
        })
}

/// Both enum derivations require unit cases. RawValue also checks that each
/// source discriminant fits the selected integer representation.
pub(crate) fn enum_derivation_obstacle<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    interface: StdItem,
    arguments: GenericArguments<'ctx>,
) -> Option<(String, crate::span::Span)> {
    let name = interface.name_str()?;
    let ident = gcx.definition_ident(owner);
    let Some(definition) = gcx.try_get_enum_definition(owner) else {
        return Some((
            format!("only payload-free enums can derive {name}"),
            ident.span,
        ));
    };
    let raw_layout = if interface == StdItem::RawValue {
        let raw = crate::sema::tycheck::utils::normalize_aliases(gcx, arguments.get(1)?.ty()?);
        let Some(layout) = crate::sema::tycheck::utils::const_eval::integer_layout(gcx, raw) else {
            return Some((
                format!(
                    "cannot derive RawValue for raw type '{}'; expected an integer type",
                    raw.format(gcx)
                ),
                ident.span,
            ));
        };
        Some((raw, layout))
    } else {
        None
    };
    for variant in definition.variants {
        let problem = if !matches!(variant.kind, crate::sema::models::EnumVariantKind::Unit) {
            format!(
                "cannot derive {name} for case '{}' with a payload",
                gcx.symbol_text(variant.name).as_str()
            )
        } else if let Some((raw, layout)) = raw_layout
            && !layout.contains(i128::from(variant.discriminant))
        {
            format!(
                "enum discriminant {} is out of range for raw type '{}'",
                variant.discriminant,
                raw.format(gcx)
            )
        } else {
            continue;
        };
        return Some((problem, gcx.definition_ident(variant.def_id).span));
    }
    None
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

/// Codec derivation follows stored struct fields and enum payloads.
/// Explicit witnesses are selected before this fallback. Initializers and
/// stored defaults are not executed: declaring the conformance opts in to
/// fieldwise construction, and missing required fields remain errors.
fn try_synthesize_codec<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
    capability: StdItem,
) -> Option<SynthesizedMethod<'ctx>> {
    let TypeHead::Nominal(owner) = type_head else {
        return None;
    };
    let expected = if capability == StdItem::Encodable {
        "encode"
    } else {
        "decode"
    };
    if (gcx.try_get_struct_definition(owner).is_none()
        && gcx.try_get_enum_definition(owner).is_none())
        || !gcx.symbol_eq(method_name, expected)
        || (!gcx.is_class_type(self_ty)
            || capability != StdItem::Decodable
            || crate::sema::lowering::class_codable::manual_initializer(gcx, self_ty, method_id)
                .is_none())
            && (!all_fields_implement(gcx, type_head, capability)
                || !codec_field_metadata_obstacles(gcx, owner, capability).is_empty())
    {
        return None;
    }
    if gcx.is_class_type(self_ty)
        && capability == StdItem::Decodable
        && gcx
            .result_parts(gcx.get_signature(method_id).output)
            .is_none()
    {
        return None;
    }
    let kind = if capability == StdItem::Encodable {
        SyntheticMethodKind::MemberwiseEncode
    } else {
        SyntheticMethodKind::MemberwiseDecode
    };
    let existing = gcx.find_synthetic_method(type_head, method_id);
    let syn_id = existing.and_then(|info| info.syn_id).or_else(|| {
        gcx.is_class_type(self_ty)
            .then(|| gcx.allocate_synthetic_id(gcx.package_index()))
    });
    if existing.is_none() {
        let info = SyntheticMethodInfo {
            kind,
            self_ty,
            interface_id,
            interface_args,
            interface_bindings: &[],
            method_id,
            method_name,
            syn_id,
        };
        // Class virtual catalogs are built before THIR bodies. Publish the
        // callable identity now, so derived encoders participate in exactly
        // the same inherited/overridden generic families as source methods.
        if let Some(id) = syn_id {
            crate::thir::synthesize::register_definition(gcx, id, type_head, info);
        }
        gcx.register_synthetic_method(type_head, method_id, method_name, info);
    }
    Some(SynthesizedMethod {
        witness: MethodWitness {
            implementation: MethodImplementation::Synthetic(kind, syn_id),
            args_template,
        },
    })
}

/// Try to synthesize Clone.clone method.
fn try_synthesize_clone<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
) -> Option<SynthesizedMethod<'ctx>> {
    if !gcx.symbol_eq(&method_name, "clone") {
        return None;
    }

    let kind = if crate::sema::impl_engine::builtin_copy_clone(gcx, self_ty) {
        SyntheticMethodKind::CopyClone
    } else {
        if !all_fields_implement_clone(gcx, type_head) {
            return None;
        }
        SyntheticMethodKind::MemberwiseClone
    };

    let existing = gcx.find_synthetic_method(type_head, method_id);
    let syn_id = existing.and_then(|info| info.syn_id);

    let info = SyntheticMethodInfo {
        kind,
        self_ty,
        interface_id,
        interface_args,
        interface_bindings: &[],
        method_id,
        method_name,
        syn_id,
    };
    if existing.is_none() {
        gcx.register_synthetic_method(type_head, method_id, method_name, info);
    }

    Some(SynthesizedMethod {
        witness: MethodWitness {
            implementation: MethodImplementation::Synthetic(kind, syn_id),
            args_template,
        },
    })
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
    if !gcx.symbol_eq(&method_name, "hash")
        || !all_fields_implement(gcx, type_head, StdItem::Hashable)
    {
        return None;
    }

    let existing = gcx.find_synthetic_method(type_head, method_id);
    let syn_id = existing.and_then(|info| info.syn_id);

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
    if existing.is_none() {
        gcx.register_synthetic_method(type_head, method_id, method_name, info);
    }

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

    if equality_rhs(gcx, interface_args, self_ty)?
        != crate::sema::tycheck::utils::normalize_aliases(gcx, self_ty)
        || !all_fields_implement(gcx, type_head, StdItem::PartialEq)
    {
        return None;
    }

    let existing = gcx.find_synthetic_method(type_head, method_id);
    let syn_id = existing.and_then(|info| info.syn_id);

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
    if existing.is_none() {
        gcx.register_synthetic_method(type_head, method_id, method_name, info);
    }

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

/// Interfaces whose derivation builds, compares or prints plain values. They
/// are never synthesized for classes (a derived `Debug` could recurse forever
/// through a reference cycle), and `Default` is never synthesized for enums.
pub(crate) fn is_value_only_derivation(item: StdItem) -> bool {
    matches!(
        item,
        StdItem::PartialOrd | StdItem::Ord | StdItem::Default | StdItem::Debug
    )
}

/// Publish a synthesized witness for `kind`, reusing an earlier registration.
fn register_synthesized<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
    kind: SyntheticMethodKind,
) -> SynthesizedMethod<'ctx> {
    let existing = gcx.find_synthetic_method(type_head, method_id);
    let syn_id = existing.and_then(|info| info.syn_id);
    if existing.is_none() {
        let info = SyntheticMethodInfo {
            kind,
            self_ty,
            interface_id,
            interface_args,
            interface_bindings: &[],
            method_id,
            method_name,
            syn_id,
        };
        gcx.register_synthetic_method(type_head, method_id, method_name, info);
    }
    SynthesizedMethod {
        witness: MethodWitness {
            implementation: MethodImplementation::Synthetic(kind, syn_id),
            args_template,
        },
    }
}

/// `PartialOrd.partialCmp` and `Ord.cmp` compare stored fields (or enum cases,
/// then payloads) in declaration order. Super-interfaces are not synthesized
/// here: conformance checking requires them to be declared separately.
fn try_synthesize_order<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
    capability: StdItem,
) -> Option<SynthesizedMethod<'ctx>> {
    let TypeHead::Nominal(owner) = type_head else {
        return None;
    };
    let (expected, kind) = if capability == StdItem::PartialOrd {
        ("partialCmp", SyntheticMethodKind::MemberwisePartialOrder)
    } else {
        ("cmp", SyntheticMethodKind::MemberwiseTotalOrder)
    };
    if !gcx.symbol_eq(method_name, expected)
        || gcx.is_class_type(self_ty)
        || (gcx.try_get_struct_definition(owner).is_none()
            && gcx.try_get_enum_definition(owner).is_none())
    {
        return None;
    }
    if capability == StdItem::PartialOrd
        && equality_rhs(gcx, interface_args, self_ty)?
            != crate::sema::tycheck::utils::normalize_aliases(gcx, self_ty)
    {
        return None;
    }
    if !all_fields_implement(gcx, type_head, capability) {
        return None;
    }
    Some(register_synthesized(
        gcx,
        type_head,
        self_ty,
        interface_id,
        interface_args,
        method_name,
        method_id,
        args_template,
        kind,
    ))
}

/// `Default.default` builds a struct from each field's declared default
/// expression, or else from the field type's own `Default`. Initializers are
/// not run, as for derived `Clone` and `Decodable`.
fn try_synthesize_default<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
) -> Option<SynthesizedMethod<'ctx>> {
    let TypeHead::Nominal(owner) = type_head else {
        return None;
    };
    if !gcx.symbol_eq(method_name, "default")
        || gcx.is_class_type(self_ty)
        || gcx.try_get_struct_definition(owner).is_none()
        || !all_fields_implement(gcx, type_head, StdItem::Default)
    {
        return None;
    }
    Some(register_synthesized(
        gcx,
        type_head,
        self_ty,
        interface_id,
        interface_args,
        method_name,
        method_id,
        args_template,
        SyntheticMethodKind::MemberwiseDefault,
    ))
}

/// `Debug.debug` writes a struct's name and fields, or an enum value's case
/// name and payload, each component through its own `debug`.
fn try_synthesize_debug<'ctx>(
    gcx: Gcx<'ctx>,
    type_head: TypeHead,
    self_ty: Ty<'ctx>,
    interface_id: DefinitionID,
    interface_args: GenericArguments<'ctx>,
    method_name: Symbol,
    method_id: DefinitionID,
    args_template: GenericArguments<'ctx>,
) -> Option<SynthesizedMethod<'ctx>> {
    let TypeHead::Nominal(owner) = type_head else {
        return None;
    };
    if !gcx.symbol_eq(method_name, "debug")
        || gcx.is_class_type(self_ty)
        || (gcx.try_get_struct_definition(owner).is_none()
            && gcx.try_get_enum_definition(owner).is_none())
        || !all_fields_implement(gcx, type_head, StdItem::Debug)
    {
        return None;
    }
    Some(register_synthesized(
        gcx,
        type_head,
        self_ty,
        interface_id,
        interface_args,
        method_name,
        method_id,
        args_template,
        SyntheticMethodKind::MemberwiseDebug,
    ))
}

/// Resolve a derivation's RHS without mistaking an arbitrary generic parameter
/// for Self. Cross-type equality is supported through explicit implementations.
pub(crate) fn equality_rhs<'ctx>(
    gcx: Gcx<'ctx>,
    arguments: GenericArguments<'ctx>,
    self_ty: Ty<'ctx>,
) -> Option<Ty<'ctx>> {
    let rhs = match arguments.get(1) {
        Some(GenericArgument::Type(ty)) if *ty == gcx.types.self_type_parameter => self_ty,
        Some(GenericArgument::Type(ty)) => *ty,
        Some(GenericArgument::Const(_)) => return None,
        None => self_ty,
    };
    Some(crate::sema::tycheck::utils::normalize_aliases(gcx, rhs))
}

/// A newly adopted class codec describes this level's own stored fields.
/// Inherited conformance continues to use its original declaration's methods.
pub(crate) fn codec_field_offset<'ctx>(gcx: Gcx<'ctx>, class: Ty<'ctx>) -> usize {
    gcx.class_base(class)
        .and_then(|base| match base.kind() {
            TyKind::Adt(definition, _) => {
                Some(gcx.get_struct_definition(definition.id).fields.len())
            }
            _ => None,
        })
        .unwrap_or(0)
}

fn stored_fields<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    capability: StdItem,
) -> Option<Vec<Ty<'ctx>>> {
    Some(
        stored_field_entries(gcx, owner, capability)?
            .into_iter()
            .map(|(_, ty)| ty)
            .collect(),
    )
}

/// The components a derivation of `capability` uses, named for diagnostics:
/// a struct field by its name, an enum payload as `case.label` or `case.index`.
/// A derived `Default` uses only the fields without a declared default, and
/// is never synthesized for an enum.
fn stored_field_entries<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    capability: StdItem,
) -> Option<Vec<(String, Ty<'ctx>)>> {
    if let Some(definition) = gcx.try_get_struct_definition(owner) {
        let skip = if matches!(capability, StdItem::Encodable | StdItem::Decodable) {
            codec_field_offset(gcx, gcx.get_type(owner))
        } else {
            0
        };
        return Some(
            definition.fields[skip..]
                .iter()
                .filter(|field| {
                    if capability == StdItem::Default {
                        field.default_provider.is_none()
                    } else if matches!(capability, StdItem::Encodable | StdItem::Decodable) {
                        !field.coding_skip
                    } else {
                        true
                    }
                })
                .map(|field| (gcx.symbol_text(field.name).to_string(), field.ty))
                .collect(),
        );
    }
    if capability == StdItem::Default {
        return None;
    }
    let definition = gcx.try_get_enum_definition(owner)?;
    Some(
        definition
            .variants
            .iter()
            .flat_map(|variant| {
                let fields = match variant.kind {
                    crate::sema::models::EnumVariantKind::Unit => &[][..],
                    crate::sema::models::EnumVariantKind::Tuple(fields)
                    | crate::sema::models::EnumVariantKind::Struct(fields) => fields,
                };
                fields.iter().enumerate().map(move |(index, field)| {
                    let case = gcx.symbol_text(variant.name);
                    let name = match field.label {
                        Some(label) => format!("{case}.{}", gcx.symbol_text(label)),
                        None => format!("{case}.{index}"),
                    };
                    (name, field.ty)
                })
            })
            .collect(),
    )
}

fn all_fields_implement_clone(gcx: Gcx<'_>, head: TypeHead) -> bool {
    all_fields_implement(gcx, head, StdItem::Clone)
}

/// A derivation can keep generic component calls abstract: conditional
/// selection checks their substituted obligations before the body is used.
fn all_fields_implement(gcx: Gcx<'_>, head: TypeHead, capability: StdItem) -> bool {
    nonconforming_fields(gcx, head, capability).is_some_and(|fields| fields.is_empty())
}

/// The named components that cannot prove `capability`. Components that
/// depend on a generic parameter are left to conditional selection. `None`
/// means the type has no derivable shape for the capability at all.
fn nonconforming_fields<'ctx>(
    gcx: Gcx<'ctx>,
    head: TypeHead,
    capability: StdItem,
) -> Option<Vec<(String, Ty<'ctx>)>> {
    let TypeHead::Nominal(owner) = head else {
        return None;
    };
    let interface_id = gcx.std_item_def(capability)?;
    let fields = stored_field_entries(gcx, owner, capability)?;
    let constraints: Vec<_> = gcx
        .canonical_constraints_of(owner)
        .iter()
        .map(|bound| bound.value)
        .collect();
    let param_env = gcx.store.arenas.global.alloc_slice_copy(&constraints);
    let environment = crate::sema::tycheck::utils::ParamEnv::new(constraints);
    let icx = std::rc::Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));
    Some(
        fields
            .into_iter()
            .filter(|(_, field)| {
                if !gcx.generics_of(owner).is_empty() && field.needs_instantiation() {
                    return false;
                }
                let field =
                    crate::sema::tycheck::utils::normalize_ty(icx.clone(), *field, &environment);
                let goal = crate::sema::models::InterfaceGoal {
                    interface_id,
                    self_ty: field,
                    interface_args: component_interface_arguments(gcx, interface_id, field),
                    bindings: &[],
                    param_env,
                };
                gcx.prove_interface_goal(goal, crate::sema::models::SelectionMode::Typecheck)
                    != crate::sema::models::GoalResult::Proven
            })
            .collect(),
    )
}

/// A derived component obligation compares a component with itself, so the
/// `Rhs` of `PartialEq` and `PartialOrd` is the component type.
pub(crate) fn component_interface_arguments<'ctx>(
    gcx: Gcx<'ctx>,
    interface_id: DefinitionID,
    component: Ty<'ctx>,
) -> GenericArguments<'ctx> {
    if [StdItem::PartialEq, StdItem::PartialOrd]
        .iter()
        .any(|item| gcx.std_item_def(*item) == Some(interface_id))
    {
        gcx.store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(component)])
    } else {
        GenericArguments::empty()
    }
}

pub(crate) fn codec_field_metadata_obstacles<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    capability: StdItem,
) -> Vec<String> {
    let Some(definition) = gcx.try_get_struct_definition(owner) else {
        return Vec::new();
    };
    let self_ty = gcx.get_type(owner);
    let offset = codec_field_offset(gcx, self_ty);
    let fields = &definition.fields[offset..];
    let type_name = TypeHead::Nominal(owner).format(gcx);
    let mut obstacles = Vec::new();

    let mut seen_keys: rustc_hash::FxHashMap<Symbol, Symbol> = rustc_hash::FxHashMap::default();
    for field in fields {
        if field.coding_skip {
            continue;
        }
        let effective_key = field.coding_key.unwrap_or(field.name);
        if let Some(&first_field) = seen_keys.get(&effective_key) {
            obstacles.push(format!(
                "duplicate coding key \"{}\" on type '{type_name}' (fields '{}' and '{}' map to the same key)",
                gcx.symbol_text(effective_key),
                gcx.symbol_text(first_field),
                gcx.symbol_text(field.name),
            ));
        } else {
            seen_keys.insert(effective_key, field.name);
        }
    }

    if capability == StdItem::Decodable {
        let optional_id = gcx.std_item_def(StdItem::Optional);
        let default_id = gcx.std_item_def(StdItem::Default);
        let constraints: Vec<_> = gcx
            .canonical_constraints_of(owner)
            .iter()
            .map(|bound| bound.value)
            .collect();
        let param_env = gcx.store.arenas.global.alloc_slice_copy(&constraints);
        let environment = crate::sema::tycheck::utils::ParamEnv::new(constraints);
        let icx = std::rc::Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));

        for field in fields {
            if !field.coding_skip {
                continue;
            }
            if field.default_provider.is_some() {
                continue;
            }
            let normalized =
                crate::sema::tycheck::utils::normalize_ty(icx.clone(), field.ty, &environment);
            if optional_id.is_some_and(|opt| {
                matches!(normalized.kind(), TyKind::Adt(def, _) if def.id == opt)
            }) {
                continue;
            }
            let has_default = default_id.is_some_and(|interface_id| {
                let goal = crate::sema::models::InterfaceGoal {
                    interface_id,
                    self_ty: normalized,
                    interface_args: GenericArguments::empty(),
                    bindings: &[],
                    param_env,
                };
                gcx.prove_interface_goal(goal, crate::sema::models::SelectionMode::Typecheck)
                    == crate::sema::models::GoalResult::Proven
            });
            if !has_default {
                obstacles.push(format!(
                    "`@skip` field '{}' on type '{type_name}' requires a default value, an Optional type, or Default conformance to derive 'Decodable'",
                    gcx.symbol_text(field.name),
                ));
            }
        }
    }

    obstacles
}

/// Explain why an inline `PartialEq`, `Hashable`, `Clone`, `PartialOrd`,
/// `Ord`, `Default` or `Debug` cannot be derived for the record's type: the
/// type's kind, or every component that lacks the interface. Empty when
/// nothing stands in the way, or for other interfaces.
pub(crate) fn derive_obstacles<'ctx>(
    gcx: Gcx<'ctx>,
    record: crate::sema::models::ConformanceRecord<'ctx>,
) -> Vec<String> {
    let Some(capability) = get_std_interface(gcx, record.interface.id) else {
        return Vec::new();
    };
    if record.is_inline && matches!(capability, StdItem::Encodable | StdItem::Decodable) {
        let TypeHead::Nominal(owner) = record.target else {
            return Vec::new();
        };
        let self_ty = gcx.get_type(owner);
        if gcx.is_class_type(self_ty)
            && capability == StdItem::Decodable
            && let Some(reqs) = gcx.get_interface_requirements(record.interface.id)
            && let Some(decode_method) = reqs
                .methods
                .iter()
                .find(|method| gcx.symbol_eq(method.name, "decode"))
            && crate::sema::lowering::class_codable::manual_initializer(
                gcx,
                self_ty,
                decode_method.id,
            )
            .is_some()
        {
            return Vec::new();
        }
        return codec_field_metadata_obstacles(gcx, owner, capability);
    }
    let memberwise = matches!(
        capability,
        StdItem::PartialEq | StdItem::Hashable | StdItem::Clone
    );
    if !record.is_inline || !(memberwise || is_value_only_derivation(capability)) {
        return Vec::new();
    }
    let TypeHead::Nominal(owner) = record.target else {
        return Vec::new();
    };
    let interface = capability.name_str().unwrap_or_default();
    let type_name = record.target.format(gcx);
    let self_ty = gcx.get_type(owner);
    if is_value_only_derivation(capability) && gcx.is_class_type(self_ty) {
        let kinds = if capability == StdItem::Default {
            "structs"
        } else {
            "structs and enums"
        };
        return vec![format!(
            "cannot derive '{interface}' for class '{type_name}': only {kinds} can derive it; implement it in a conformance instead"
        )];
    }
    if capability == StdItem::Default && gcx.try_get_enum_definition(owner).is_some() {
        return vec![format!(
            "cannot derive 'Default' for enum '{type_name}': enums have no synthesized default; implement 'static func default() -> Self' in a conformance instead"
        )];
    }
    let Some(fields) = nonconforming_fields(gcx, record.target, capability) else {
        return Vec::new();
    };
    fields
        .into_iter()
        .map(|(field, ty)| {
            let ty = ty.format(gcx);
            if capability == StdItem::Default {
                format!(
                    "cannot derive 'Default' for '{type_name}': field '{field}' has no default value and its type '{ty}' does not conform to 'Default'"
                )
            } else {
                format!(
                    "cannot derive '{interface}' for '{type_name}': field '{field}' has type '{ty}', which does not conform to '{interface}'"
                )
            }
        })
        .collect()
}

/// Stored components that condition an inline generic value derivation.
/// These obligations belong to the conformance, never the owning type's
/// parameter environment, so e.g. Wrapper[Plain] remains a valid type.
pub(crate) fn conditional_fields<'ctx>(
    gcx: Gcx<'ctx>,
    record: crate::sema::models::ConformanceRecord<'ctx>,
) -> Option<Vec<Ty<'ctx>>> {
    if !record.is_inline
        || gcx.generics_of(record.extension).is_empty()
        || !get_std_interface(gcx, record.interface.id).is_some_and(StdItem::is_derivable)
    {
        return None;
    }
    let TypeHead::Nominal(id) = record.target else {
        return None;
    };
    // Equatable has no own methods: its actual PartialEq super-conformance
    // supplies equality, including a valid manual implementation.
    if [StdItem::Equatable, StdItem::RawValue, StdItem::CaseIterable]
        .iter()
        .any(|&item| gcx.std_item_def(item) == Some(record.interface.id))
    {
        return Some(Vec::new());
    }
    if gcx.is_class_type(gcx.get_type(id))
        && gcx.std_item_def(StdItem::Decodable) == Some(record.interface.id)
        && let Some(method) = gcx
            .get_interface_requirements(record.interface.id)
            .and_then(|requirements| requirements.methods.first())
        && crate::sema::lowering::class_codable::manual_initializer(
            gcx,
            gcx.get_type(id),
            method.id,
        )
        .is_some()
    {
        return Some(vec![]);
    }
    let capability = get_std_interface(gcx, record.interface.id)?;
    if gcx.store.collecting_constant_headers.get()
        && let Some(components) = super::collect::adt::derived_fields(gcx, id, capability)
    {
        return Some(components);
    }
    stored_fields(gcx, id, capability)
}

#[cfg(test)]
mod tests {
    use crate::{hir::StdItem, test_support::analyze_language_item_script};

    fn codec_diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        analyze_language_item_script(
            &format!(
                r#"
interface Encodable {{ func encode[E](_ encoder: E); }}
interface Decodable {{ static func decode[D](_ decoder: D) -> Self; }}
type Codable = Encodable & Decodable
conform int32 to Encodable {{
func encode[E](_ encoder: E) {{}}
}}
conform int32 to Decodable {{
static func decode[D](_ decoder: D) -> int32 {{ 0 }}
}}
{body}
func main() {{}}
"#
            ),
            false,
            &[
                (StdItem::Encodable, "Encodable"),
                (StdItem::Decodable, "Decodable"),
            ],
        )
    }

    #[test]
    fn codable_alias_derives_both_struct_directions() {
        let errors =
            codec_diagnostics("struct Person: Codable { age: int32 }\nstruct Empty: Codable {}");
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn codec_derivation_requires_codable_fields_and_result_based_class_decoding() {
        for body in [
            "struct Plain {}\nstruct Record: Codable { value: Plain }",
            "struct Plain {}\nenum Choice: Codable { case value(Plain) }",
            // This test protocol returns bare Self; class construction needs
            // the production Result-based decoding contract instead.
            "final class Object: Codable { value: int32 }",
        ] {
            let errors = codec_diagnostics(body);
            assert!(!errors.is_empty(), "unexpected derivation for {body}");
        }
    }

    #[test]
    fn class_encoders_can_be_derived_and_inherited_without_final() {
        let errors = codec_diagnostics(
            "class Base[T]: Encodable { value: T }\nclass Child: Base[int32] { extra: int32 = 7 }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = codec_diagnostics(
            "struct Plain {}\nclass Base { ignored: Plain }\nfinal class Child: Base, Encodable { value: int32 }",
        );
        assert!(
            errors.is_empty(),
            "nonconforming base storage is not part of a newly adopted encoder: {errors:#?}"
        );
    }

    #[test]
    fn codec_derivation_supports_all_enum_payload_shapes() {
        let errors = codec_diagnostics(
            "enum Choice: Codable { case unit; case tuple(int32); case labeled(value: int32); case record { value: int32 }; case empty {} }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn generic_enum_codec_conformance_checks_every_payload() {
        let declarations = "enum Choice[T]: Codable { case unit; case item(T); case record { value: T } }\nstruct Plain {}\nfunc needs[T: Codable](_ value: T) {}\n";
        let errors = codec_diagnostics(&format!(
            "{declarations}func test(_ value: Choice[int32]) {{ needs(value) }}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = codec_diagnostics(&format!(
            "{declarations}func test(_ value: Choice[Plain]) {{ needs(value) }}"
        ));
        assert!(
            !errors.is_empty(),
            "an inactive noncodable payload must still reject derivation"
        );
    }

    #[test]
    fn generic_codec_conformance_is_conditional_on_fields() {
        let errors = codec_diagnostics(
            "struct Box[T]: Codable { value: T }\nstruct Plain {}\nfunc needs[T: Codable](_ value: T) {}\nfunc test() { needs(Box[int32] { value: 1 }) }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = codec_diagnostics(
            "struct Box[T]: Codable { value: T }\nstruct Plain {}\nfunc needs[T: Codable](_ value: T) {}\nfunc test() { needs(Box[Plain] { value: Plain {} }) }",
        );
        assert!(
            !errors.is_empty(),
            "noncodable field must not claim generic conformance"
        );
    }

    #[test]
    fn recursive_codec_fields_do_not_prove_unrelated_leaves_or_where_cycles() {
        let declarations = "struct Link[T] {}\nconform[T: Encodable] Link[T] to Encodable {\nfunc encode[E](_ encoder: E) {}\n}\nstruct Chain[T]: Encodable { next: Link[Chain[T]]; value: T; }\nstruct Plain {}\nfunc wants[T: Encodable](_ value: T) {}\n";
        let errors = codec_diagnostics(&format!(
            "{declarations}func test(_ value: Chain[int32]) {{ wants(value) }}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = codec_diagnostics(&format!(
            "{declarations}func test(_ value: Chain[Plain], _ link: Link[Chain[Plain]]) {{ wants(value); wants(link); }}"
        ));
        assert!(
            errors.len() >= 2,
            "a recursive assumption must not leak to unrelated leaves: {errors:#?}"
        );
        let errors = codec_diagnostics(
            "struct Circle[T] {}\nconform[T] Circle[T] to Encodable where Circle[T]: Encodable {\nfunc encode[E](_ encoder: E) {}\n}\nfunc wants[T: Encodable](_ value: T) {}\nfunc test(_ value: Circle[int32]) { wants(value) }",
        );
        assert!(
            !errors.is_empty(),
            "an ordinary self-dependent where clause is not a proof"
        );
    }

    fn diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        analyze_language_item_script(
            &format!("interface Clone {{\nfunc clone() -> Self\n}}\n{body}\nfunc main() {{}}\n"),
            true,
            &[(StdItem::Clone, "Clone")],
        )
    }

    fn class_clone_diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        analyze_language_item_script(
            &format!("interface Clone {{ func clone() -> Self; }}\n{body}\nfunc main() {{}}"),
            false,
            &[(StdItem::Clone, "Clone")],
        )
    }

    #[test]
    fn final_class_clone_is_structural_and_requires_every_component() {
        let errors = class_clone_diagnostics("final class Empty: Clone {}");
        assert!(errors.is_empty(), "{errors:#?}");
        for source in [
            "class Open: Clone {}",
            "struct Plain {}\nfinal class Container: Clone { value: Plain }",
        ] {
            let errors = class_clone_diagnostics(source);
            assert!(
                errors.iter().any(|error| error.message.contains("Clone")
                    || error.message.contains("checked witness")),
                "{source}: {errors:#?}"
            );
        }
    }

    #[test]
    fn values_do_not_prove_clone_implicitly() {
        let errors = diagnostics(
            "struct Plain { value: int32 }\nfunc needsClone[T: Clone](_ value: &T) {}\nfunc test() { value := Plain { value: 1 }; needsClone(&value) }",
        );
        assert!(
            errors.iter().any(|error| error.message.contains("Clone")),
            "{errors:?}"
        );
    }

    #[test]
    fn field_without_clone_cannot_derive_clone() {
        let errors =
            diagnostics("struct Plain { value: int32 }\nstruct Container: Clone { value: Plain }");
        assert!(
            errors.iter().any(|error| error.message.contains("Clone")),
            "{errors:?}"
        );
    }

    #[test]
    fn explicit_component_clone_is_not_ambiguous() {
        let errors = diagnostics(
            "struct Component { value: int32 }\nconform Component to Clone {\nfunc clone() -> Component { Component { value: self.value + 1 } }\n}\nstruct Container: Clone { value: Component }\nfunc test() { value := Container { value: Component { value: 1 } }; cloned := value.clone() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn bounded_generic_field_can_derive_clone() {
        let errors = diagnostics(
            "struct Container[T: Clone]: Clone { value: T }\nfunc test() { value := Container[int32] { value: 1 }; cloned := value.clone() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }
    #[test]
    fn inline_generic_requests_do_not_bound_every_instantiation() {
        let errors = diagnostics(
            "struct Wrapper[T]: Clone { value: T }\nstruct Owned { value: int32 }\nfunc test() { owned := Wrapper[Owned] { value: Owned { value: 1 } }; moved := owned; value := Wrapper[int32] { value: 2 }; copied := value; cloned := value.clone() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn conditional_clone_still_requires_each_substituted_field() {
        let errors = diagnostics(
            "struct Wrapper[T]: Clone { value: T }\nstruct Plain { value: int32 }\nfunc needsClone[T: Clone](_ value: &T) {}\nfunc test() { value := Wrapper[Plain] { value: Plain { value: 1 } }; needsClone(&value) }",
        );
        assert!(
            errors.iter().any(|error| error.message.contains("Clone")),
            "{errors:?}"
        );
    }

    #[test]
    fn primitive_field_aliases_support_clone() {
        let errors = diagnostics(
            "type Number = int32\nstruct Wrapper: Clone { value: Number }\nfunc test() { original := Wrapper { value: 3 }; cloned := original.clone() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }
    #[test]
    fn phantom_parameter_does_not_require_clone() {
        let errors = diagnostics(
            "struct Owned { value: int32 }\nstruct Phantom[T]: Clone { value: int32 }\nfunc test() { original := Phantom[Owned] { value: 3 }; copied := original; cloned := original.clone() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }
    #[test]
    fn tuple_clone_discovers_components_without_warming_a_generic_call() {
        let errors = diagnostics(
            "struct Component: Clone { value: int32 }\nfunc test() { original := (Component { value: 1 }, Component { value: 2 }); cloned := original.clone() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn tuple_clone_uses_the_generic_component_bounds() {
        let errors =
            diagnostics("func duplicate[T: Clone](_ value: &(T, T)) -> (T, T) { value.clone() }");
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn plain_tuple_component_does_not_imply_clone() {
        let errors = diagnostics(
            "struct Plain { value: int32 }\nfunc needsClone[T: Clone](_ value: &T) {}\nfunc test() { original := (Plain { value: 1 }, 2); needsClone(&original) }",
        );
        assert!(
            errors.iter().any(|error| error.message.contains("Clone")),
            "{errors:?}"
        );
    }
    #[test]
    fn direct_tuple_clone_must_prove_component_conformances() {
        let errors = diagnostics(
            "struct Plain { value: int32 }\nfunc test() { original := (Plain { value: 1 }, 2); cloned := original.clone() }",
        );
        assert!(
            !errors.is_empty(),
            "a direct call must not bypass the Clone bound"
        );
    }
    #[test]
    fn array_clone_discovers_noncopyable_components_and_const_generic_bounds() {
        let errors = diagnostics(
            "struct Component: Clone { value: int32 }\nfunc duplicate[T: Clone, const N: usize](_ value: &[T; N]) -> [T; N] { value.clone() }\nfunc test() { var original: [Component; 2] = [Component { value: 1 }, Component { value: 2 }]; cloned := original.clone(); generic := duplicate(&original) }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn empty_array_clone_still_requires_its_element_conformance() {
        let errors = diagnostics(
            "struct Plain { value: int32 }\nfunc test() { var value: [Plain; 0] = []; cloned := value.clone() }",
        );
        assert!(!errors.is_empty(), "zero length must not invent Clone");
    }

    #[test]
    fn closure_clone_checks_captures_and_keeps_callable_kind() {
        let errors = diagnostics(
            "struct Item: Clone { value: int32 }\nfunc duplicate[F: Clone](_ f: &F) -> F { f.clone() }\nfunc test() { item := Item { value: 7 }; once := () => item; cloned := duplicate(&once); a := once(); b := cloned(); var count: int32 = 1; var increment = () => { count += 1; count }; var other = increment.clone(); c := increment(); d := other() }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn shared_variable_captures_clone_without_a_pointee_clone_bound() {
        for body in ["value := Plain { value: 7 }; f := () => value; cloned := f.clone()"] {
            let errors = diagnostics(&format!(
                "struct Plain {{ value: int32 }}\nfunc test() {{ {body} }}"
            ));
            assert!(errors.is_empty(), "{body}: {errors:?}");
        }
    }
    #[test]
    fn equality_synthesis_rejects_concrete_and_generic_other_rhs_types() {
        for declaration in [
            "struct Wrong: PartialEq[Other] { value: int32 }",
            "struct Wrong[T]: PartialEq[T] { value: int32 }",
        ] {
            let source = format!(
                "interface PartialEq[Rhs = Self] {{\nfunc eq(_ other: Rhs) -> bool\n}}\nstruct Other {{ value: int32 }}\n{declaration}\nfunc main() {{}}\n"
            );
            let errors =
                analyze_language_item_script(&source, true, &[(StdItem::PartialEq, "PartialEq")]);
            assert!(
                errors.iter().any(|error| error
                    .message
                    .contains("automatic equality requires Rhs = Self")),
                "{errors:?}"
            );
        }
    }

    #[test]
    fn explicit_cross_type_equality_remains_available() {
        let source = "interface PartialEq[Rhs = Self] {\nfunc eq(_ other: Rhs) -> bool\n}\nstruct Other { value: int32 }\nstruct Value { value: int32 }\nconform Value to PartialEq[Other] {\nfunc eq(_ other: Other) -> bool { true }\n}\nfunc main() {}";
        let errors =
            analyze_language_item_script(source, true, &[(StdItem::PartialEq, "PartialEq")]);
        assert!(errors.is_empty(), "{errors:?}");
    }
    fn equality_capability_diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        let source = format!(
            r#"
interface PartialEq[Rhs = Self] {{
    func eq(_ other: Rhs) -> bool
}}
interface Equatable[Rhs = Self]: PartialEq[Rhs] {{}}
interface Hasher {{}}
interface Hashable: PartialEq {{
    func hash[H: Hasher](into hasher: &H)
}}
conform int32 to PartialEq {{
    func eq(_ other: int32) -> bool {{ true }}
}}
conform int32 to Hashable {{
    func hash[H: Hasher](into hasher: &H) {{}}
}}
{body}
func main() {{}}
"#
        );
        analyze_language_item_script(
            &source,
            true,
            &[
                (StdItem::PartialEq, "PartialEq"),
                (StdItem::Equatable, "Equatable"),
                (StdItem::Hashable, "Hashable"),
            ],
        )
    }

    #[test]
    fn generic_equality_hash_and_marker_conditions_do_not_bound_the_type() {
        let errors = equality_capability_diagnostics(
            "struct Wrapper[T]: PartialEq, Equatable, Hashable { value: T }\nstruct Owned { value: int32 }\nfunc needsHash[T: Hashable](_ value: &T) {}\nfunc needsEq[T: Equatable](_ value: &T) {}\nfunc test() { owned := Wrapper[Owned] { value: Owned { value: 1 } }; moved := owned; value := Wrapper[int32] { value: 2 }; needsHash(&value); needsEq(&value) }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn derived_equality_rejects_nonconforming_fields_before_codegen() {
        let errors = equality_capability_diagnostics(
            "struct Owned { value: int32 }\nstruct Invalid: PartialEq { value: Owned }",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("PartialEq")),
            "{errors:?}"
        );
    }

    #[test]
    fn inherited_equality_requirement_is_not_an_overload_of_itself() {
        let errors = equality_capability_diagnostics(
            "struct Wrapper[T]: PartialEq, Hashable { value: T }\nfunc wrapped[T: PartialEq[T]](_ a: &Wrapper[T], _ b: &Wrapper[T]) -> bool { a.eq(*b) }\nfunc bounded[T: Hashable](_ a: &T, _ b: &T) -> bool { a.eq(*b) }",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn generic_equality_does_not_claim_nonconforming_instantiations() {
        let errors = equality_capability_diagnostics(
            "struct Owned { value: int32 }\nstruct Wrapper[T]: PartialEq { value: T }\nfunc needsEq[T: PartialEq[T]](_ value: &T) {}\nfunc test() { value := Wrapper[Owned] { value: Owned { value: 1 } }; needsEq(&value) }",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("PartialEq")),
            "{errors:?}"
        );
    }

    #[test]
    fn conditional_hashable_requires_the_actual_super_conformance() {
        let errors = equality_capability_diagnostics(
            "struct Wrapper[T]: Hashable { value: T }\nfunc needsHash[T: Hashable](_ value: &T) {}\nfunc test() { value := Wrapper[int32] { value: 1 }; needsHash(&value) }",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("Hashable")),
            "{errors:?}"
        );
    }

    fn ordering_diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        let source = format!(
            r#"
enum Ordering {{ case less; case equal; case greater; }}
enum Optional[T] {{ case some(T); case none; }}
interface PartialEq[Rhs = Self] {{
    func eq(_ other: Rhs) -> bool
}}
interface PartialOrd[Rhs = Self]: PartialEq[Rhs] {{
    func partialCmp(_ other: Rhs) -> Optional[Ordering]
}}
interface Ord: PartialOrd {{
    func cmp(_ other: Self) -> Ordering
}}
interface Default {{
    static func default() -> Self
}}
type Comparable = PartialEq & PartialOrd & Ord
conform int32 to PartialEq {{
    func eq(_ other: int32) -> bool {{ true }}
}}
conform int32 to PartialOrd {{
    func partialCmp(_ other: int32) -> Optional[Ordering] {{ .none }}
}}
conform int32 to Ord {{
    func cmp(_ other: int32) -> Ordering {{ .equal }}
}}
conform int32 to Default {{
    static func default() -> int32 {{ 0 }}
}}
conform double to PartialEq {{
    func eq(_ other: double) -> bool {{ true }}
}}
conform double to PartialOrd {{
    func partialCmp(_ other: double) -> Optional[Ordering] {{ .none }}
}}
{body}
func main() {{}}
"#
        );
        analyze_language_item_script(
            &source,
            false,
            &[
                (StdItem::PartialEq, "PartialEq"),
                (StdItem::PartialOrd, "PartialOrd"),
                (StdItem::Ord, "Ord"),
                (StdItem::Default, "Default"),
            ],
        )
    }

    fn assert_reports(body: &str, expected: &[&str]) {
        let errors = ordering_diagnostics(body);
        for message in expected {
            assert!(
                errors.iter().any(|error| error.message.contains(message)),
                "{body}: expected '{message}' in {errors:#?}"
            );
        }
    }

    #[test]
    fn ordering_derives_for_structs_enums_and_the_comparable_alias() {
        for body in [
            "struct Version: PartialEq, PartialOrd, Ord { major: int32; minor: int32 }",
            "struct Version: Comparable { major: int32; minor: int32 }",
            "struct Empty: Comparable {}",
            "enum Priority: Comparable { case low; case high }",
            "enum Shape: Comparable { case point; case circle(int32); case rect(width: int32, height: int32); case named { size: int32 } }",
            "struct Inner: Comparable { value: int32 }\nstruct Outer: Comparable { inner: Inner; extra: int32 }",
            "struct Measure: PartialEq, PartialOrd { value: double }",
            "func needsOrd[T: Ord](_ value: T) {}\nstruct Version: Comparable { major: int32 }\nfunc test() { needsOrd(Version { major: 1 }) }",
        ] {
            let errors = ordering_diagnostics(body);
            assert!(errors.is_empty(), "{body}: {errors:#?}");
        }
    }

    #[test]
    fn ordering_derivation_names_each_nonconforming_field() {
        assert_reports(
            "struct Point: PartialEq { x: int32 }\nstruct Ranked: Comparable { rank: int32; position: Point }",
            &[
                "cannot derive 'PartialOrd' for 'Ranked': field 'position' has type 'Point', which does not conform to 'PartialOrd'",
                "cannot derive 'Ord' for 'Ranked': field 'position' has type 'Point', which does not conform to 'Ord'",
            ],
        );
        assert_reports(
            "struct Point: PartialEq { x: int32 }\nenum Slot: Comparable { case empty; case filled(int32, Point); case at(spot: Point) }",
            &[
                "field 'filled.1' has type 'Point'",
                "field 'at.spot' has type 'Point'",
            ],
        );
        assert_reports(
            "struct Sample: Comparable { value: double }",
            &[
                "cannot derive 'Ord' for 'Sample': field 'value' has type 'double', which does not conform to 'Ord'",
            ],
        );
    }

    #[test]
    fn ordering_synthesis_rejects_other_rhs_types() {
        assert_reports(
            "struct Other { value: int32 }\nstruct Wrong: PartialOrd[Other] { value: int32 }\nconform Wrong to PartialEq[Other] {\nfunc eq(_ other: Other) -> bool { true }\n}",
            &["automatic ordering requires Rhs = Self"],
        );
    }

    #[test]
    fn derived_ord_requires_listed_super_interfaces() {
        assert_reports(
            "struct Score: Ord { value: int32 }",
            &[
                "interface 'Ord' requires type 'Score' to conform to 'PartialOrd[Score]'",
                "add 'PartialOrd' to the conformance list of 'Score'",
                "add 'PartialEq' to the conformance list of 'Score'",
            ],
        );
        assert_reports(
            "struct Score[T]: Ord { value: T }",
            &["add 'PartialOrd' to the conformance list of 'Score'"],
        );
        // A hand-written super-interface satisfies a derived Ord.
        let errors = ordering_diagnostics(
            "struct Score: PartialEq, Ord { value: int32 }\nconform Score to PartialOrd {\nfunc partialCmp(_ other: Score) -> Optional[Ordering] { .none }\n}",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn generic_ordering_and_default_are_conditional_on_arguments() {
        let declarations = "struct Plain { value: int32 }\nstruct Pair[T]: Comparable, Default { first: T; second: T }\nfunc needsOrd[T: Ord](_ value: T) {}\nfunc needsDefault[T: Default](_ value: T) {}\n";
        let errors = ordering_diagnostics(&format!(
            "{declarations}func test(_ value: Pair[int32]) {{ needsOrd(value); needsDefault(value) }}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = ordering_diagnostics(&format!(
            "{declarations}func test(_ value: Pair[Plain]) {{ needsOrd(value); needsDefault(value) }}"
        ));
        for interface in ["'Ord'", "'Default'"] {
            assert!(
                errors.iter().any(|error| error.message.contains(interface)),
                "{interface}: {errors:#?}"
            );
        }
    }

    #[test]
    fn default_derives_from_field_defaults_and_field_types() {
        for body in [
            "struct Settings: Default { retries: int32 = 3; count: int32 }",
            "struct Handle { id: int32 }\nstruct Session: Default { handle: Handle = Handle { id: 1 } }",
            "struct Inner: Default { value: int32 }\nstruct Outer: Default { inner: Inner }",
            "struct Empty: Default {}",
            "struct Plain { value: int32 }\nstruct Labelled[T]: Default { value: T; plain: Plain = Plain { value: 1 } }",
        ] {
            let errors = ordering_diagnostics(body);
            assert!(errors.is_empty(), "{body}: {errors:#?}");
        }
        assert_reports(
            "struct Handle { id: int32 }\nstruct Session: Default { retries: int32 = 3; handle: Handle }",
            &[
                "cannot derive 'Default' for 'Session': field 'handle' has no default value and its type 'Handle' does not conform to 'Default'",
            ],
        );
    }

    #[test]
    fn value_only_derivations_reject_enum_defaults_and_classes() {
        assert_reports(
            "enum Mode: Default { case fast; case slow }",
            &["cannot derive 'Default' for enum 'Mode'"],
        );
        assert_reports(
            "final class Account: PartialEq, PartialOrd, Ord { balance: int32 }",
            &[
                "cannot derive 'PartialOrd' for class 'Account': only structs and enums",
                "cannot derive 'Ord' for class 'Account'",
            ],
        );
        assert_reports(
            "final class Config: Default { retries: int32 = 3 }",
            &["cannot derive 'Default' for class 'Config': only structs can derive it"],
        );
        // A conformance block implements the requirement instead.
        let errors = ordering_diagnostics(
            "enum Mode { case fast; case slow }\nconform Mode to Default {\nstatic func default() -> Mode { .slow }\n}",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn equality_derivation_names_each_nonconforming_field() {
        let errors = ordering_diagnostics(
            "struct Plain { value: int32 }\nstruct Keyed: PartialEq { id: int32; plain: Plain }\nenum Slot: PartialEq { case empty; case filled(int32, Plain) }\nfinal class Account: PartialEq { owner: Plain }",
        );
        for message in [
            "cannot derive 'PartialEq' for 'Keyed': field 'plain' has type 'Plain', which does not conform to 'PartialEq'",
            "cannot derive 'PartialEq' for 'Slot': field 'filled.1' has type 'Plain'",
            "cannot derive 'PartialEq' for 'Account': field 'owner' has type 'Plain'",
        ] {
            assert!(
                errors.iter().any(|error| error.message.contains(message)),
                "expected '{message}' in {errors:#?}"
            );
        }
        assert!(
            !errors
                .iter()
                .any(|error| error.message.contains("does not satisfy requirements")),
            "{errors:#?}"
        );
    }

    fn debug_diagnostics(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        let source = format!(
            r#"
struct Formatter {{}}
interface Debug {{
    func debug(_ into: &Formatter)
}}
conform int32 to Debug {{
    func debug(_ into: &Formatter) {{}}
}}
{body}
func main() {{}}
"#
        );
        analyze_language_item_script(&source, false, &[(StdItem::Debug, "Debug")])
    }

    fn assert_debug_reports(body: &str, expected: &[&str]) {
        let errors = debug_diagnostics(body);
        for message in expected {
            assert!(
                errors.iter().any(|error| error.message.contains(message)),
                "{body}: expected '{message}' in {errors:#?}"
            );
        }
    }

    #[test]
    fn debug_derives_for_structs_and_every_enum_payload_shape() {
        for body in [
            "struct Version: Debug { major: int32; minor: int32 }",
            "struct Empty: Debug {}",
            "struct Inner: Debug { value: int32 }\nstruct Outer: Debug { inner: Inner; extra: int32 }",
            "enum Event: Debug { case quit; case key(int32); case click { x: int32, y: int32 }; case resize(width: int32, height: int32) }",
            "enum Never: Debug {}",
            "func needsDebug[T: Debug](_ value: T) {}\nstruct Version: Debug { major: int32 }\nfunc test() { needsDebug(Version { major: 1 }) }",
        ] {
            let errors = debug_diagnostics(body);
            assert!(errors.is_empty(), "{body}: {errors:#?}");
        }
    }

    #[test]
    fn debug_derivation_names_each_nonconforming_field() {
        assert_debug_reports(
            "struct Plain { value: int32 }\nstruct Holder: Debug { count: int32; plain: Plain }",
            &[
                "cannot derive 'Debug' for 'Holder': field 'plain' has type 'Plain', which does not conform to 'Debug'",
            ],
        );
        assert_debug_reports(
            "struct Plain { value: int32 }\nenum Slot: Debug { case empty; case filled(int32, Plain); case at(spot: Plain); case record { inner: Plain } }",
            &[
                "field 'filled.1' has type 'Plain'",
                "field 'at.spot' has type 'Plain'",
                "field 'record.inner' has type 'Plain'",
            ],
        );
    }

    #[test]
    fn debug_is_derived_for_value_types_only() {
        assert_debug_reports(
            "final class Node: Debug { value: int32 }",
            &["cannot derive 'Debug' for class 'Node': only structs and enums can derive it"],
        );
        // A conformance block implements it for a class instead.
        let errors = debug_diagnostics(
            "final class Node { value: int32 }\nconform Node to Debug {\nfunc debug(_ into: &Formatter) {}\n}",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn generic_debug_is_conditional_on_arguments() {
        let declarations = "struct Plain { value: int32 }\nstruct Pair[T]: Debug { first: T; second: T }\nenum Choice[T]: Debug { case none; case some(T) }\nfunc needsDebug[T: Debug](_ value: T) {}\n";
        let errors = debug_diagnostics(&format!(
            "{declarations}func test(_ pair: Pair[int32], _ choice: Choice[int32]) {{ needsDebug(pair); needsDebug(choice) }}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
        // Pair[Plain] is still a valid type; it only lacks Debug.
        let errors = debug_diagnostics(&format!(
            "{declarations}func test(_ pair: Pair[Plain]) {{ needsDebug(pair) }}"
        ));
        assert!(
            errors.iter().any(|error| error.message.contains("'Debug'")),
            "{errors:#?}"
        );
    }
}
