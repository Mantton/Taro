//! Materialize the missing instance witnesses of a delegated conformance once
//! signatures, stored fields and explicit overloads are available.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::{
        impl_engine::{prove_interface_goal, ref_ops},
        models::*,
        tycheck::utils::{instantiate::instantiate_ty_with_args, normalize_aliases},
    },
    span::Identifier,
};

pub(crate) fn register(package: &hir::Package, gcx: Gcx<'_>) -> CompileResult<()> {
    struct Delegates<'ctx>(Gcx<'ctx>);
    impl HirVisitor for Delegates<'_> {
        fn visit_declaration(&mut self, node: &hir::Declaration) {
            if let hir::DeclarationKind::Impl(block) = &node.kind
                && let Some(field) = block.delegate
            {
                register_block(self.0, node.id, block, field);
            }
        }
    }
    hir::walk_package(&mut Delegates(gcx), package);
    gcx.dcx().ok()
}

fn register_block<'ctx>(
    gcx: Gcx<'ctx>,
    id: hir::DefinitionID,
    block: &hir::Impl,
    name: Identifier,
) {
    let Some((conformance, record)) = gcx.with_session_type_database(|db| {
        let key = *db.conformance_by_extension.get(&id)?.first()?;
        Some((key, db.conformance_records[&key]))
    }) else {
        return;
    };
    let Some(wrapper) = record.interface.self_ty() else {
        return;
    };
    let Some((index, storage)) = stored_field(gcx, wrapper, id, name) else {
        gcx.dcx().emit_error(
            format!(
                "delegation requires an accessible stored field named '{}'",
                gcx.symbol_text(name.symbol)
            ),
            Some(name.span),
        );
        return;
    };
    let assumptions = crate::sema::tycheck::constraints::canonical_constraints_of(gcx, id);
    let assumptions = gcx
        .store
        .arenas
        .global
        .alloc_slice_fill_iter(assumptions.into_iter().map(|c| c.value));
    let supports = |receiver| {
        let interface = ref_ops::interface_ref_with_self(gcx, receiver, record.interface);
        if let TyKind::BoxedExistential { interfaces } = receiver.kind() {
            return interfaces
                .iter()
                .flat_map(|root| ref_ops::collect_interface_with_superfaces(gcx, *root))
                .any(|actual| {
                    ref_ops::interface_ref_matches(
                        interface,
                        actual,
                        ref_ops::InterfaceRefMatch::Logical,
                    )
                });
        }
        interface.to_goal(gcx, assumptions).is_some_and(|goal| {
            prove_interface_goal(gcx, goal, SelectionMode::Typecheck) == GoalResult::Proven
        })
    };
    let storage = normalize_aliases(gcx, storage);
    let borrow = !supports(storage);
    let receiver = if borrow {
        Ty::new(TyKind::Reference(storage), gcx)
    } else {
        storage
    };
    if borrow && !supports(receiver) {
        gcx.dcx().emit_error(
            format!(
                "stored field '{}' of type '{}' does not conform to '{}'",
                gcx.symbol_text(name.symbol),
                storage.format(gcx),
                record.interface.format(gcx)
            ),
            Some(name.span),
        );
        return;
    }
    let Some(requirements) = gcx.get_interface_requirements(record.interface.id) else {
        return;
    };
    let Ok(bindings) = crate::sema::impl_engine::witness::associated_type_witnesses(
        gcx,
        record.target,
        &record,
        GenericArguments::empty(),
        requirements,
    ) else {
        return;
    };
    let env = crate::sema::tycheck::utils::ParamEnv::new(assumptions.to_vec());
    let icx = std::rc::Rc::new(crate::sema::tycheck::infer::InferCtx::new(gcx));
    let mut subscripts = rustc_hash::FxHashMap::default();
    for method in &requirements.methods {
        if !method.has_self
            || block.declarations.iter().any(|member| {
                matches!(member.kind, hir::AssociatedDeclarationKind::Function(_))
                    && member.identifier.symbol == method.name
                    && crate::sema::impl_engine::witness::method_signature_matches(
                        gcx,
                        method.id,
                        member.id,
                        &record,
                        GenericArguments::empty(),
                        &bindings,
                    )
            })
        {
            continue;
        }
        let Some(adapter) =
            gcx.conformance_adapter(conformance, method.id, Some((index as u32, borrow)))
        else {
            gcx.dcx().emit_error(
                format!("cannot forward requirement '{}'", gcx.symbol_text(method.name)),
                Some(name.span),
            );
            continue;
        };
        if matches!(receiver.kind(), TyKind::BoxedExistential { .. })
            && !ref_ops::method_is_dispatchable(gcx, method)
        {
            gcx.dcx().emit_error(format!("implement '{}' explicitly: the method cannot be called through a boxed interface", gcx.symbol_text(method.name)), Some(name.span));
            continue;
        }
        let identity =
            crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(gcx, adapter);
        let (_, wrapper_args) = gcx
            .adapter_source_arguments(adapter, identity)
            .expect("delegation adapter");
        let mut field_args = wrapper_args.to_vec();
        field_args[0] = GenericArgument::Type(receiver);
        let field_args = gcx.store.interners.intern_generic_args(field_args);
        let caller = gcx.get_signature(adapter);
        let callee = crate::sema::tycheck::utils::instantiate::instantiate_signature_with_args(
            gcx,
            gcx.get_signature(method.id),
            field_args,
        );
        let same = |left, right| {
            if left == right {
                return true;
            }
            let left = crate::sema::impl_engine::witness::substitute_projection_witnesses(
                gcx,
                left,
                &bindings,
                &record,
                GenericArguments::empty(),
            );
            crate::sema::tycheck::utils::normalize_ty(icx.clone(), left, &env)
                == crate::sema::tycheck::utils::normalize_ty(icx.clone(), right, &env)
        };
        if !same(caller.output, callee.output)
            || caller
                .inputs
                .iter()
                .zip(&callee.inputs)
                .skip(1)
                .any(|(left, right)| !same(left.ty, right.ty))
        {
            gcx.dcx().emit_error(format!("implement '{}' explicitly: forwarding changes a Self-dependent parameter or return type", gcx.symbol_text(method.name)), Some(name.span));
            continue;
        }
        if let Some((subscript, source)) = gcx.native_subscript_for_accessor(method.id) {
            let (_, entry) = subscripts.entry(subscript).or_insert_with(|| {
                (
                    adapter,
                    crate::compile::context::NativeSubscriptEntry {
                        getter: None,
                        setter: None,
                        address: None,
                        getter_is_default: false,
                        setter_is_default: false,
                        is_override: false,
                        is_final: false,
                    },
                )
            });
            if source.getter == Some(method.id) {
                entry.getter = Some(adapter);
            }
            if source.setter == Some(method.id) {
                entry.setter = Some(adapter);
            }
            if source.address == Some(method.id) {
                entry.address = Some(adapter);
            }
        }
        gcx.with_session_type_database(|db| {
            if let Some(property) = requirements
                .properties
                .iter()
                .find(|p| p.getter_id == method.id)
            {
                db.type_head_to_interface_properties
                    .entry(record.target)
                    .or_default()
                    .entry((record.interface.id, property.name))
                    .or_default()
                    .push(crate::compile::context::ComputedPropertyEntry {
                        property_id: adapter,
                        getter_id: adapter,
                        ty: caller.output,
                        visibility: gcx.definition_visibility(property.id),
                    });
                return;
            }
            let members = db.type_head_to_members.entry(record.target).or_default();
            members
                .trait_methods
                .entry((record.interface.id, method.name))
                .or_default()
                .members
                .push(adapter);
            members
                .trait_methods_by_name
                .entry(method.name)
                .or_default()
                .push(adapter);
        });
    }
    gcx.with_session_type_database(|db| db.native_subscripts.extend(subscripts.into_values()));
}

fn stored_field<'ctx>(
    gcx: Gcx<'ctx>,
    wrapper: Ty<'ctx>,
    id: hir::DefinitionID,
    name: Identifier,
) -> Option<(usize, Ty<'ctx>)> {
    let mut owner = normalize_aliases(gcx, wrapper);
    if let TyKind::Reference(inner) = owner.kind() {
        owner = normalize_aliases(gcx, inner)
    }
    let TyKind::Adt(def, args) = owner.kind() else {
        return None;
    };
    let fields = &gcx.try_get_struct_definition(def.id)?.fields;
    let (index, field) = fields
        .iter()
        .enumerate()
        .find(|(_, field)| field.name == name.symbol)?;
    if !gcx.is_visibility_allowed(field.visibility, id) {
        return None;
    }
    Some((index, instantiate_ty_with_args(gcx, field.ty, args)))
}
