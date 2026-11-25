//! Collect member names with the same receiver search used for method calls.

use std::collections::BTreeMap;

use rustc_hash::FxHashSet;

use crate::{
    compile::{analysis_products::MemberCompletion, context::Gcx},
    hir::DefinitionID,
    sema::models::{Ty, TyKind},
    span::{Span, Symbol},
};

use super::{ConstraintSolver, ConstraintSystem};

pub(crate) fn members<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    typed_receiver: Ty<'ctx>,
    addressable: bool,
    span: Span,
) -> Vec<MemberCompletion> {
    let solver = ConstraintSystem::new(gcx, owner).take_solver(None);
    let mut items = BTreeMap::new();
    for (candidate, _, referenceable) in solver.reciever_candidates(typed_receiver, addressable) {
        fields(gcx, owner, candidate, &mut items);
        let mut receivers = vec![candidate];
        if referenceable {
            receivers.push(Ty::new(TyKind::Reference(candidate), gcx));
        }
        for receiver in receivers {
            for name in method_names(&solver, receiver) {
                if solver
                    .lookup_instance_candidates_method(candidate, receiver, name, span)
                    .is_empty()
                {
                    continue;
                }
                let name = gcx.symbol_text(name).to_string();
                items.entry(name.clone()).or_insert(MemberCompletion {
                    name,
                    is_method: true,
                    detail: None,
                });
            }
        }
    }
    items.into_values().collect()
}

fn fields<'ctx>(
    gcx: Gcx<'ctx>,
    owner: DefinitionID,
    ty: Ty<'ctx>,
    items: &mut BTreeMap<String, MemberCompletion>,
) {
    let mut insert = |name: Symbol, ty: Ty<'ctx>| {
        let name = gcx.symbol_text(name).to_string();
        items
            .entry(name.clone())
            .or_insert_with(|| MemberCompletion {
                name,
                is_method: false,
                detail: Some(ty.format(gcx)),
            });
    };
    if let TyKind::Tuple(elements) = ty.kind() {
        for (index, name) in ty.tuple_labels() {
            if let Some(&element) = elements.get(*index) {
                insert(*name, element);
            }
        }
    }
    if let Some(definition) = gcx.source_struct_definition(ty) {
        for field in definition.fields {
            if gcx.is_visibility_allowed(field.visibility, owner) {
                insert(field.name, field.ty);
            }
        }
    }
}

fn method_names<'ctx>(solver: &ConstraintSolver<'ctx>, receiver: Ty<'ctx>) -> FxHashSet<Symbol> {
    let gcx = solver.gcx();
    let mut names = FxHashSet::default();
    if let Some(head) = solver.type_head_from_type(receiver) {
        let mut collect = |db: &mut crate::compile::context::TypeDatabase<'ctx>| {
            if let Some(member_index) = db.type_head_to_members.get(&head) {
                names.extend(member_index.inherent_instance.keys().copied());
            }
        };
        gcx.with_session_type_database(&mut collect);
        for index in gcx.visible_packages() {
            gcx.with_type_database(index, &mut collect);
        }
    }
    if gcx.is_class_type(receiver) {
        for method in gcx.class_methods(receiver) {
            names.insert(gcx.definition_ident(method.implementation).symbol);
        }
    }
    names
}
