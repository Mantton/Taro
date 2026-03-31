use crate::{
    compile::context::Gcx,
    constants::INTERFACE_COMPUTED_PROPERTIES_DEFERRED_DIAGNOSTIC,
    error::CompileResult,
    hir::{self, DefinitionID},
    sema::{
        impl_engine::method_signature_matches,
        models::{
            ConformanceRecord, Constraint, GenericArgument, GenericArguments, InterfaceGoal,
            InterfaceMethodRequirement, InterfaceReference, SelectionError, SelectionMode, Ty,
        },
        tycheck::utils::{
            generics::GenericsBuilder, instantiate::instantiate_interface_ref_with_args,
            type_head_from_value_ty,
        },
    },
};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn run(_: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let actor = Actor { context };
        actor.validate_all_conformances();
        context.dcx().ok()
    }

    fn validate_all_conformances(&self) {
        let mut records = self
            .context
            .all_conformance_records(self.context.package_index());
        records.sort_by_key(|record| {
            (
                std::cmp::Reverse(record.location.start.line),
                std::cmp::Reverse(record.location.start.offset),
            )
        });

        for record in &records {
            self.validate_direct(
                record.interface,
                record.location,
                record.is_conditional,
                Some(*record),
            );
        }

        let mut seen = FxHashSet::default();
        for record in records {
            if record.is_conditional {
                continue;
            }

            let mut supers = self.collect_interface_with_supers(record.interface);
            for iface in supers.drain(1..) {
                if !seen.insert((record.target, iface)) {
                    continue;
                }

                let explicit_record = self
                    .context
                    .collect_from_databases(|db| {
                        db.conformance_by_interface_head
                            .get(&(iface.id, record.target))
                            .into_iter()
                            .flat_map(|ids| ids.iter())
                            .filter_map(|id| db.conformance_records.get(id))
                            .copied()
                            .collect::<Vec<_>>()
                    })
                    .into_iter()
                    .find(|rec| rec.interface == iface);

                if let Some(explicit_record) = explicit_record {
                    self.validate_direct(
                        iface,
                        explicit_record.location,
                        explicit_record.is_conditional,
                        Some(explicit_record),
                    );
                } else {
                    let type_name = record.target.format(self.context);
                    let requiring = record.interface.format(self.context);
                    let required = iface.format(self.context);
                    self.context.dcx().emit_error(
                        format!(
                            "interface '{}' requires type '{}' to conform to '{}'",
                            requiring, type_name, required
                        ),
                        Some(record.location),
                    );
                }
            }
        }
    }

    fn validate_direct(
        &self,
        interface: InterfaceReference<'ctx>,
        span: crate::span::Span,
        is_conditional: bool,
        record: Option<ConformanceRecord<'ctx>>,
    ) {
        if let Some(record) = record {
            if !self.context.generics_of(record.extension).is_empty() {
                return;
            }
        }

        let Some(goal) = self.goal_from_interface(interface) else {
            return;
        };
        if self.context.interface_has_associated_property(goal.interface_id) {
            self.context.dcx().emit_error(
                INTERFACE_COMPUTED_PROPERTIES_DEFERRED_DIAGNOSTIC.into(),
                Some(span),
            );
            return;
        }
        if is_conditional || goal_has_unresolved_types(goal) {
            return;
        }

        match self
            .context
            .build_conformance_witness(goal, SelectionMode::Typecheck)
        {
            Ok(_) => {}
            Err(err) => self.emit_selection_error(err, span, record),
        }
    }

    fn emit_selection_error(
        &self,
        err: SelectionError<'ctx>,
        span: crate::span::Span,
        record: Option<ConformanceRecord<'ctx>>,
    ) {
        match err {
            SelectionError::NoCandidates(goal) => {
                let iface = goal.to_interface_ref(self.context);
                self.context.dcx().emit_error(
                    format!(
                        "type '{}' does not satisfy requirements for interface '{}'",
                        goal.self_ty.format(self.context),
                        iface.format(self.context)
                    ),
                    Some(span),
                );
                self.emit_missing_required_methods(goal, span, record);
            }
            SelectionError::Ambiguous(goal) => {
                let iface = goal.to_interface_ref(self.context);
                self.context.dcx().emit_error(
                    format!(
                        "ambiguous conformance: multiple impls satisfy '{}' for '{}'",
                        iface.format(self.context),
                        goal.self_ty.format(self.context)
                    ),
                    Some(span),
                );
            }
            SelectionError::ObligationFailed {
                candidate,
                obligation,
            } => {
                let iface = obligation.to_interface_ref(self.context);
                self.context.dcx().emit_error(
                    format!(
                        "conformance candidate '{:?}' failed obligation '{}'",
                        candidate,
                        iface.format(self.context)
                    ),
                    Some(span),
                );
            }
        }
    }

    fn emit_missing_required_methods(
        &self,
        goal: InterfaceGoal<'ctx>,
        span: crate::span::Span,
        record: Option<ConformanceRecord<'ctx>>,
    ) {
        let Some(record) = record else {
            return;
        };

        let Some(requirements) = self.context.get_interface_requirements(goal.interface_id) else {
            return;
        };

        for requirement in &requirements.methods {
            if !requirement.is_required {
                continue;
            }

            if self.has_required_method_impl(goal, record, requirement) {
                continue;
            }

            self.context.dcx().emit_info(
                format!(
                    "missing required method '{}' with signature '{}'",
                    self.context.symbol_text(requirement.name),
                    requirement.signature.format_for_display(self.context)
                ),
                Some(span),
            );
        }
    }

    fn has_required_method_impl(
        &self,
        goal: InterfaceGoal<'ctx>,
        record: ConformanceRecord<'ctx>,
        requirement: &InterfaceMethodRequirement<'ctx>,
    ) -> bool {
        if record.is_inline {
            let Some(type_head) = type_head_from_value_ty(goal.self_ty) else {
                return false;
            };
            let args_template = GenericsBuilder::identity_for_item(self.context, requirement.id);
            return crate::sema::tycheck::derive::try_synthesize_method(
                self.context,
                type_head,
                goal.self_ty,
                goal.interface_id,
                goal.to_interface_ref(self.context).arguments,
                requirement.name,
                requirement.id,
                args_template,
            )
            .is_some();
        }

        let empty_type_witnesses: FxHashMap<DefinitionID, Ty<'ctx>> = FxHashMap::default();

        self.context
            .with_type_database(record.extension.package(), |db| {
                db.def_to_fn_sig.keys().copied().any(|candidate| {
                    self.context.definition_parent(candidate) == Some(record.extension)
                        && self.context.definition_kind(candidate)
                            == crate::sema::resolve::models::DefinitionKind::AssociatedFunction
                        && self.context.definition_ident(candidate).symbol == requirement.name
                        && method_signature_matches(
                            self.context,
                            requirement.id,
                            candidate,
                            &record,
                            GenericArguments::empty(),
                            &empty_type_witnesses,
                        )
                })
            })
    }

    fn collect_interface_with_supers(
        &self,
        root: InterfaceReference<'ctx>,
    ) -> Vec<InterfaceReference<'ctx>> {
        let mut out = Vec::new();
        let mut queue = std::collections::VecDeque::new();
        let mut seen: FxHashSet<DefinitionID> = FxHashSet::default();

        seen.insert(root.id);
        out.push(root);
        queue.push_back(root);

        while let Some(current) = queue.pop_front() {
            let Some(def) = self.context.get_interface_definition(current.id) else {
                continue;
            };

            for superface in &def.superfaces {
                let iface = instantiate_interface_ref_with_args(
                    self.context,
                    superface.value,
                    current.arguments,
                );
                if seen.insert(iface.id) {
                    out.push(iface);
                    queue.push_back(iface);
                }
            }
        }

        out
    }

    fn goal_from_interface(
        &self,
        interface: InterfaceReference<'ctx>,
    ) -> Option<InterfaceGoal<'ctx>> {
        let self_ty = match interface.arguments.get(0).copied() {
            Some(GenericArgument::Type(ty)) => ty,
            _ => return None,
        };
        let interface_args = if interface.arguments.len() > 1 {
            self.context
                .store
                .interners
                .intern_generic_args_slice(&interface.arguments[1..])
        } else {
            GenericArguments::empty()
        };
        Some(InterfaceGoal {
            interface_id: interface.id,
            self_ty,
            interface_args,
            bindings: interface.bindings,
            param_env: &[] as &[Constraint<'ctx>],
        })
    }
}

pub fn resolve_conformance_witness<'ctx>(
    context: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
    resolve_conformance_witness_with_mode(context, interface, SelectionMode::Typecheck)
}

pub fn resolve_conformance_witness_with_mode<'ctx>(
    context: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    mode: SelectionMode,
) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
    if interface_has_unresolved_types(interface) {
        return None;
    }

    let self_ty = match interface.arguments.get(0).copied() {
        Some(GenericArgument::Type(ty)) => ty,
        _ => return None,
    };
    if ty_has_infer_types(self_ty) {
        return None;
    }
    let interface_args = if interface.arguments.len() > 1 {
        context
            .store
            .interners
            .intern_generic_args_slice(&interface.arguments[1..])
    } else {
        GenericArguments::empty()
    };
    let goal = InterfaceGoal {
        interface_id: interface.id,
        self_ty,
        interface_args,
        bindings: interface.bindings,
        param_env: &[],
    };

    match context.build_conformance_witness(goal, mode) {
        Ok(witness) => Some(witness),
        Err(SelectionError::Ambiguous(_))
        | Err(SelectionError::NoCandidates(_))
        | Err(SelectionError::ObligationFailed { .. }) => None,
    }
}

fn goal_has_unresolved_types(goal: InterfaceGoal<'_>) -> bool {
    if ty_has_infer_types(goal.self_ty) {
        return true;
    }

    if goal
        .interface_args
        .iter()
        .any(generic_arg_has_unresolved_types)
    {
        return true;
    }

    goal.bindings
        .iter()
        .any(|binding| ty_has_infer_types(binding.ty))
}

fn interface_has_unresolved_types(interface: InterfaceReference<'_>) -> bool {
    interface
        .arguments
        .iter()
        .any(generic_arg_has_unresolved_types)
        || interface
            .bindings
            .iter()
            .any(|binding| ty_has_infer_types(binding.ty))
}

fn generic_arg_has_unresolved_types(arg: &GenericArgument<'_>) -> bool {
    match arg {
        GenericArgument::Type(ty) => ty_has_infer_types(*ty),
        GenericArgument::Const(c) => {
            matches!(c.kind, crate::sema::models::ConstKind::Infer(_)) || ty_has_infer_types(c.ty)
        }
    }
}

fn ty_has_infer_types(ty: crate::sema::models::Ty<'_>) -> bool {
    use crate::sema::models::{ConstKind, GenericArgument, TyKind};

    match ty.kind() {
        TyKind::Infer(_) => true,
        TyKind::Adt(_, args) | TyKind::Alias { args, .. } => args.iter().any(|arg| match arg {
            GenericArgument::Type(ty) => ty_has_infer_types(*ty),
            GenericArgument::Const(c) => {
                matches!(c.kind, ConstKind::Infer(_)) || ty_has_infer_types(c.ty)
            }
        }),
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => ty_has_infer_types(inner),
        TyKind::Array { element, len } => {
            ty_has_infer_types(element)
                || matches!(len.kind, ConstKind::Infer(_))
                || ty_has_infer_types(len.ty)
        }
        TyKind::Tuple(items) => items.iter().any(|item| ty_has_infer_types(*item)),
        TyKind::FnPointer { inputs, output } => {
            inputs.iter().any(|input| ty_has_infer_types(*input)) || ty_has_infer_types(output)
        }
        TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
            iface.arguments.iter().any(|arg| match arg {
                GenericArgument::Type(ty) => ty_has_infer_types(*ty),
                GenericArgument::Const(c) => {
                    matches!(c.kind, ConstKind::Infer(_)) || ty_has_infer_types(c.ty)
                }
            })
        }),
        TyKind::Closure {
            captured_generics,
            inputs,
            output,
            ..
        } => {
            captured_generics.iter().any(|arg| match arg {
                GenericArgument::Type(ty) => ty_has_infer_types(*ty),
                GenericArgument::Const(c) => {
                    matches!(c.kind, ConstKind::Infer(_)) || ty_has_infer_types(c.ty)
                }
            }) || inputs.iter().any(|input| ty_has_infer_types(*input))
                || ty_has_infer_types(output)
        }
        TyKind::Bool
        | TyKind::Rune
        | TyKind::String
        | TyKind::Int(_)
        | TyKind::UInt(_)
        | TyKind::Float(_)
        | TyKind::Parameter(_)
        | TyKind::Opaque(_)
        | TyKind::Error
        | TyKind::Never => false,
    }
}
