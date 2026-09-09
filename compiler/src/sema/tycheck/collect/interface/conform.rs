use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir,
    sema::{
        models::{
            AdtKind, ConformanceRecord, Constraint, EnumVariantKind, GenericArgument,
            GenericArguments, InterfaceGoal, InterfaceReference, SelectionError, SelectionMode,
            TyKind,
        },
        tycheck::solve::{ConstraintSystem, Goal},
        tycheck::utils::{
            instantiate::instantiate_ty_with_args,
            type_head_from_value_ty,
            unresolved::{
                goal_contains_unresolved_inference, interface_ref_contains_unresolved_inference,
                ty_contains_unresolved_inference,
            },
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
            self.validate_copy_storage(*record);
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
                        db.conformance_by_interface
                            .get(&iface.id)
                            .into_iter()
                            .flat_map(|ids| ids.iter())
                            .filter_map(|id| db.conformance_records.get(id))
                            .filter(|candidate| {
                                candidate.target == record.target
                                    || (candidate.target.is_blanket() && record.target.is_blanket())
                            })
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

    fn validate_copy_storage(&self, record: ConformanceRecord<'ctx>) {
        let gcx = self.context;
        if gcx.std_item_def(hir::StdItem::Copy) != Some(record.interface.id) {
            return;
        }
        let Some(self_ty) = record.interface.self_ty() else {
            return;
        };
        let mut cs = ConstraintSystem::new(gcx, record.extension);
        let self_ty = cs.structurally_resolve(self_ty);
        let TyKind::Adt(def, args) = self_ty.kind() else {
            // Builtin Copy types already have a representation guarantee. A
            // blanket assertion on an arbitrary type cannot establish one.
            if !gcx.is_type_builtin_copyable(self_ty) {
                gcx.dcx().emit_error(
                    "Copy can only be implemented for structs, enums, or intrinsically copyable types"
                        .into(),
                    Some(record.location),
                );
            }
            return;
        };

        // Check the representation even for unused generic declarations and
        // conditional impls. Instantiation maps nominal field parameters into
        // the impl's parameter environment (including specialized impl heads).
        let mut require_copy = |ty| {
            let ty = instantiate_ty_with_args(gcx, ty, args);
            let arguments = gcx
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(ty)]);
            cs.add_goal(
                Goal::Conforms {
                    ty,
                    interface: InterfaceReference {
                        id: record.interface.id,
                        arguments,
                        bindings: &[],
                    },
                },
                record.location,
            );
        };
        match def.kind {
            AdtKind::Struct => {
                for field in gcx.get_struct_definition(def.id).fields {
                    require_copy(field.ty);
                }
            }
            AdtKind::Enum => {
                for variant in gcx.get_enum_definition(def.id).variants {
                    if let EnumVariantKind::Tuple(fields) = variant.kind {
                        for field in fields {
                            require_copy(field.ty);
                        }
                    }
                }
            }
        }
        cs.solve_all();
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

        let Some(type_head) = type_head_from_value_ty(goal.self_ty) else {
            return;
        };
        let mut property_accessors = FxHashSet::default();
        for property in &requirements.properties {
            property_accessors.insert(property.getter_id);
            property_accessors.extend(property.setter_id);
            if crate::sema::impl_engine::property_requirement_satisfied(
                self.context,
                type_head,
                property,
                &record,
            ) {
                continue;
            }
            let capability = match (
                property.getter_is_required,
                property.setter_is_required.unwrap_or(false),
            ) {
                (true, true) => "readable and writable",
                (false, true) => "writable",
                _ => "readable",
            };
            self.context.dcx().emit_info(
                format!(
                    "missing {capability} property '{}' of type '{}'",
                    self.context.symbol_text(property.name),
                    property.ty.format(self.context)
                ),
                Some(span),
            );
        }

        for requirement in &requirements.methods {
            if !requirement.is_required || property_accessors.contains(&requirement.id) {
                continue;
            }

            if crate::sema::impl_engine::find_method_witness(
                self.context,
                type_head,
                requirement,
                &record,
                GenericArguments::empty(),
                &FxHashMap::default(),
            )
            .is_some()
            {
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

    fn collect_interface_with_supers(
        &self,
        root: InterfaceReference<'ctx>,
    ) -> Vec<InterfaceReference<'ctx>> {
        crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(self.context, root)
    }

    fn goal_from_interface(
        &self,
        interface: InterfaceReference<'ctx>,
    ) -> Option<InterfaceGoal<'ctx>> {
        interface.to_goal(self.context, &[])
    }
}

pub fn resolve_conformance_witness<'ctx>(
    context: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
    resolve_conformance_witness_with_mode_and_param_env(
        context,
        interface,
        SelectionMode::Typecheck,
        &[],
    )
}

pub fn resolve_conformance_witness_with_param_env<'ctx>(
    context: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    param_env: &'ctx [Constraint<'ctx>],
) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
    resolve_conformance_witness_with_mode_and_param_env(
        context,
        interface,
        SelectionMode::Typecheck,
        param_env,
    )
}

pub fn resolve_conformance_witness_with_mode<'ctx>(
    context: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    mode: SelectionMode,
) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
    resolve_conformance_witness_with_mode_and_param_env(context, interface, mode, &[])
}

fn resolve_conformance_witness_with_mode_and_param_env<'ctx>(
    context: Gcx<'ctx>,
    interface: InterfaceReference<'ctx>,
    mode: SelectionMode,
    param_env: &'ctx [Constraint<'ctx>],
) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
    if interface_ref_contains_unresolved_inference(interface) {
        return None;
    }

    let self_ty = interface.self_ty()?;
    if ty_contains_unresolved_inference(self_ty) {
        return None;
    }
    let goal = interface.to_goal_with_self_ty(context, param_env, self_ty);

    match context.build_conformance_witness(goal, mode) {
        Ok(witness) => Some(witness),
        Err(SelectionError::Ambiguous(_))
        | Err(SelectionError::NoCandidates(_))
        | Err(SelectionError::ObligationFailed { .. }) => None,
    }
}

fn goal_has_unresolved_types(goal: InterfaceGoal<'_>) -> bool {
    goal_contains_unresolved_inference(goal)
}
