use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir,
    sema::{
        models::{
            ConformanceRecord, Constraint, GenericArguments, InterfaceGoal, InterfaceReference,
            SelectionError, SelectionMode,
        },
        tycheck::utils::{
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
            if self.context.std_item_def(hir::StdItem::AnyObject) == Some(record.interface.id)
                && !record
                    .interface
                    .self_ty()
                    .is_some_and(|ty| self.context.uses_native_class_handle(ty))
            {
                self.context.dcx().emit_error("AnyObject is a compiler-provided class-only capability; value types cannot declare this conformance".into(), Some(record.location));
                continue;
            }
            if record.is_inline
                && self.context.std_item_def(hir::StdItem::PartialEq) == Some(record.interface.id)
                && let Some(self_ty) = record.interface.self_ty()
                && crate::sema::tycheck::derive::equality_rhs(
                    self.context,
                    record.interface.arguments,
                    self_ty,
                ) != Some(crate::sema::tycheck::utils::normalize_aliases(
                    self.context,
                    self_ty,
                ))
            {
                self.context.dcx().emit_error(
                    "automatic equality requires Rhs = Self; provide an explicit cross-type conformance".into(),
                    Some(record.location),
                );
                continue;
            }
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

                if self.context.std_item_def(hir::StdItem::AnyObject) == Some(iface.id)
                    && iface
                        .self_ty()
                        .is_some_and(|ty| self.context.uses_native_class_handle(ty))
                {
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
                } else if iface
                    .self_ty()
                    .is_some_and(|ty| self.context.is_class_type(ty))
                    && resolve_conformance_witness(self.context, iface).is_some()
                {
                    // A verified inherited class conformance satisfies a
                    // superinterface too. Requiring a second declaration here
                    // contradicts coherence (which rejects redeclaring it).
                    // Witness selection keeps the base's generic arguments;
                    // this never invents Parent[Derived] from Parent[Base].
                    continue;
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
            if crate::sema::impl_engine::property_requirement_satisfied(
                self.context,
                type_head,
                property,
                &record,
            ) {
                continue;
            }
            self.context.dcx().emit_info(
                format!(
                    "missing readable property '{}' of type '{}'",
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

#[cfg(test)]
mod final_class_tests {
    #[test]
    fn final_class_conformances_support_generic_calls_and_readonly_defaults() {
        crate::test_support::analyze_script(
            r#"
interface CounterOps {
    func bump(_ amount: int32)
    func current() -> int32
    func duplicate() -> Self
    func next() -> int32 { self.current() + 1 }
}
final class Counter { value: int32 }
extend Counter { init(_ value: int32) { self.value = value } }
conform Counter to CounterOps {
    func bump(_ amount: int32) { self.value += amount }
    func current() -> int32 { self.value }
    func duplicate() -> Self { Self(self.value) }
}
func inspect[T: CounterOps](_ value: &T) -> int32 { value.next() }
func update[T: CounterOps](_ value: &T) { value.bump(2) }
func main() {
    var value: Counter = Counter(3)
    update(&value)
    var result: int32 = inspect(&value)
    var duplicate: Counter = value.duplicate()
}
"#,
            |_, _| {},
        );
    }

    #[test]
    fn value_interface_defaults_can_change_or_reference_their_receiver_copy() {
        for source in [
            "interface Replace { func replace(_ other: Self) { self = other }; }\nfinal class Counter { value: int32 }\nconform Counter to Replace {}\nfunc main() {}",
            "interface Export { func borrowed() -> &Self { &self }; }\nfinal class Counter { value: int32 }\nconform Counter to Export {}\nfunc main() {}",
        ] {
            let diagnostics = crate::test_support::analyze_script_mir_diagnostics(source);
            assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        }
    }

    #[test]
    fn value_defaults_dispatch_through_the_shared_class_object() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"
interface Steps {
    func step()
    func twice() { self.step(); self.step() }
}
final class Counter { value: int32 }
conform Counter to Steps { func step() {}; }
final class GenericCounter[Tag] { value: int32 }
conform[Tag] GenericCounter[Tag] to Steps { func step() {}; }
func useGeneric(_ value: &GenericCounter[bool]) { value.twice() }
func change[T: Steps](_ value: &T) { value.twice() }
func use(_ value: &Counter) { change(value) }
func main() {}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn retargeting_defaults_remain_valid_for_ordinary_value_types() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            r#"
interface Replace { func replace(_ other: Self) { self = other }; }
struct Counter { value: int32 }
conform Counter to Replace {}
func use(_ value: &Counter, _ other: Counter) { value.replace(other) }
func main() {}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}

#[cfg(test)]
mod inherited_superinterface_tests {
    #[test]
    fn inherited_class_witness_satisfies_superinterface_without_redeclaration() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            r#"
interface Reader { func read() -> int32; }
interface Duplicate: Reader { func duplicate() -> Self; }
class Base {}
extend Base { init() {}; }
conform Base to Reader { func read() -> int32 { 7 }; }
final class Derived: Base {}
conform Derived to Duplicate { func duplicate() -> Self { Derived() }; }
func main() { var source: any Duplicate = Derived(); }
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}
