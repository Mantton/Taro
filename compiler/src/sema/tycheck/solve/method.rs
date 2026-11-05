use super::{
    BindInterfaceMethodGoalData, BindMethodOverloadGoalData, ConstraintSolver, Goal,
    InterfaceCallInfo, MethodCallData, Obligation, SolverResult,
};
use crate::{
    sema::{
        error::TypeError,
        models::{
            GenericArgument, GenericArguments, InterfaceReference, LabeledFunctionSignature, Ty,
            TyKind,
        },
        resolve::models::DefinitionID,
        tycheck::{
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, BindOverloadGoalData, DisjunctionBranch,
            },
            utils::instantiate::instantiate_ty_with_args,
        },
    },
    span::{Span, Spanned, Symbol},
};
use rustc_hash::FxHashSet;

pub(super) struct InterfaceMethodCandidate<'ctx> {
    pub(super) call_info: InterfaceCallInfo,
    pub(super) candidate_ty: Ty<'ctx>,
    pub(super) instantiation_args: Option<GenericArguments<'ctx>>,
    pub(super) source: DefinitionID,
}

#[cfg(test)]
mod concrete_interface_tests {
    #[test]
    fn discovery_does_not_require_parameters_absent_from_the_interface_header() {
        let source = r#"
interface Source { type Item; }
struct IntSource {}
conform IntSource to Source { type Item = int32; }
interface Read { func count() -> int32 { 7 }; }
struct Adapter[S] {}
conform[Item, S: Source[Item = Item]] Adapter[S] to Read {}
func count(_ value: &Adapter[IntSource]) -> int32 { value.count() }
func main() {}
"#;
        let diagnostics = crate::test_support::analyze_script_diagnostics(source);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn blanket_method_arguments_absent_from_self_are_inferred_from_result() {
        let source = r#"
interface Make[T] { static func from(_ value: T) -> Self; }
interface Convert[T] { func convert() -> T; }
conform[S, T: Make[S]] S to Convert[T] {
    func convert() -> T { T::from(self) }
}
struct Wrapped { value: int32 }
struct Other { value: int32 }
conform Wrapped to Make[int32] { static func from(_ value: int32) -> Wrapped { Wrapped { value } }; }
conform Other to Make[int32] { static func from(_ value: int32) -> Other { Other { value } }; }
func generic[S, T: Make[S]](_ value: S) -> T { value.convert() }
func bounded[S: Convert[int32]](_ value: S) -> int32 { value.convert() }
func another[S: Convert[int32], T: Make[S]](_ value: S) -> T { value.convert() }
func main() {
    var value: Wrapped = 3_i32.convert()
    var other: Other = 4_i32.convert()
    var wrapped: Wrapped = generic(6_i32)
}
"#;
        let prefix = source.split("func main()").next().unwrap();
        for main in [
            "func main() {}",
            "func main() { var value: Wrapped = 3_i32.convert(); }",
            "func main() { var value: Other = 4_i32.convert(); }",
            "func main() { var value: Wrapped = generic(6_i32); }",
        ] {
            let diagnostics =
                crate::test_support::analyze_script_mir_diagnostics(&format!("{prefix}{main}"));
            assert!(diagnostics.is_empty(), "{main}: {diagnostics:#?}");
        }
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            &source.replace("var value: Wrapped", "var value: bool"),
        );
        assert!(
            !diagnostics.is_empty(),
            "an unimplemented destination must fail its conformance"
        );
    }

    #[test]
    fn bounded_static_self_is_fixed_before_associated_result_normalization() {
        let source = r#"
enum Attempt[T, E] { case ok(T); case err(E) }
interface TryMake[S] {
    type Error
    static func tryFrom(_ value: S) -> Attempt[Self, Self::Error]
}
interface TryConvert[T] { type Error; func tryConvert() -> Attempt[T, Self::Error]; }
conform[S, T: TryMake[S]] S to TryConvert[T] {
    type Error = T::Error
    func tryConvert() -> Attempt[T, Self::Error] { T::tryFrom(self) }
}
struct Wrapped { value: int32 }
conform Wrapped to TryMake[int32] {
    type Error = bool
    static func tryFrom(_ value: int32) -> Attempt[Wrapped, bool] { .ok(Wrapped { value }) }
}
func generic[S, T: TryMake[S]](_ value: S) -> Attempt[T, T::Error] { T::tryFrom(value) }
func main() {
    var result: Attempt[Wrapped, bool] = 4_i32.tryConvert()
    var genericResult: Attempt[Wrapped, bool] = generic(5_i32)
}
"#;
        let prefix = source.split("func main()").next().unwrap();
        crate::test_support::analyze_script(
            &format!("{prefix}func main() {{}}"),
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let interface = find("TryConvert");
                let goal = crate::sema::models::InterfaceGoal {
                    interface_id: interface,
                    self_ty: gcx.types.int32,
                    interface_args: gcx.store.interners.intern_generic_args(vec![
                        crate::sema::models::GenericArgument::Type(gcx.get_type(find("Wrapped"))),
                    ]),
                    bindings: &[],
                    param_env: &[],
                };
                let witness = crate::sema::impl_engine::build_conformance_witness(
                    gcx,
                    goal,
                    crate::sema::models::SelectionMode::Typecheck,
                );
                assert!(witness.is_ok(), "conversion witness: {witness:#?}");
            },
        );
        for main in [
            "func main() {}",
            "func main() { var value: Attempt[Wrapped, bool] = 4_i32.tryConvert(); }",
            "func main() { var value: Attempt[Wrapped, bool] = generic(5_i32); }",
        ] {
            let diagnostics =
                crate::test_support::analyze_script_mir_diagnostics(&format!("{prefix}{main}"));
            assert!(diagnostics.is_empty(), "{main}: {diagnostics:#?}");
        }
    }

    #[test]
    fn concrete_blanket_calls_substitute_rhs_as_well_as_self() {
        let source = r#"
interface Select[Rhs] { func select(_ other: Rhs) -> Rhs; }
conform[T] T to Select[T] { func select(_ other: T) -> T { other }; }
class Base { value: int32 }
func choose(_ first: Base, _ second: Base) -> Base { first.select(second) }
struct Box[T] { value: T }
interface SelectValue[Rhs] { func value(_ other: Rhs) -> Rhs; }
conform[T] Box[T] to SelectValue[T] { func value(_ other: T) -> T { other }; }
func unbox(_ first: Box[int32], _ second: int32) -> int32 { first.value(second) }
func main() {}
"#;
        let diagnostics = crate::test_support::analyze_script_diagnostics(source);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}

impl<'ctx> ConstraintSolver<'ctx> {
    fn build_adjustments(deref_steps: usize, autoref_cost: u8) -> Vec<Adjustment<'ctx>> {
        let mut adjustments = Vec::with_capacity(deref_steps + usize::from(autoref_cost > 0));
        adjustments.extend((0..deref_steps).map(|_| Adjustment::Dereference));
        if autoref_cost > 0 {
            adjustments.push(Adjustment::Reference);
        }
        adjustments
    }

    #[inline]
    fn with_receiver_argument(
        arguments: &[ApplyArgument<'ctx>],
        receiver: ApplyArgument<'ctx>,
    ) -> Vec<ApplyArgument<'ctx>> {
        let mut out = Vec::with_capacity(arguments.len() + 1);
        out.push(receiver);
        out.extend_from_slice(arguments);
        out
    }

    pub fn solve_method_call(&mut self, data: MethodCallData<'ctx>) -> SolverResult<'ctx> {
        self.solve_method_call_with_interface(data, None)
    }

    pub(super) fn solve_method_call_with_interface(
        &mut self,
        data: MethodCallData<'ctx>,
        required: Option<crate::hir::StdItem>,
    ) -> SolverResult<'ctx> {
        self.solve_restricted_method_call(data, required, None)
    }

    pub(super) fn solve_native_subscript_call(
        &mut self,
        data: MethodCallData<'ctx>,
        access: crate::compile::context::NativeSubscriptAccess,
    ) -> SolverResult<'ctx> {
        self.solve_restricted_method_call(data, None, Some(access))
    }

    fn solve_restricted_method_call(
        &mut self,
        data: MethodCallData<'ctx>,
        required: Option<crate::hir::StdItem>,
        native: Option<crate::compile::context::NativeSubscriptAccess>,
    ) -> SolverResult<'ctx> {
        self.solve_method_call_at(data, required, native, Vec::new(), Vec::new())
    }

    fn solve_method_call_at(
        &mut self,
        data: MethodCallData<'ctx>,
        required: Option<crate::hir::StdItem>,
        native: Option<crate::compile::context::NativeSubscriptAccess>,
        prefix: Vec<Adjustment<'ctx>>,
        mut visited: Vec<Ty<'ctx>>,
    ) -> SolverResult<'ctx> {
        let required_interface = required.and_then(|item| self.gcx().std_item_def(item));
        let MethodCallData {
            node_id,
            receiver,
            reciever_node,
            reciever_span,
            is_unsafe_context,
            name,
            arguments,
            result,
            span,
            method_ty,
            ..
        } = &data;

        let resolved_receiver = self.structurally_resolve(*receiver);
        // The receiver may be the unresolved result of an overloaded subscript.
        // This also applies through reference/pointer layers. Looking up or
        // auto-referencing it here would admit every matching reference-head
        // extension and reject unrelated arities before the index can resolve.
        if self.autoderef(resolved_receiver).any(|ty| ty.is_infer()) {
            return SolverResult::Deferred;
        }
        if resolved_receiver.is_error() {
            let obligation = Obligation {
                location: data.span,
                goal: Goal::Equal(data.result, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        let mut receiver_variable = None;
        let mut branches = Vec::new();
        let mut seen = FxHashSet::default();
        // Address-derived bodies call their own declared capability,
        // including extra capabilities absent from a get-only bound.
        // The binding still uses ordinary receiver/argument solving.
        let default_address = if name.symbol.as_str() == "__subscript_address" {
            self.gcx()
                .native_subscript_for_accessor(self.current_def)
                .filter(|(_, entry)| {
                    entry.getter == Some(self.current_def) && entry.getter_is_default
                        || entry.setter == Some(self.current_def) && entry.setter_is_default
                })
                .and_then(|(_, entry)| entry.address)
                .filter(|source| {
                    self.gcx().definition_ident(*source).symbol == name.symbol
                        && self.gcx().definition_parent(*source).is_some_and(|parent| {
                            self.gcx().definition_kind(parent) == crate::hir::DefinitionKind::Impl
                        })
                })
        } else {
            None
        };
        for (candidate_ty, deref_steps, referenceable) in
            self.reciever_candidates(*receiver, data.receiver_addressable)
        {
            let candidate_ty = self.structurally_resolve(candidate_ty);
            for autoref_cost in 0..=u8::from(referenceable) {
                let receiver_ty = if autoref_cost == 0 {
                    candidate_ty
                } else {
                    Ty::new(TyKind::Reference(candidate_ty), self.gcx())
                };
                let direct = if let Some(source) = default_address {
                    vec![source]
                } else {
                    self.lookup_instance_candidates_method(
                        candidate_ty,
                        receiver_ty,
                        name.symbol,
                        *span,
                    )
                    .unwrap_or_default()
                };
                for source in direct {
                    if native.is_some_and(|access| {
                        self.gcx()
                            .native_subscript_for_receiver(source, receiver_ty)
                            .is_none_or(|(_, entry)| access.method(entry) != Some(source))
                    }) {
                        continue;
                    }
                    // Operators exclude unrelated inherent declarations.
                    // Primitive requirements have no source conformance record
                    // and remain available through their builtin witness.
                    if required.is_some_and(|item| {
                        self.gcx().definition_parent(source) != required_interface
                            || !crate::mir::primitive_operators::supports(
                                self.gcx(),
                                receiver_ty,
                                item,
                            )
                    }) {
                        continue;
                    }
                    let source = required.map_or(source, |item| {
                        crate::mir::primitive_operators::declaration(self.gcx(), item, *span)
                    });
                    if data
                        .selected
                        .is_some_and(|(selected, _)| selected != source)
                        || !seen.insert((source, receiver_ty, deref_steps, None))
                    {
                        continue;
                    }
                    branches.push(
                        self.method_call_branch(
                            &data,
                            source,
                            receiver_ty,
                            *receiver_variable
                                .get_or_insert_with(|| self.icx.next_ty_var(*reciever_span)),
                            self.gcx().get_type(source),
                            None,
                            data.selected.map(|(_, arguments)| arguments),
                            deref_steps,
                            autoref_cost,
                            &prefix,
                        ),
                    );
                }
                if default_address.is_some() {
                    continue;
                }
                let interfaces = self.method_interfaces(receiver_ty, *span);
                let Some(interfaces) = interfaces else {
                    continue;
                };
                let (candidates, _) = self.interface_method_candidates(
                    receiver_ty,
                    Some(receiver_ty),
                    interfaces,
                    name.symbol,
                    name.span,
                );
                for candidate in candidates {
                    if native.is_some_and(|access| {
                        self.gcx()
                            .native_subscript_for_accessor(candidate.source)
                            .is_none_or(|(_, entry)| access.method(entry) != Some(candidate.source))
                    }) {
                        continue;
                    }
                    if required_interface
                        .is_some_and(|interface| candidate.call_info.method_interface != interface)
                    {
                        continue;
                    }
                    if autoref_cost > 0 && self.gcx().definition_is_clone_method(candidate.source)
                        || data
                            .selected
                            .is_some_and(|(source, _)| source != candidate.source)
                        || !seen.insert((
                            candidate.source,
                            receiver_ty,
                            deref_steps,
                            candidate.instantiation_args,
                        ))
                    {
                        continue;
                    }
                    branches.push(
                        self.method_call_branch(
                            &data,
                            candidate.source,
                            receiver_ty,
                            *receiver_variable
                                .get_or_insert_with(|| self.icx.next_ty_var(*reciever_span)),
                            candidate.candidate_ty,
                            Some(candidate.call_info),
                            data.selected
                                .map(|(_, arguments)| arguments)
                                .or(candidate.instantiation_args),
                            deref_steps,
                            autoref_cost,
                            &prefix,
                        ),
                    );
                }
            }
        }
        if !branches.is_empty() {
            // Native overloads are selected from their inputs. An unresolved
            // key may be produced by another indexed expression; probing now
            // can constrain it to an unrelated range overload and reject its
            // actual producer. Numeric literals still receive normal context,
            // and a single candidate can supply a generic key's expected type.
            if native.is_some()
                && branches.len() > 1
                && arguments
                    .iter()
                    .any(|argument| self.structurally_resolve(argument.ty).is_ty_var())
            {
                return SolverResult::Deferred;
            }
            let apply = ApplyGoalData {
                call_node_id: *node_id,
                callee_node_id: None,
                call_span: *span,
                callee_ty: *method_ty,
                callee_source: None,
                is_unsafe_context: *is_unsafe_context,
                result_ty: *result,
                arguments: Self::with_receiver_argument(
                    arguments,
                    ApplyArgument {
                        id: *reciever_node,
                        label: None,
                        ty: receiver_variable.expect("method candidate receiver"),
                        span: *reciever_span,
                    },
                ),
                skip_labels: required.is_some(),
                input_only_selection: required.is_some() || native.is_some(),
            };
            return SolverResult::Solved(vec![
                Obligation {
                    location: name.span,
                    goal: Goal::Disjunction(branches),
                },
                Obligation {
                    location: *span,
                    goal: Goal::Apply(apply),
                },
            ]);
        }

        // ── Callable field fallback ──────────────────────────────────
        // If no method named `f` was found, check if `f` is a struct field
        // whose type is callable (e.g., `F: Fn[T, T]`).
        // Resolve `self.f(args)` as `(self.f)(args)`.
        if required.is_none() && native.is_none() {
            let mut adjustments = prefix.clone();
            let mut prev: Option<Ty<'ctx>> = None;
            for ty in self.autoderef(*receiver) {
                let ty = self.structurally_resolve(ty);
                if prev.is_some() {
                    adjustments.push(Adjustment::Dereference);
                }
                prev = Some(ty);

                if let Some((field, index)) = self.lookup_field(ty, name.symbol) {
                    if !self
                        .gcx()
                        .is_visibility_allowed(field.visibility, self.current_def)
                    {
                        // Field exists but is not visible; fall through to error.
                        break;
                    }

                    // Record field index and receiver adjustments.
                    self.record_adjustments(*reciever_node, adjustments);
                    self.record_field_index(*node_id, index);

                    // Create a Member goal: resolves `self.f` to the field type.
                    let field_ty = field.ty;

                    // Create an Apply goal: calls the field value with the arguments.
                    let apply_goal = Obligation {
                        location: *span,
                        goal: Goal::Apply(ApplyGoalData {
                            call_node_id: *node_id,
                            callee_node_id: None,
                            call_span: *span,
                            callee_ty: field_ty,
                            callee_source: None,
                            is_unsafe_context: *is_unsafe_context,
                            result_ty: *result,
                            arguments: arguments.clone(),
                            skip_labels: false,
                            input_only_selection: false,
                        }),
                    };

                    // Equate method_ty with the field type so downstream sees the right type.
                    let eq_goal = Obligation {
                        location: name.span,
                        goal: Goal::Equal(*method_ty, field_ty),
                    };

                    return SolverResult::Solved(vec![eq_goal, apply_goal]);
                }
            }
        }

        if required.is_none() && native.is_none() {
            let hidden = self.autoderef(*receiver).any(|ty| {
                self.type_head_from_type(ty)
                    .is_some_and(|head| self.has_invisible_instance_member(head, name.symbol))
                    || self
                        .lookup_field(ty, name.symbol)
                        .is_some_and(|(field, _)| {
                            !self
                                .gcx()
                                .is_visibility_allowed(field.visibility, self.current_def)
                        })
            });
            if !hidden {
                match self.custom_deref_fallback(
                    *receiver,
                    data.receiver_addressable,
                    *span,
                    &prefix,
                    &mut visited,
                ) {
                    Ok(Some((target, prefix, proof))) => {
                        let mut nested = data.clone();
                        nested.receiver = target;
                        nested.receiver_addressable = true;
                        let mut result =
                            self.solve_method_call_at(nested, required, native, prefix, visited);
                        if let SolverResult::Solved(obligations) = &mut result {
                            obligations.extend(proof);
                        }
                        return result;
                    }
                    Err(result) => return result,
                    Ok(None) => {}
                }
            }
        }

        let final_on = self.structurally_resolve(*receiver);
        if final_on.contains_inference() {
            return SolverResult::Deferred;
        }

        // Check if the member exists but is private before falling back to
        // "no such member" — this gives a much more actionable error message.
        let error = if let Some(head) = self.type_head_from_type(final_on) {
            if self.has_invisible_instance_member(head, name.symbol) {
                TypeError::MethodNotVisible {
                    name: name.symbol,
                    on: final_on,
                }
            } else {
                TypeError::NoSuchMember {
                    name: name.symbol,
                    on: final_on,
                }
            }
        } else {
            TypeError::NoSuchMember {
                name: name.symbol,
                on: final_on,
            }
        };

        return SolverResult::Error(vec![Spanned::new(error, name.span)]);
    }

    fn reciever_candidates(
        &self,
        base_ty: Ty<'ctx>,
        mut referenceable: bool,
    ) -> Vec<(Ty<'ctx>, usize, bool)> {
        let mut candidates = Vec::with_capacity(4);
        let mut previous: Option<Ty<'ctx>> = None;
        for (steps, ty) in self.autoderef(base_ty).enumerate() {
            if let Some(previous) = previous {
                referenceable = !matches!(
                    previous.kind(),
                    TyKind::Pointer(_, crate::hir::Mutability::Immutable)
                );
            }
            candidates.push((ty, steps, referenceable));
            previous = Some(ty);
        }
        candidates
    }

    pub fn lookup_instance_candidates_method(
        &self,
        candidate: Ty<'ctx>,
        reciever: Ty<'ctx>,
        name: Symbol,
        span: Span,
    ) -> Option<Vec<DefinitionID>> {
        let autoreferenced = candidate != reciever;
        let all_candidates = self.lookup_instance_candidates(reciever, name);
        if all_candidates.is_empty() {
            return None;
        }

        let mut matching = Vec::with_capacity(all_candidates.len());
        for candidate in all_candidates.into_iter() {
            // Taking an address must not turn a missing Clone on T into an
            // identity copy of &T. Reference copies are explicit: (&value).clone().
            if autoreferenced && self.gcx().definition_is_clone_method(candidate) {
                continue;
            }
            let ty = self.gcx().get_type(candidate);
            let fn_reciever = match ty.kind() {
                TyKind::FnPointer { inputs, .. } => inputs.first().cloned(),
                _ => None,
            };

            let Some(fn_reciever) = fn_reciever else {
                continue;
            };

            let fn_reciever =
                crate::sema::tycheck::utils::normalize_aliases(self.gcx(), fn_reciever);
            let reciever_head = self.type_head_from_type(reciever);
            let fn_reciever_head = self.type_head_from_type(fn_reciever);

            let matches = fn_reciever.needs_instantiation()
                || match (reciever_head, fn_reciever_head) {
                    (Some(a), Some(b)) => a == b,
                    _ => reciever == fn_reciever,
                };

            let inherited = self.gcx().class_ancestry(reciever).iter().any(|ancestor| {
                self.type_head_from_type(*ancestor) == self.type_head_from_type(fn_reciever)
            });
            if matches || inherited {
                matching.push(candidate);
            }
        }

        self.filter_extension_candidates_in_place(&mut matching, reciever, span);
        return Some(matching);
    }

    /// Bounds supplement concrete/blanket conformances; they do not hide them.
    /// Erased values carry their complete interface set in the value type.
    pub(super) fn method_interfaces(
        &self,
        receiver: Ty<'ctx>,
        span: Span,
    ) -> Option<&'ctx [InterfaceReference<'ctx>]> {
        if let TyKind::BoxedExistential { interfaces } = receiver.kind() {
            return Some(interfaces);
        }
        let mut interfaces = self.bounds_for_type_in_scope(receiver);
        if let Some(callable) = crate::sema::models::callable_interface_ref(self.gcx(), receiver) {
            interfaces.push(callable);
        }
        if let Some(roots) = self.concrete_interface_roots(receiver, span) {
            interfaces.extend_from_slice(roots);
        }
        let mut seen = FxHashSet::default();
        interfaces.retain(|interface| seen.insert((interface.id, interface.arguments)));
        (!interfaces.is_empty()).then(|| {
            self.gcx()
                .store
                .arenas
                .global
                .alloc_slice_clone(&interfaces) as &_
        })
    }

    pub(super) fn concrete_interface_roots(
        &self,
        self_ty: Ty<'ctx>,
        span: Span,
    ) -> Option<&'ctx [InterfaceReference<'ctx>]> {
        let ancestry = self.gcx().class_ancestry(self_ty);
        let owners = if ancestry.is_empty() {
            vec![self_ty]
        } else {
            ancestry
        };
        let mut records = Vec::new();
        for owner in owners {
            let head = self.type_head_from_type(owner);
            records.extend(self.gcx().collect_from_databases(|db| {
                db.conformance_records
                    .values()
                    .filter(|record| {
                        head.is_some_and(|head| record.target == head) || record.target.is_blanket()
                    })
                    .map(|record| (owner, *record))
                    .collect::<Vec<_>>()
            }));
        }
        if records.is_empty() {
            return None;
        }

        let mut interfaces = Vec::with_capacity(records.len());
        let mut seen: FxHashSet<InterfaceReference<'ctx>> = FxHashSet::default();
        seen.reserve(records.len());

        for (owner, record) in records {
            if !self.visible_traits.is_empty()
                && !self.visible_traits.contains(&record.interface.id)
            {
                continue;
            }

            if !self.extension_target_matches(record.extension, owner, span) {
                continue;
            }
            // Every interface argument lives in the extension's coordinates,
            // not only Self. A blanket `T: Select[T]` must become
            // `Base: Select[Base]`, never `Base: Select[unbound T]`.
            let Some(interface) =
                crate::sema::impl_engine::deduce_conformance_interface(self.gcx(), &record, owner)
            else {
                continue;
            };
            let iface = InterfaceReference {
                id: interface.id,
                arguments: self.interface_args_with_self(interface, self_ty),
                bindings: interface.bindings,
            };
            if seen.insert(iface) {
                interfaces.push(iface);
            }
        }

        if interfaces.is_empty() {
            return None;
        }

        Some(
            self.gcx()
                .store
                .arenas
                .global
                .alloc_slice_clone(&interfaces),
        )
    }

    fn method_call_branch(
        &self,
        data: &MethodCallData<'ctx>,
        source: DefinitionID,
        receiver: Ty<'ctx>,
        variable: Ty<'ctx>,
        candidate_ty: Ty<'ctx>,
        call_info: Option<InterfaceCallInfo>,
        arguments: Option<GenericArguments<'ctx>>,
        deref_steps: usize,
        autoref_cost: u8,
        prefix: &[Adjustment<'ctx>],
    ) -> DisjunctionBranch<'ctx> {
        let binding = match call_info {
            Some(call_info) => Goal::BindInterfaceMethod(BindInterfaceMethodGoalData {
                node_id: data.node_id,
                var_ty: data.method_ty,
                candidate_ty,
                call_info,
                instantiation_args: arguments,
            }),
            None => Goal::BindOverload(BindOverloadGoalData {
                static_owner: None,
                node_id: data.node_id,
                var_ty: data.method_ty,
                candidate_ty,
                source,
                instantiation_args: arguments,
            }),
        };
        let mut adjustments = prefix.to_vec();
        adjustments.extend(Self::build_adjustments(deref_steps, autoref_cost));
        DisjunctionBranch {
            goal: Goal::BindMethodOverload(BindMethodOverloadGoalData {
                binding: Box::new(binding),
                receiver_node_id: data.reciever_node,
                receiver_constraint: Some((variable, receiver)),
                adjustments,
            }),
            source: Some(source),
            autoref_cost,
            matches_async_preference: self.gcx().definition_is_async(source) == data.prefer_async,
            deref_steps,
        }
    }

    pub(super) fn interface_method_candidates(
        &mut self,
        self_ty: Ty<'ctx>,
        reciever_ty: Option<Ty<'ctx>>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
        name: Symbol,
        name_span: Span,
    ) -> (Vec<InterfaceMethodCandidate<'ctx>>, bool) {
        let mut out = Vec::with_capacity(interfaces.len().saturating_mul(2));
        let mut seen = FxHashSet::default();
        let mut object_safety_violation = false;
        let is_existential_dispatch = matches!(self_ty.kind(), TyKind::BoxedExistential { .. });

        for (table_index, iface) in interfaces.iter().enumerate() {
            let iface_args = self.interface_args_with_self(*iface, self_ty);
            let root = InterfaceReference {
                id: iface.id,
                arguments: iface_args,
                bindings: &[],
            };

            // A partial header is a method template. Its missing arguments
            // are freshened only after selection; do not carry uninstantiated
            // root parameters into a super-interface's argument coordinates.
            let interfaces = if root.arguments.len() < self.gcx().generics_of(root.id).total_count()
            {
                vec![root]
            } else {
                self.collect_interface_with_supers(root)
            };
            for iface_ref in interfaces {
                let Some(requirements) = self.interface_requirements(iface_ref.id) else {
                    continue;
                };

                for method in &requirements.methods {
                    if method.name != name {
                        continue;
                    }
                    if !method.has_self {
                        continue;
                    }
                    if is_existential_dispatch
                        && self.gcx().generics_of(method.id).total_count() > 0
                    {
                        if !object_safety_violation {
                            self.gcx().dcx().emit_error(
                                format!(
                                    "cannot call generic interface method '{}' on an existential value",
                                    self.gcx().symbol_text(method.name)
                                ),
                                Some(name_span),
                            );
                            self.gcx().dcx().emit_info(
                                "methods with their own generic parameters are not object-safe"
                                    .into(),
                                Some(name_span),
                            );
                        }
                        object_safety_violation = true;
                        continue;
                    }

                    // No witness-table slot is computed here. For existential
                    // receivers every candidate that survives the checks above
                    // is dispatchable (has `self`, no method generics) and the
                    // slot is derived at monomorphization time. For abstract
                    // receivers (generic params / projections) generic methods
                    // are legitimate candidates even though they have no slot —
                    // they resolve statically once the receiver is concrete, so
                    // gating candidacy on a slot would reject valid calls.

                    // Only substitute interface-level args (e.g. `Self`) for receiver matching.
                    // Method-generic inference vars are created later, when a branch is selected.
                    let candidate_ty = self.labeled_signature_to_ty(method.signature);
                    let candidate_receiver_ty =
                        instantiate_ty_with_args(self.gcx(), candidate_ty, iface_ref.arguments);

                    if reciever_ty.is_some_and(|receiver| {
                        !self.receiver_matches_method(receiver, candidate_receiver_ty)
                    }) {
                        continue;
                    }

                    // A requirement reached through several super-interface paths
                    // is still one method. Keep distinct instantiations (including
                    // RHS types) and unrelated requirements as separate candidates.
                    if !seen.insert((method.id, iface_ref)) {
                        continue;
                    }

                    let call_info = InterfaceCallInfo {
                        root_interface: root.id,
                        method_interface: iface_ref.id,
                        method_id: method.id,
                        table_index,
                    };

                    out.push(InterfaceMethodCandidate {
                        call_info,
                        candidate_ty,
                        instantiation_args: Some(iface_ref.arguments),
                        source: method.id,
                    });
                }
            }
        }

        (out, object_safety_violation)
    }

    fn receiver_matches_method(&self, receiver: Ty<'ctx>, method_ty: Ty<'ctx>) -> bool {
        let TyKind::FnPointer { inputs, .. } = method_ty.kind() else {
            return false;
        };
        let Some(expected) = inputs.first().cloned() else {
            return false;
        };

        let receiver_head = self.type_head_from_type(receiver);
        let expected_head = self.type_head_from_type(expected);
        match (receiver_head, expected_head) {
            (Some(a), Some(b)) => a == b,
            _ => receiver == expected,
        }
    }

    pub(super) fn interface_args_with_self(
        &self,
        iface: InterfaceReference<'ctx>,
        self_ty: Ty<'ctx>,
    ) -> GenericArguments<'ctx> {
        if iface.arguments.is_empty() {
            return iface.arguments;
        }

        let mut args: Vec<GenericArgument<'ctx>> = Vec::with_capacity(iface.arguments.len());
        args.push(GenericArgument::Type(self_ty));
        args.extend_from_slice(&iface.arguments[1..]);

        self.gcx().store.interners.intern_generic_args(args)
    }

    pub(super) fn labeled_signature_to_ty(&self, sig: &LabeledFunctionSignature<'ctx>) -> Ty<'ctx> {
        let inputs: Vec<_> = sig.inputs.iter().map(|p| p.ty).collect();
        let inputs = self.gcx().store.interners.intern_ty_list(inputs);
        Ty::new(
            TyKind::FnPointer {
                effects: Default::default(),
                inputs,
                output: sig.output,
            },
            self.gcx(),
        )
    }
}
