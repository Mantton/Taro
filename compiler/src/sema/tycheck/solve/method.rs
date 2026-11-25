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

/// A discovered declaration with its receiver adjustment. Looking it up does
/// not allocate signature variables or bind the receiver's literal types.
pub(super) struct MethodCandidate<'ctx> {
    pub source: DefinitionID,
    pub receiver: Ty<'ctx>,
    pub signature: Ty<'ctx>,
    pub header: super::ExtensionHeaderMatch,
    pub interface: Option<InterfaceCallInfo>,
    pub arguments: Option<GenericArguments<'ctx>>,
    pub deref_steps: usize,
    pub autoref_cost: u8,
}

pub(super) enum ReceiverResolution {
    Ready,
    Deferred,
    Inferred,
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
                        .find(|declaration| gcx.symbol_text(declaration.identifier.symbol).as_str() == name)
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
    pub(super) fn method_application(
        data: &MethodCallData<'ctx>,
        method_ty: Ty<'ctx>,
        receiver: Ty<'ctx>,
        skip_labels: bool,
        input_only_selection: bool,
    ) -> ApplyGoalData<'ctx> {
        let mut arguments = Vec::with_capacity(data.arguments.len() + 1);
        arguments.push(ApplyArgument {
            is_spread: false,
            is_lazy_wrapped: false,
            contains_await: false,
            deferred_return_scope: None,
            id: data.reciever_node,
            label: None,
            ty: receiver,
            span: data.reciever_span,
        });
        arguments.extend_from_slice(&data.arguments);
        ApplyGoalData {
            call_node_id: data.node_id,
            callee_node_id: None,
            call_span: data.span,
            callee_ty: method_ty,
            callee_source: None,
            is_unsafe_context: data.is_unsafe_context,
            result_ty: data.result,
            arguments,
            skip_labels,
            input_only_selection,
        }
    }

    pub fn solve_method_call(&mut self, mut data: MethodCallData<'ctx>) -> SolverResult<'ctx> {
        if let Some(node) = data.pending_selection.take() {
            let Some(&source) = self.overload_sources.get(&node) else {
                return SolverResult::Deferred;
            };
            let arguments = self.instantiation_args.get(&node).copied().unwrap_or_default();
            data.selected = Some((source, arguments));
        }
        let interface = data.interface;
        self.solve_restricted_method_call(data, interface, None)
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
            ..
        } = &data;

        // The operator goal may retry this lookup before its receiver has a
        // concrete type. A failed attempt must not leave an unconstrained
        // signature variable in the shared inference context.
        let icx = self.icx.clone();
        let method_ty =
            std::cell::LazyCell::new(|| data.method_ty.unwrap_or_else(|| icx.next_ty_var(*span)));
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

        // Operators and native subscripts keep their own lookup; see
        // `method_interfaces_for_call` for the guard this enables.
        let literal_guard = required.is_none() && native.is_none();
        let mut methods = Vec::new();
        let mut seen = FxHashSet::default();
        // Address-derived bodies call their own declared capability,
        // including extra capabilities absent from a get-only bound.
        // The binding still uses ordinary receiver/argument solving.
        let default_address = if self.gcx().symbol_eq(name.symbol, "__subscript_address") {
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
                    vec![(source, super::ExtensionHeaderMatch::Independent)]
                } else {
                    self.lookup_instance_candidates_method(
                        candidate_ty,
                        receiver_ty,
                        name.symbol,
                        *span,
                    )
                };
                for (source, header) in direct {
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
                    methods.push(MethodCandidate {
                        source,
                        receiver: receiver_ty,
                        signature: self.gcx().get_type(source),
                        header,
                        interface: None,
                        arguments: data.selected.map(|(_, args)| args),
                        deref_steps,
                        autoref_cost,
                    });
                }
                if default_address.is_some() {
                    continue;
                }
                let interfaces = self.method_interfaces_for_call(receiver_ty, *span, literal_guard);
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
                    let duplicate_builtin_operator = seen
                        .contains(&(candidate.source, receiver_ty, deref_steps, None))
                        && candidate.instantiation_args.is_some_and(|args| {
                            crate::mir::primitive_operators::ITEMS.iter().any(|&item| {
                                self.gcx().std_item_def(item)
                                    == Some(candidate.call_info.method_interface)
                                    && crate::mir::primitive_operators::interface_for_type(
                                        self.gcx(),
                                        receiver_ty,
                                        item,
                                    )
                                    .is_some_and(|builtin| builtin.arguments == args)
                            })
                        });
                    if autoref_cost > 0 && self.gcx().definition_is_clone_method(candidate.source)
                        || duplicate_builtin_operator
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
                    methods.push(MethodCandidate {
                        source: candidate.source,
                        receiver: receiver_ty,
                        signature: candidate.candidate_ty,
                        header: super::ExtensionHeaderMatch::Independent,
                        interface: Some(candidate.call_info),
                        arguments: data
                            .selected
                            .map(|(_, args)| args)
                            .or(candidate.instantiation_args),
                        deref_steps,
                        autoref_cost,
                    });
                }
            }
        }
        if literal_guard && !methods.is_empty() && resolved_receiver.contains_inference() {
            match self.resolve_method_receiver(&data, resolved_receiver, &mut methods) {
                ReceiverResolution::Ready => {}
                ReceiverResolution::Deferred => return SolverResult::Deferred,
                ReceiverResolution::Inferred => {
                    return self.solve_method_call_at(data, required, native, prefix, visited);
                }
            }
        }
        if !methods.is_empty() {
            // Native overloads are selected from their inputs. An unresolved
            // key may be produced by another indexed expression; probing now
            // can constrain it to an unrelated range overload and reject its
            // actual producer. Numeric literals still receive normal context,
            // and a single candidate can supply a generic key's expected type.
            if native.is_some()
                && methods.len() > 1
                && arguments
                    .iter()
                    .any(|argument| self.structurally_resolve(argument.ty).is_ty_var())
            {
                return SolverResult::Deferred;
            }
            let variable = self.icx.next_ty_var(*reciever_span);
            let branches = methods
                .iter()
                .map(|candidate| {
                    self.method_call_branch(&data, *method_ty, variable, candidate, &prefix)
                })
                .collect();
            let apply = Self::method_application(
                &data,
                *method_ty,
                variable,
                required.is_some(),
                required.is_some() || native.is_some(),
            );
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

                if let Some((field, field_ty, visibility)) = self.lookup_field(ty, name.symbol) {
                    if !self
                        .gcx()
                        .is_visibility_allowed(visibility, self.current_def)
                    {
                        // Field exists but is not visible; fall through to error.
                        break;
                    }

                    if let Some(result) = self.solve_early_interface_call(&data, &prefix, true) {
                        return result;
                    }

                    // Record field index and receiver adjustments.
                    self.record_adjustments(*reciever_node, adjustments);
                    self.record_field(*node_id, field);

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
                        .is_some_and(|(_, _, visibility)| {
                            !self
                                .gcx()
                                .is_visibility_allowed(visibility, self.current_def)
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
            if required.is_none()
                && native.is_none()
                && default_address.is_none()
                && let Some(result) = self.solve_early_interface_call(&data, &prefix, false)
            {
                return result;
            }
            return SolverResult::Deferred;
        }

        if required == Some(crate::hir::StdItem::Closeable)
            && let Some(id) = required_interface
        {
            let arguments = self
                .gcx()
                .store
                .interners
                .intern_generic_args(vec![GenericArgument::Type(final_on)]);
            let interface = InterfaceReference {
                id,
                arguments,
                bindings: &[],
            };
            return SolverResult::Error(vec![Spanned::new(
                TypeError::NonConformance { ty: final_on, interface },
                name.span,
            )]);
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

    /// A specialized implementation's existence cannot supply a receiver
    /// width. A declared argument or result can, when a viable independent
    /// signature determines it and all viable signatures agree.
    fn resolve_method_receiver(
        &self,
        data: &MethodCallData<'ctx>,
        receiver: Ty<'ctx>,
        methods: &mut Vec<MethodCandidate<'ctx>>,
    ) -> ReceiverResolution {
        // A direct method with incompatible inputs must not hide class
        // interface candidates still waiting for a concrete receiver.
        if data.selected.is_none()
            && self
                .autoderef(receiver)
                .any(|ty| self.gcx().is_class_type(ty))
            && !methods
                .iter()
                .any(|method| method.header == super::ExtensionHeaderMatch::NeedsLiteralType)
        {
            methods.retain(|method| {
                method.interface.is_some()
                    || self.probe_method_signature(data, method, &[]).is_some()
            });
        }
        self.resolve_specialized_receivers(receiver, methods, |method, literals| {
            self.probe_method_signature(data, method, literals)
        })
    }

    pub(super) fn resolve_specialized_receivers(
        &self,
        receiver: Ty<'ctx>,
        methods: &mut Vec<MethodCandidate<'ctx>>,
        probe: impl Fn(&MethodCandidate<'ctx>, &[Ty<'ctx>]) -> Option<Vec<Option<Ty<'ctx>>>>,
    ) -> ReceiverResolution {
        use super::ExtensionHeaderMatch::{Independent, NeedsLiteralType};
        use crate::sema::tycheck::utils::unresolved::inference_variables;
        if !methods
            .iter()
            .any(|method| method.header == NeedsLiteralType)
        {
            return ReceiverResolution::Ready;
        }
        let literals: Vec<_> = inference_variables(receiver)
            .into_iter()
            .filter(|&ty| self.icx.unresolved_numeric_var(ty).is_some())
            .collect();
        let mut dependent = false;
        let mut independent = false;
        let mut common: Option<Vec<Option<Ty<'ctx>>>> = None;
        methods.retain(|method| {
            let Some(widths) = probe(method, &literals) else {
                return false;
            };
            dependent |= method.header == NeedsLiteralType;
            independent |= method.header == Independent;
            if let Some(common) = &mut common {
                for (width, other) in common.iter_mut().zip(widths) {
                    if *width != other {
                        *width = None;
                    }
                }
            } else {
                common = Some(widths);
            }
            true
        });
        if !dependent {
            return ReceiverResolution::Ready;
        }
        if independent {
            let mut progress = false;
            for (literal, width) in literals.into_iter().zip(common.into_iter().flatten()) {
                if let Some(width) = width {
                    // Each literal was open on entry; only concrete numeric
                    // types from rolled-back probes reach this point.
                    self.unify(literal, width)
                        .expect("agreed receiver literal type");
                    progress = true;
                }
            }
            if progress {
                return ReceiverResolution::Inferred;
            }
        }
        ReceiverResolution::Deferred
    }

    fn method_header_match(
        &self,
        method: DefinitionID,
        owner: Ty<'ctx>,
        span: Span,
    ) -> super::ExtensionHeaderMatch {
        use super::ExtensionHeaderMatch::{Independent, Mismatch};
        let Some(extension) = self.gcx().definition_parent(method) else {
            return Independent;
        };
        if self.gcx().definition_kind(extension) != crate::hir::DefinitionKind::Impl {
            return Independent;
        }
        let mut result = self.match_extension_header(extension, owner, owner, span);
        if result == Mismatch {
            for ancestor in self.gcx().class_ancestry(owner).into_iter().skip(1) {
                result = self.match_extension_header(extension, ancestor, owner, span);
                if result != Mismatch {
                    break;
                }
            }
        }
        result
    }

    /// Probe the declaration and call without defaulting. A pending constraint
    /// is still possible. Only concrete numeric types can escape the snapshot.
    fn probe_method_signature(
        &self,
        data: &MethodCallData<'ctx>,
        candidate: &MethodCandidate<'ctx>,
        literals: &[Ty<'ctx>],
    ) -> Option<Vec<Option<Ty<'ctx>>>> {
        self.probe_receiver_widths(literals, |fork| {
            let signature = self.icx.next_ty_var(data.span);
            let receiver = self.icx.next_ty_var(data.reciever_span);
            let branch = self.method_call_branch(data, signature, receiver, candidate, &[]);
            fork.obligations.push_back(Obligation {
                location: data.span,
                goal: branch.goal,
            });
            fork.obligations.push_back(Obligation {
                location: data.span,
                goal: Goal::Apply(Self::method_application(
                    data, signature, receiver, false, false,
                )),
            });
        })
    }

    pub(super) fn probe_receiver_widths(
        &self,
        literals: &[Ty<'ctx>],
        enqueue: impl FnOnce(&mut ConstraintSolver<'ctx>),
    ) -> Option<Vec<Option<Ty<'ctx>>>> {
        self.gcx()
            .dcx()
            .with_deferred_diagnostics(|| {
                self.icx.probe(|_| {
                    let mut fork = self.fork_for_lookup();
                    enqueue(&mut fork);
                    let mut driver = super::SolverDriver::new(fork);
                    driver.allow_fallbacks = false;
                    driver.solve_to_fixpoint().ok()?;
                    Some(
                        literals
                            .iter()
                            .map(|&literal| {
                                let ty = self.icx.shallow_resolve(literal);
                                (!ty.is_infer()).then_some(ty)
                            })
                            .collect(),
                    )
                })
            })
            .0
    }

    pub(super) fn reciever_candidates(
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

    pub(super) fn lookup_instance_candidates_method(
        &self,
        candidate: Ty<'ctx>,
        reciever: Ty<'ctx>,
        name: Symbol,
        span: Span,
    ) -> Vec<(DefinitionID, super::ExtensionHeaderMatch)> {
        let autoreferenced = candidate != reciever;
        let all_candidates = self.lookup_instance_candidates(reciever, name);

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
                let header = self.method_header_match(candidate, reciever, span);
                if header != super::ExtensionHeaderMatch::Mismatch {
                    matching.push((candidate, header));
                }
            }
        }

        matching
    }

    /// The interfaces a method call looks through on one receiver candidate.
    ///
    /// While the candidate still holds untyped literals (`Boxed[{integer}]`),
    /// its own conformance records cannot be matched, so the bounds in scope
    /// would stand in for them. A bound another call left pending on it
    /// (`Boxed[{integer}]: A`) is not the set the typed receiver would see;
    /// such a candidate leaves those to the early binding, which weighs every
    /// record and bound, or to the deferral. On an unresolved class a known
    /// ancestor may supply only part of the overload set. Early interface
    /// lookup considers both the derived class and all its ancestors.
    fn method_interfaces_for_call(
        &self,
        receiver: Ty<'ctx>,
        span: Span,
        literal_guard: bool,
    ) -> Option<&'ctx [InterfaceReference<'ctx>]> {
        if literal_guard && receiver.contains_inference() && self.gcx().is_class_type(receiver) {
            return None;
        }
        let bounds = !(literal_guard && self.only_open_literals(receiver));
        self.collect_method_interfaces(receiver, span, bounds)
    }

    /// Bounds supplement concrete/blanket conformances; they do not hide them.
    /// Erased values carry their complete interface set in the value type.
    pub(super) fn method_interfaces(
        &self,
        receiver: Ty<'ctx>,
        span: Span,
    ) -> Option<&'ctx [InterfaceReference<'ctx>]> {
        self.collect_method_interfaces(receiver, span, true)
    }

    fn collect_method_interfaces(
        &self,
        receiver: Ty<'ctx>,
        span: Span,
        bounds: bool,
    ) -> Option<&'ctx [InterfaceReference<'ctx>]> {
        if let TyKind::BoxedExistential { interfaces } = receiver.kind() {
            return Some(interfaces);
        }
        let mut interfaces = if bounds {
            self.bounds_for_member_lookup(receiver)
        } else {
            Vec::new()
        };
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
                .alloc_slice_copy(&interfaces) as &_
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
        let normalized_self = crate::sema::tycheck::utils::normalize_aliases(self.gcx(), self_ty);
        let is_tuple = matches!(normalized_self.kind(), TyKind::Tuple(_));
        if records.is_empty() && !is_tuple {
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
            if !self.visible_traits.is_empty() {
                self.gcx()
                    .store
                    .trait_visibility_uses
                    .borrow_mut()
                    .insert(record.interface.id);
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

        if is_tuple {
            for &item in crate::mir::tuple_conformances::CONFORMANCE_ITEMS {
                let Some(interface_id) = self.gcx().std_item_def(item) else {
                    continue;
                };
                let always_visible = matches!(
                    item,
                    crate::hir::StdItem::PartialEq | crate::hir::StdItem::PartialOrd
                );
                if !always_visible
                    && !self.visible_traits.is_empty()
                    && !self.visible_traits.contains(&interface_id)
                {
                    continue;
                }
                if !self.visible_traits.is_empty() && self.visible_traits.contains(&interface_id) {
                    self.gcx()
                        .store
                        .trait_visibility_uses
                        .borrow_mut()
                        .insert(interface_id);
                }
                let mut args = vec![GenericArgument::Type(self_ty)];
                if crate::mir::tuple_conformances::is_rhs_parameterized(item) {
                    args.push(GenericArgument::Type(self_ty));
                }
                let iface = InterfaceReference {
                    id: interface_id,
                    arguments: self.gcx().store.interners.intern_generic_args(args),
                    bindings: &[],
                };
                if seen.insert(iface) {
                    interfaces.push(iface);
                }
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
                .alloc_slice_copy(&interfaces),
        )
    }

    pub(super) fn method_call_branch(
        &self,
        data: &MethodCallData<'ctx>,
        method_ty: Ty<'ctx>,
        variable: Ty<'ctx>,
        candidate: &MethodCandidate<'ctx>,
        prefix: &[Adjustment<'ctx>],
    ) -> DisjunctionBranch<'ctx> {
        let MethodCandidate {
            source,
            receiver,
            signature: candidate_ty,
            interface: call_info,
            arguments,
            deref_steps,
            autoref_cost,
            ..
        } = *candidate;
        let binding = match call_info {
            Some(call_info) => Goal::BindInterfaceMethod(BindInterfaceMethodGoalData {
                node_id: data.node_id,
                var_ty: method_ty,
                candidate_ty,
                call_info,
                instantiation_args: arguments,
                published_projections: Vec::new(),
            }),
            None => Goal::BindOverload(BindOverloadGoalData {
                static_owner: None,
                node_id: data.node_id,
                var_ty: method_ty,
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
