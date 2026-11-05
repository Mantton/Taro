use super::ConstraintSolver;
use crate::{
    sema::{
        error::TypeError,
        models::{InterfaceReference, Ty, TyKind},
        tycheck::solve::{Adjustment, DerefGoalData, Goal, Obligation, SolverResult},
    },
    span::{Span, Spanned},
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_deref(&mut self, data: DerefGoalData<'ctx>) -> SolverResult<'ctx> {
        let DerefGoalData {
            operand_ty,
            operand_node,
            receiver_addressable,
            is_unsafe_context,
            result_ty,
            span,
        } = data;

        // Resolve the operand type
        let operand_ty = self.structurally_resolve(operand_ty);

        match operand_ty.kind() {
            TyKind::Pointer(_, _) if !is_unsafe_context => SolverResult::Error(vec![Spanned::new(
                TypeError::UnsafePointerDereference,
                span,
            )]),
            TyKind::Pointer(inner, _) | TyKind::Reference(inner) => {
                // Successfully dereferenced - unify result with inner type
                self.solve_equality(span, result_ty, inner)
            }
            TyKind::Infer(_) => {
                // Operand is still an inference variable - defer until it's resolved
                SolverResult::Deferred
            }
            TyKind::Error => {
                // Error type - propagate error
                SolverResult::Solved(vec![])
            }
            _ => {
                match self.custom_deref_step(operand_ty, receiver_addressable, span) {
                    Ok(Some(step)) => {
                        self.record_adjustments(operand_node, step.adjustments);
                        let mut obligations: Vec<_> = step.obligation.into_iter().collect();
                        obligations.push(Obligation {
                            location: span,
                            goal: Goal::ConstraintEqual(result_ty, step.target),
                        });
                        return SolverResult::Solved(obligations);
                    }
                    Err(error) => return error,
                    Ok(None) => {}
                }
                // Cannot dereference this type
                let error = Spanned::new(TypeError::CannotDereference { ty: operand_ty }, span);
                SolverResult::Error(vec![error])
            }
        }
    }
}

/// A normal interface call returning a reference; callers choose whether to
/// read the referent explicitly (`*`) or continue member lookup through it.
pub(super) struct CustomDerefStep<'ctx> {
    pub adjustments: Vec<Adjustment<'ctx>>,
    pub target: Ty<'ctx>,
    pub obligation: Option<Obligation<'ctx>>,
}

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn custom_deref_step(
        &mut self,
        receiver: Ty<'ctx>,
        addressable: bool,
        span: Span,
    ) -> Result<Option<CustomDerefStep<'ctx>>, SolverResult<'ctx>> {
        let Some(interface_id) = self.gcx().std_item_def(crate::hir::StdItem::Deref) else {
            return Ok(None);
        };
        let Some(requirements) = self.interface_requirements(interface_id) else {
            return Ok(None);
        };
        let Some(method) = requirements
            .methods
            .iter()
            .find(|method| method.name.as_str() == "deref")
        else {
            return Ok(None);
        };
        for reference_receiver in [false, true] {
            if reference_receiver && !addressable {
                continue;
            }
            let self_ty = if reference_receiver {
                Ty::new(TyKind::Reference(receiver), self.gcx())
            } else {
                receiver
            };
            let Some(roots) = self.method_interfaces(self_ty, span) else {
                continue;
            };
            let interface = roots
                .iter()
                .flat_map(|root| self.collect_interface_with_supers(*root))
                .find(|interface| interface.id == interface_id);
            let Some(interface) = interface else { continue };
            let arguments = self.interface_args_with_self(interface, self_ty);
            let signature =
                crate::sema::tycheck::utils::instantiate::instantiate_signature_with_args(
                    self.gcx(),
                    method.signature,
                    arguments,
                );
            let result = self.structurally_resolve(signature.output);
            let TyKind::Reference(target) = result.kind() else {
                return Err(SolverResult::Error(vec![Spanned::new(
                    TypeError::CannotDereference { ty: receiver },
                    span,
                )]));
            };
            if matches!(self_ty.kind(), TyKind::BoxedExistential { .. })
                && matches!(target.kind(), TyKind::Alias { kind: crate::sema::models::AliasKind::Projection, args, .. } if args.first().and_then(|argument| argument.ty()).is_some_and(|source| matches!(source.kind(), TyKind::BoxedExistential { .. })))
            {
                return Err(SolverResult::Error(vec![Spanned::new(
                    TypeError::ErasedMethodUsesHiddenType,
                    span,
                )]));
            }
            if crate::sema::tycheck::utils::unresolved::ty_contains_unresolved_inference(result) {
                return Err(SolverResult::Deferred);
            }
            let mut adjustments = Vec::with_capacity(2);
            if reference_receiver {
                adjustments.push(Adjustment::Reference);
            }
            adjustments.push(Adjustment::DerefCall {
                method: method.id,
                arguments,
                result,
            });
            return Ok(Some(CustomDerefStep {
                adjustments,
                target,
                obligation: (!matches!(self_ty.kind(), TyKind::BoxedExistential { .. })).then_some(
                    Obligation {
                        location: span,
                        goal: Goal::Conforms {
                            ty: self_ty,
                            interface: InterfaceReference {
                                arguments,
                                ..interface
                            },
                        },
                    },
                ),
            }));
        }
        Ok(None)
    }

    /// Try one user Deref after exhausting the builtin reference/pointer chain.
    /// Bound the type walk without adding checks to the generated program.
    pub(super) fn custom_deref_fallback(
        &mut self,
        receiver: Ty<'ctx>,
        addressable: bool,
        span: Span,
        prefix: &[Adjustment<'ctx>],
        visited: &mut Vec<Ty<'ctx>>,
    ) -> Result<
        Option<(Ty<'ctx>, Vec<Adjustment<'ctx>>, Option<Obligation<'ctx>>)>,
        SolverResult<'ctx>,
    > {
        let chain: Vec<_> = self
            .autoderef(receiver)
            .map(|ty| self.structurally_resolve(ty))
            .collect();
        let source = *chain.last().expect("receiver");
        let addressable = chain.iter().rev().nth(1).map_or(addressable, |previous| {
            !matches!(
                previous.kind(),
                TyKind::Pointer(_, crate::hir::Mutability::Immutable)
            )
        });
        let Some(step) = self.custom_deref_step(source, addressable, span)? else {
            return Ok(None);
        };
        if visited.len() >= 32 || visited.contains(&source) {
            return Err(SolverResult::Error(vec![Spanned::new(
                TypeError::DerefCycle { ty: source },
                span,
            )]));
        }
        visited.push(source);
        let mut adjustments = prefix.to_vec();
        adjustments.extend((1..chain.len()).map(|_| Adjustment::Dereference));
        adjustments.extend(step.adjustments);
        adjustments.push(Adjustment::Dereference);
        Ok(Some((step.target, adjustments, step.obligation)))
    }
}

#[cfg(test)]
mod tests {
    use crate::{hir::StdItem, test_support::analyze_language_item_script};
    const INTERFACE: &str = "interface Deref { type Target; func deref() -> &Self::Target; }";
    fn diagnostics(source: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        analyze_language_item_script(
            &format!("{INTERFACE}\n{source}"),
            true,
            &[(StdItem::Deref, "Deref")],
        )
    }

    #[test]
    fn custom_deref_uses_value_or_storage_receivers_and_preserves_own_members() {
        let source = r#"
struct Point { value: int32 }
extend Point { func read() -> int32 { self.value }; func flag() -> int32 { 1 }; }
struct Box { point: Point }
extend Box { func flag() -> bool { true }; }
conform &Box to Deref { type Target = Point; func deref() -> &Point { &self.point }; }
struct View[T] { target: &T }
conform[T] View[T] to Deref { type Target = T; func deref() -> &T { self.target }; }
func read[T: Deref[Target = Point]](_ value: T) -> int32 { value.value }
func target[T: Deref](_ value: T) -> &T::Target { &*value }
func erased(_ value: any Deref[Target = Point]) -> int32 { value.value }
func erasedTarget[T](_ value: any Deref[Target = T]) -> &T { &*value }
func makeView[T](_ target: &T) -> View[T] { View { target } }
func main() {
    var box = Box { point: Point { value: 1 } }
    var copy: Point = *box
    box.value = 2
    var value: int32 = box.read()
    var own: bool = box.flag()
    var view = View { target: &box }
    view.value = 3
    var nested: int32 = view.read()
    var builtin: Box = *&box
    var pointAddress: &Point = &*box
    var fieldAddress: &int32 = &view.value
    *box = Point { value: 7 }
    var tuple = (1_i32, 2_i32)
    var tupleView = View { target: &tuple }
    var first = tupleView.0
    tupleView.1 = 3
    makeView(&tuple).1 = 4
    makeView(&box).value = 8
}
"#;
        let errors = diagnostics(source);
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn deref_cycles_are_diagnosed_only_when_lookup_needs_the_target() {
        let definitions = "struct Loop { next: &Loop }; conform Loop to Deref { type Target = Loop; func deref() -> &Loop { self.next }; }";
        let errors = diagnostics(&format!(
            "{definitions}; func read(_ value: Loop) -> &Loop {{ value.next }}; func main() {{}}"
        ));
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = diagnostics(&format!(
            "{definitions}; func read(_ value: Loop) -> int32 {{ value.missing }}; func main() {{}}"
        ));
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("Deref lookup has a cycle")),
            "{errors:#?}"
        );
    }

    #[test]
    fn deref_does_not_satisfy_target_bounds_or_erase_pointer_safety() {
        for (source, expected) in [
            (
                "struct Point { value: int32 }; interface Read { func read() -> int32; }; conform Point to Read { func read() -> int32 { self.value }; }; struct View { target: &Point }; conform View to Deref { type Target = Point; func deref() -> &Point { self.target }; }; func accept[T: Read](_ value: T) {}; func main() { var point = Point { value: 1 }; accept(View { target: &point }); }",
                "does not conform",
            ),
            (
                "struct Point { value: int32 }; struct View { pointer: *mut Point }; conform &View to Deref { type Target = *mut Point; func deref() -> &*mut Point { &self.pointer }; }; func read(_ view: &View) -> int32 { view.value }; func main() {}",
                "unsafe",
            ),
            (
                "struct Point { value: int32 }; struct View { target: &Point }; extend View { func deref() -> &Point { self.target }; }; func main() { var point = Point { value: 1 }; var view = View { target: &point }; var copy = *view; }",
                "cannot dereference",
            ),
        ] {
            let errors = diagnostics(source);
            assert!(
                errors.iter().any(|error| error.message.contains(expected)),
                "{source}: {errors:#?}"
            );
            assert!(
                !errors.iter().any(|error| error.message == "expected ';'"),
                "parse recovery is not a safety oracle: {errors:#?}"
            );
        }
    }

    #[test]
    fn deref_respects_readonly_storage_and_initializer_boundaries() {
        for (source, expected) in [
            (
                "struct Point { readonly value: int32 }; struct View { target: &Point }; conform View to Deref { type Target = Point; func deref() -> &Point { self.target }; }; func write(_ view: View) { view.value = 3 }; func main() {}",
                "immutable field",
            ),
            (
                "struct Point { value: int32 }; class View { target: &Point }; conform View to Deref { type Target = Point; func deref() -> &Point { self.target }; }; extend View { init(_ target: &Point) { self.target = target }; convenience init(_ target: &Point, _ flag: bool) { self.init(target); var copy = self.value }; }; func main() {}",
                "initialization",
            ),
            (
                "struct Point { value: int32 }; struct View { target: Point }; conform &View to Deref { type Target = Point; func deref() -> &Point { &self.target }; }; extend View { init() { self.target = Point { value: 1 }; var copy = self.value }; }; func main() {}",
                "initialization",
            ),
        ] {
            let errors = diagnostics(source);
            assert!(
                errors.iter().any(|error| error.message.contains(expected)),
                "{errors:#?}"
            );
        }
    }

    #[test]
    fn erased_deref_requires_a_known_target_for_value_reads() {
        let errors =
            diagnostics("func read(_ value: any Deref) { var copy = *value }; func main() {}");
        assert!(
            !errors.is_empty(),
            "an erased target needs an associated binding"
        );
    }

    #[test]
    fn deref_language_item_requires_a_reference_to_its_associated_target() {
        for interface in [
            "interface Deref { type Target; func deref() -> Self::Target; }",
            "interface Deref { type Target; func deref(_ extra: int32) -> &Self::Target; }",
        ] {
            let errors = analyze_language_item_script(
                &format!("{interface}; func main() {{}}"),
                false,
                &[(StdItem::Deref, "Deref")],
            );
            assert!(
                errors
                    .iter()
                    .any(|error| error.message.contains("Deref must declare")),
                "{errors:#?}"
            );
        }
    }
}
