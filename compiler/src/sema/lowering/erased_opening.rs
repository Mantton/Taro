//! Eligibility for call-scoped opening of an owning existential.
//!
//! An opened call uses a real concrete generic specialization selected from the
//! payload metadata. The erased container is only its bridge ABI, never a proof
//! that `any P` itself conforms to P. Keep these checks shared by source call
//! checking, specialization discovery, imported facts and bridge generation.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{Constraint, GenericArguments, Ty, TyKind},
        tycheck::{
            constraints::canonical_constraints_of,
            utils::normalize_aliases,
            visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
        },
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct OpeningPlan<'ctx> {
    pub parameter: usize,
    pub input: usize,
    pub erased: Ty<'ctx>,
    /// None transfers the owned payload; Some preserves that borrow permission.
    pub borrow: Option<()>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OpeningError {
    MultipleHiddenTypes,
    HiddenResult,
    RelatedInputs,
    UnsupportedInput,
    UnsupportedCall,
    HiddenConstraint,
}

pub(crate) fn contains_parameter(ty: Ty<'_>, index: usize) -> bool {
    struct Find(usize);
    impl<'ctx> TypeVisitor<'ctx> for Find {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            matches!(ty.kind(), TyKind::Parameter(parameter) if parameter.index == self.0)
                || ty.super_visit_with(self)
        }
    }
    ty.visit_with(&mut Find(index))
}

fn container_capability(gcx: Gcx<'_>, interface: DefinitionID) -> bool {
    gcx.std_item_def(StdItem::AnyObject) == Some(interface)
}

/// Identify the single hidden input supported by the initial opening contract.
/// Capability-only generics still operate on the owning container itself.
/// Parent generic coordinates never acquire call-scoped opening authority.
pub(crate) fn plan<'ctx>(
    gcx: Gcx<'ctx>,
    source: DefinitionID,
    arguments: GenericArguments<'ctx>,
) -> Result<Option<OpeningPlan<'ctx>>, OpeningError> {
    let generics = gcx.generics_of(source);
    let mut parameters = Vec::new();
    for constraint in canonical_constraints_of(gcx, source) {
        let Constraint::Bound { ty, interface } = constraint.value else {
            continue;
        };
        let TyKind::Parameter(parameter) = normalize_aliases(gcx, ty).kind() else {
            continue;
        };
        if parameter.index < generics.parent_count || container_capability(gcx, interface.id) {
            continue;
        }
        if let Some(erased) = arguments
            .get(parameter.index)
            .and_then(|argument| argument.ty())
            && matches!(
                normalize_aliases(gcx, erased).kind(),
                TyKind::BoxedExistential { .. }
            )
            && !parameters.contains(&(parameter.index, erased))
        {
            parameters.push((parameter.index, erased));
        }
    }
    let Some(&(parameter, erased)) = parameters.first() else {
        return Ok(None);
    };
    if parameters.len() != 1 {
        return Err(OpeningError::MultipleHiddenTypes);
    }
    if hidden_constraint(gcx, source, arguments, parameter, erased) {
        return Err(OpeningError::HiddenConstraint);
    }
    let signature = gcx.get_signature(source);
    // Async calls bridge only their cold constructors. Source storage analysis
    // still checks every captured input; concrete codegen requires its Native
    // suspension certificate. Defaults run over prepared input storage first.
    if signature.abi.is_some() {
        return Err(OpeningError::UnsupportedCall);
    }
    if contains_parameter(
        normalize_aliases(gcx, gcx.function_body_output(source)),
        parameter,
    ) {
        return Err(OpeningError::HiddenResult);
    }
    let mut input = None;
    for (index, value) in signature.inputs.iter().enumerate() {
        let ty = normalize_aliases(gcx, value.ty);
        if !contains_parameter(ty, parameter) {
            continue;
        }
        if input.is_some() {
            return Err(OpeningError::RelatedInputs);
        }
        let (inner, borrow) = match ty.kind() {
            TyKind::Reference(inner) => (normalize_aliases(gcx, inner), Some(())),
            _ => (ty, None),
        };
        if !matches!(inner.kind(), TyKind::Parameter(value) if value.index == parameter) {
            return Err(OpeningError::UnsupportedInput);
        }
        input = Some((index, borrow));
    }
    let Some((input, borrow)) = input else {
        return Err(OpeningError::UnsupportedInput);
    };
    Ok(Some(OpeningPlan {
        parameter,
        input,
        erased,
        borrow,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::models::GenericArgument;

    #[test]
    fn async_opening_uses_the_same_unambiguous_hidden_input_contract() {
        let prelude = r#"
interface Reader { func read() -> int32; }
struct Counter { value: int32 }
conform Counter to Reader { func read() -> int32 { self.value }; }
func inspect[T: Reader](_ value: &T) async -> int32 { value.read() }
func compare[T: Reader](_ left: &T, _ right: &T) async -> bool { true }
func identity[T: Reader](_ value: T) async -> T { value }
"#;
        for (statement, accepted) in [
            ("var result: int32 = await inspect(&boxed)", true),
            ("var result: bool = await compare(&boxed,&boxed)", false),
            (
                "var result: int32 = await inspect[any Reader](&boxed)",
                false,
            ),
            ("result := await identity(boxed)", false),
        ] {
            let errors = crate::test_support::analyze_language_item_script(
                &format!(
                    "{prelude}\nfunc main() async {{ var boxed: any Reader = Counter {{ value: 7 }}; {statement} }}"
                ),
                false,
                &[],
            );
            assert_eq!(errors.is_empty(), accepted, "{statement}: {errors:#?}");
        }
    }

    #[test]
    fn known_interface_arguments_infer_other_generics_without_exposing_hidden_self() {
        let diagnostics = crate::test_support::analyze_language_item_script(
            r#"
interface Reader[Value] { func read() -> Value; }
struct Counter { value: int32 }
conform Counter to Reader[int32] { func read() -> int32 { self.value }; }
func inspect[Value, T: Reader[Value]](_ value: &T) -> Value { value.read() }
func main() {
    var boxed: any Reader[int32] = Counter { value: 7 }
    value := inspect(&boxed)
}
"#,
            false,
            &[],
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn relative_self_is_not_an_independently_known_generic_result() {
        let prefix = r#"
interface Duplicate[Value = Self] { func duplicate() -> Value; }
struct Counter { value: int32 }
conform Counter to Duplicate { func duplicate() -> Counter { Counter { value: self.value } }; }
func duplicate[Value, T: Duplicate[Value]](_ value: &T) -> Value { value.duplicate() }
"#;
        for statement in [
            "result := duplicate(&boxed)",
            "var result: any Duplicate = duplicate(&boxed)",
        ] {
            let diagnostics = crate::test_support::analyze_language_item_script(
                &format!(
                    "{prefix}\nfunc main() {{ var boxed: any Duplicate = Counter {{ value: 7 }}; {statement} }}"
                ),
                false,
                &[],
            );
            assert!(
                !diagnostics.is_empty(),
                "must not infer a public container as hidden Self: {statement}"
            );
        }
    }

    #[test]
    fn equalities_cannot_join_independently_erased_inputs() {
        let diagnostics = crate::test_support::analyze_language_item_script(
            r#"
interface P { func read() -> int32; }
struct Counter { value: int32 }
conform Counter to P { func read() -> int32 { self.value }; }
func same[T: P, U](_ left: &T, _ right: &U) -> bool where T == U { true }
func main() {
    var left: any P = Counter { value: 1 }
    var right: any P = Counter { value: 2 }
    var result: bool = same(&left, &right)
}
"#,
            false,
            &[],
        );
        assert!(
            !diagnostics.is_empty(),
            "erased container equality is not concrete type identity"
        );
    }

    #[test]
    fn opening_is_call_scoped_and_does_not_grant_existential_self_conformance() {
        let prelude = r#"
interface P { func read() -> int32; }
struct Counter { value: int32 }
conform Counter to P { func read() -> int32 { self.value }; }
func inspect[T: P](_ value: &T) -> int32 { value.read() }
func choose[T: P](_ left: &T, _ right: &T) -> int32 { left.read() }
func identity[T: P](_ value: T) -> T { value }
struct Bound[T: P] { value: T }
"#;
        let errors = |body: &str| {
            crate::test_support::analyze_language_item_script(
                &format!(
                    "{prelude}\nfunc main() {{ var boxed: any P = Counter {{ value: 7 }}; {body} }}"
                ),
                false,
                &[],
            )
        };
        assert!(errors("var result: int32 = inspect(&boxed)").is_empty());
        assert!(errors("var result: int32 = boxed.read()").is_empty());
        for body in [
            "var result: int32 = inspect[any P](&boxed)",
            "var result: int32 = choose(&boxed, &boxed)",
            "result := identity(boxed)",
            "var result: Bound[any P] = Bound[any P] { value: boxed }",
        ] {
            let diagnostics = errors(body);
            assert!(
                diagnostics
                    .iter()
                    .any(|error| error.message.contains("conform")),
                "{body}: {diagnostics:#?}"
            );
        }
    }
    #[test]
    fn opening_does_not_change_generic_layout_or_join_independent_hidden_values() {
        crate::test_support::analyze_script(
            r#"
interface P {}
struct Erased { value: any P }
func read[T: P](_ value: &T) -> int32 { 0 }
func edit[T: P](_ value: &T) -> int32 { 0 }
func consume[T: P](_ value: T) -> int32 { 0 }
func leak[T: P](_ value: T) -> T { value }
func compare[T: P](_ left: &T, _ right: &T) -> int32 { 0 }
func nested[T: P](_ value: &(T,)) -> int32 { 0 }
func main() {}
"#,
            |package, gcx| {
                let erased_id = package
                    .root
                    .declarations
                    .iter()
                    .find(|item| gcx.symbol_text(item.identifier.symbol).as_str() == "Erased")
                    .unwrap()
                    .id;
                let erased = gcx.get_struct_definition(erased_id).fields[0].ty;
                let arguments = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(erased)]);
                for (name, mode) in [("read", Some(())), ("edit", Some(())), ("consume", None)] {
                    let id = package
                        .root
                        .declarations
                        .iter()
                        .find(|item| gcx.symbol_text(item.identifier.symbol).as_str() == name)
                        .unwrap()
                        .id;
                    assert_eq!(
                        plan(gcx, id, arguments),
                        Ok(Some(OpeningPlan {
                            parameter: 0,
                            input: 0,
                            erased,
                            borrow: mode
                        }))
                    );
                }
                for (name, error) in [
                    ("leak", OpeningError::HiddenResult),
                    ("compare", OpeningError::RelatedInputs),
                    ("nested", OpeningError::UnsupportedInput),
                ] {
                    let id = package
                        .root
                        .declarations
                        .iter()
                        .find(|item| gcx.symbol_text(item.identifier.symbol).as_str() == name)
                        .unwrap()
                        .id;
                    assert_eq!(plan(gcx, id, arguments), Err(error));
                }
            },
        );
    }
}

impl<'ctx> Gcx<'ctx> {
    /// Borrow a prepared call argument only to select the concrete generic
    /// environment for its default provider. Normal MIR owns the result and
    /// unwinds already prepared arguments if a later default panics.
    pub(crate) fn erased_default(
        self,
        source: DefinitionID,
        provider: DefinitionID,
        parameter: usize,
    ) -> DefinitionID {
        use crate::sema::models::{
            LabeledFunctionParameter, LabeledFunctionSignature, SyntheticDefinition,
            SyntheticDefinitionKind,
        };
        let kind = SyntheticDefinitionKind::ErasedDefault {
            source,
            provider,
            parameter,
        };
        if let Some(id) =
            self.store
                .synthetic_definitions
                .borrow()
                .iter()
                .find_map(|(id, declaration)| {
                    (id.package() == self.package_index() && declaration.kind == kind)
                        .then_some(*id)
                })
        {
            return id;
        }
        let id = self.allocate_synthetic_id(self.package_index());
        let identity =
            crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(self, source);
        let target = identity[parameter]
            .ty()
            .expect("opened default type parameter");
        let provider_signature = self.get_signature(provider);
        let mut inputs = vec![LabeledFunctionParameter {
            label: None,
            name: self.intern_symbol("source"),
            ty: Ty::new(TyKind::Reference(target), self),
            is_lazy: false,
            default_provider: None,
        }];
        inputs.extend_from_slice(&provider_signature.inputs);
        let signature = self
            .store
            .arenas
            .function_signatures
            .alloc(LabeledFunctionSignature {
                inputs,
                output: provider_signature.output,
                is_variadic: false,
                abi: None,
            });
        self.register_synthetic_definition(
            id,
            SyntheticDefinition {
                kind,
                name: self.intern_symbol("__openedDefault"),
                generics: self.generics_of(source),
                signature,
                span: self.definition_ident(provider).span,
            },
        );
        self.cache_signature(id, signature.clone());
        self.cache_type(id, Ty::from_labeled_signature(self, signature));
        self.update_constraints(id, canonical_constraints_of(self, source));
        id
    }
}

/// Receiver-relative Self may stand for the selected hidden parameter, but
/// must never be inferred as an independently named result/other parameter.
/// In particular Reader[Self] cannot supply a statically known Reader[Value].
pub(crate) fn relative_self_matches_template<'ctx>(
    gcx: Gcx<'ctx>,
    template: crate::sema::models::InterfaceReference<'ctx>,
    provided: crate::sema::models::InterfaceReference<'ctx>,
    parameter: usize,
) -> bool {
    fn ty_matches<'ctx>(
        gcx: Gcx<'ctx>,
        template: Ty<'ctx>,
        provided: Ty<'ctx>,
        parameter: usize,
        depth: u32,
    ) -> bool {
        let template = normalize_aliases(gcx, template);
        let provided = normalize_aliases(gcx, provided);
        if !crate::sema::tycheck::utils::erased_self::has_free_self(provided) {
            return true;
        }
        match (template.kind(), provided.kind()) {
            (TyKind::Parameter(value), TyKind::ExistentialSelf(level)) if level == depth => {
                value.index == parameter
            }
            (TyKind::ExistentialSelf(left), TyKind::ExistentialSelf(right)) if right < depth => {
                left == right
            }
            (TyKind::Reference(left), TyKind::Reference(right)) => {
                ty_matches(gcx, left, right, parameter, depth)
            }
            (TyKind::Pointer(left, lm), TyKind::Pointer(right, rm)) => {
                lm == rm && ty_matches(gcx, left, right, parameter, depth)
            }
            (TyKind::Tuple(left), TyKind::Tuple(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| ty_matches(gcx, *left, *right, parameter, depth))
            }
            (TyKind::Array { element: left, .. }, TyKind::Array { element: right, .. }) => {
                ty_matches(gcx, left, right, parameter, depth)
            }
            (TyKind::Adt(left, la), TyKind::Adt(right, ra))
                if left == right && la.len() == ra.len() =>
            {
                la.iter()
                    .zip(ra)
                    .all(|(left, right)| match (left.ty(), right.ty()) {
                        (Some(left), Some(right)) => ty_matches(gcx, left, right, parameter, depth),
                        (None, None) => true,
                        _ => false,
                    })
            }
            (
                TyKind::FnPointer {
                    effects: le,
                    inputs: li,
                    output: lo,
                },
                TyKind::FnPointer {
                    effects: re,
                    inputs: ri,
                    output: ro,
                },
            ) => {
                le == re
                    && li.len() == ri.len()
                    && li
                        .iter()
                        .zip(ri)
                        .all(|(left, right)| ty_matches(gcx, *left, *right, parameter, depth))
                    && ty_matches(gcx, lo, ro, parameter, depth)
            }
            (
                TyKind::BoxedExistential { interfaces: left },
                TyKind::BoxedExistential { interfaces: right },
            ) => {
                left.len() == right.len()
                    && left.iter().zip(right).all(|(left, right)| {
                        left.id == right.id
                            && left.arguments.len() == right.arguments.len()
                            && left.arguments.iter().zip(right.arguments).all(
                                |(left, right)| match (left.ty(), right.ty()) {
                                    (Some(left), Some(right)) => {
                                        ty_matches(gcx, left, right, parameter, depth + 1)
                                    }
                                    (None, None) => true,
                                    _ => false,
                                },
                            )
                            && left.bindings.iter().all(|left| {
                                right
                                    .bindings
                                    .iter()
                                    .find(|right| right.name == left.name)
                                    .is_some_and(|right| {
                                        ty_matches(gcx, left.ty, right.ty, parameter, depth + 1)
                                    })
                            })
                    })
            }
            _ => false,
        }
    }
    template.id == provided.id
        && template.arguments.len() == provided.arguments.len()
        && template
            .arguments
            .iter()
            .skip(1)
            .zip(provided.arguments.iter().skip(1))
            .all(|(left, right)| match (left.ty(), right.ty()) {
                (Some(left), Some(right)) => ty_matches(gcx, left, right, parameter, 0),
                (None, None) => true,
                _ => false,
            })
        && template.bindings.iter().all(|left| {
            provided
                .bindings
                .iter()
                .find(|right| right.name == left.name)
                .is_some_and(|right| ty_matches(gcx, left.ty, right.ty, parameter, 0))
        })
}

fn hidden_constraint<'ctx>(
    gcx: Gcx<'ctx>,
    source: DefinitionID,
    arguments: GenericArguments<'ctx>,
    parameter: usize,
    erased: Ty<'ctx>,
) -> bool {
    use crate::sema::models::AliasKind;
    struct Contains<'ctx>(Ty<'ctx>);
    impl<'ctx> TypeVisitor<'ctx> for Contains<'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            ty == self.0 || ty.super_visit_with(self)
        }
    }
    fn hidden_projection<'ctx>(
        gcx: Gcx<'ctx>,
        ty: Ty<'ctx>,
        parameter: usize,
        erased: Ty<'ctx>,
    ) -> bool {
        let TyKind::Alias {
            kind: AliasKind::Projection,
            def_id,
            args,
        } = normalize_aliases(gcx, ty).kind()
        else {
            return false;
        };
        if !args.first().and_then(|argument| argument.ty()).is_some_and(
            |ty| matches!(ty.kind(),TyKind::Parameter(value) if value.index==parameter),
        ) {
            return false;
        }
        let TyKind::BoxedExistential { interfaces } = erased.kind() else {
            return false;
        };
        let name = gcx.definition_ident(def_id).symbol;
        let owner = gcx.definition_parent(def_id);
        interfaces
            .iter()
            .flat_map(|root| {
                crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(gcx, *root)
            })
            .filter(|interface| Some(interface.id) == owner)
            .filter_map(|interface| {
                interface
                    .bindings
                    .iter()
                    .find(|binding| binding.name == name)
                    .copied()
            })
            .any(|binding| {
                crate::sema::tycheck::utils::erased_self::has_free_self(normalize_aliases(
                    gcx, binding.ty,
                ))
            })
    }
    fn invalid_relation<'ctx>(
        gcx: Gcx<'ctx>,
        left: Ty<'ctx>,
        right: Ty<'ctx>,
        parameter: usize,
        arguments: GenericArguments<'ctx>,
        erased: Ty<'ctx>,
    ) -> bool {
        let left = normalize_aliases(gcx, left);
        let right = normalize_aliases(gcx, right);
        if [(left, right), (right, left)]
            .into_iter()
            .any(|(projection, other)| {
                hidden_projection(gcx, projection, parameter, erased)
                    && normalize_aliases(
                        gcx,
                        crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                            gcx, other, arguments,
                        ),
                    )
                    .visit_with(&mut Contains(erased))
            })
        {
            return true;
        }
        let nested = |left, right| invalid_relation(gcx, left, right, parameter, arguments, erased);
        match (left.kind(), right.kind()) {
            (TyKind::Parameter(left), TyKind::Parameter(right)) => {
                left.index != right.index && (left.index == parameter || right.index == parameter)
            }
            (TyKind::Reference(left), TyKind::Reference(right))
            | (TyKind::Pointer(left, _), TyKind::Pointer(right, _)) => nested(left, right),
            (TyKind::Array { element: left, .. }, TyKind::Array { element: right, .. }) => {
                nested(left, right)
            }
            (TyKind::Tuple(left), TyKind::Tuple(right)) if left.len() == right.len() => left
                .iter()
                .zip(right)
                .any(|(left, right)| nested(*left, *right)),
            (TyKind::Adt(left, la), TyKind::Adt(right, ra))
                if left == right && la.len() == ra.len() =>
            {
                la.iter()
                    .zip(ra)
                    .any(|(left, right)| match (left.ty(), right.ty()) {
                        (Some(left), Some(right)) => nested(left, right),
                        _ => false,
                    })
            }
            (
                TyKind::FnPointer {
                    effects: _,
                    inputs: li,
                    output: lo,
                },
                TyKind::FnPointer {
                    effects: _,
                    inputs: ri,
                    output: ro,
                },
            ) if li.len() == ri.len() => {
                li.iter().zip(ri).any(|(left, right)| nested(*left, *right)) || nested(lo, ro)
            }
            _ => false,
        }
    }
    canonical_constraints_of(gcx, source)
        .into_iter()
        .any(|constraint| {
            let Constraint::TypeEquality(left, right) = constraint.value else {
                return false;
            };
            invalid_relation(gcx, left, right, parameter, arguments, erased)
        })
}
