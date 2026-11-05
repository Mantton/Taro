//! Build inherited method families and validate overrides before body lookup.
//! A family survives replacement; implementation owner substitutions do not.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::{
        models::{ClassMethod, Ty, TyKind},
        tycheck::utils::{generics::GenericsBuilder, instantiate::instantiate_ty_with_args},
    },
};
use rustc_hash::{FxHashMap, FxHashSet};
mod subscripts;
#[derive(Clone, Copy)]
struct Method {
    id: hir::DefinitionID,
    is_final: bool,
    is_override: bool,
    returns_self: bool,
}

pub fn run(package: &hir::Package, gcx: Gcx<'_>) -> CompileResult<()> {
    struct Collector<'ctx> {
        gcx: Gcx<'ctx>,
        classes: Vec<hir::DefinitionID>,
        methods: FxHashMap<hir::DefinitionID, Vec<Method>>,
        subscripts: FxHashMap<hir::DefinitionID, Vec<hir::DefinitionID>>,
    }
    impl HirVisitor for Collector<'_> {
        fn visit_declaration(&mut self, node: &hir::Declaration) {
            if let hir::DeclarationKind::Struct(value) = &node.kind
                && value.class_header.is_some()
            {
                self.classes.push(node.id);
            }
            if let hir::DeclarationKind::Function(function) = &node.kind
                && (function.is_final || function.is_override)
            {
                self.gcx.dcx().emit_error(
                    "final/override requires a class instance method".into(),
                    Some(node.span),
                );
            }
            if let hir::DeclarationKind::Impl(value) = &node.kind {
                let class = self
                    .gcx
                    .get_impl_target_ty(node.id)
                    .filter(|ty| self.gcx.is_class_type(*ty));
                for member in &value.declarations {
                    if matches!(&member.kind, hir::AssociatedDeclarationKind::Subscript(_)) {
                        if let Some(class) = class {
                            let TyKind::Adt(class, _) = class.kind() else {
                                unreachable!()
                            };
                            self.subscripts.entry(class.id).or_default().push(member.id);
                        }
                    }
                    if let hir::AssociatedDeclarationKind::Function(function) = &member.kind {
                        let has_self = function
                            .signature
                            .prototype
                            .inputs
                            .first()
                            .is_some_and(|parameter| parameter.name.symbol.as_str() == "self");
                        if let Some(class) = class
                            && has_self
                        {
                            let TyKind::Adt(class, _) = class.kind() else {
                                unreachable!()
                            };
                            self.methods.entry(class.id).or_default().push(Method {
                                id: member.id,
                                is_final: function.is_final,
                                is_override: function.is_override,
                                returns_self: function.signature.prototype.output.as_ref().is_some_and(|output|
                                    matches!(&output.kind, hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path))
                                        if matches!(path.resolution, hir::Resolution::SelfTypeAlias(_)))),
                            });
                        } else if function.is_override || function.is_final {
                            self.gcx.dcx().emit_error(
                                "final/override requires a class instance method".into(),
                                Some(member.span),
                            );
                        }
                    }
                }
            }
            hir::walk_declaration(self, node);
        }
    }
    let mut collector = Collector {
        gcx,
        classes: vec![],
        methods: FxHashMap::default(),
        subscripts: FxHashMap::default(),
    };
    hir::walk_package(&mut collector, package);
    fn build<'ctx>(
        gcx: Gcx<'ctx>,
        id: hir::DefinitionID,
        methods: &FxHashMap<hir::DefinitionID, Vec<Method>>,
        declarations: &FxHashMap<hir::DefinitionID, Vec<hir::DefinitionID>>,
        active: &mut FxHashSet<hir::DefinitionID>,
        done: &mut FxHashSet<hir::DefinitionID>,
    ) {
        if !active.insert(id) || done.contains(&id) {
            return;
        }
        let class = gcx.get_type(id);
        let mut definition = gcx.get_struct_definition(id).clone();
        let mut info = definition.class_info.unwrap();
        let mut slots = vec![];
        if let Some(base) = info.base
            && let TyKind::Adt(base_def, _) = base.kind()
        {
            if base_def.id.package() == gcx.package_index() {
                build(gcx, base_def.id, methods, declarations, active, done);
            }
            slots.extend(gcx.class_methods(base));
        }
        // Only the original base catalog can be overridden. Methods introduced
        // earlier in this class are overloads, never inherited declarations.
        let inherited_slots = slots.clone();
        let subscripts = subscripts::prepare(
            gcx,
            class,
            declarations.get(&id).map(Vec::as_slice).unwrap_or_default(),
        );
        let mut overridden = FxHashSet::default();
        for method in methods.get(&id).into_iter().flatten() {
            if subscripts.suppressed.contains(&method.id) {
                continue;
            }
            let method = &Method {
                is_override: subscripts
                    .overrides
                    .get(&method.id)
                    .copied()
                    .unwrap_or(method.is_override),
                ..*method
            };
            let generic = gcx.generics_of(method.id);
            let identity = GenericsBuilder::identity_for_item(gcx, method.id);
            let own = gcx
                .store
                .interners
                .intern_generic_args_slice(&identity[generic.parent_count..]);
            // A shaped extension may only exist for some instantiations:
            // Base[Box[U]] cannot be deduced from the abstract Base[T]. Check
            // its declaration in its own target environment, and rebase the
            // inherited catalog into those same coordinates for matching.
            let context_class = if gcx.class_method_arguments(class, method.id, own).is_some() {
                class
            } else {
                gcx.get_impl_target_ty(gcx.definition_parent(method.id).unwrap())
                    .unwrap()
            };
            let inherited_slots: Vec<_> = if context_class == class {
                inherited_slots.clone()
            } else {
                let TyKind::Adt(_, args) = context_class.kind() else {
                    unreachable!()
                };
                inherited_slots
                    .iter()
                    .map(|slot| ClassMethod {
                        owner: instantiate_ty_with_args(gcx, slot.owner, args),
                        ..*slot
                    })
                    .collect()
            };
            let actual_args = gcx
                .class_method_arguments(context_class, method.id, own)
                .expect("class member's declared target");
            let actual = subscripts::method_type(gcx, method.id, actual_args);
            let TyKind::FnPointer {
                effects: _,
                inputs: actual_inputs,
                output: actual_output,
            } = actual.kind()
            else {
                unreachable!()
            };
            let name = gcx.definition_ident(method.id).symbol;
            let actual_signature = gcx.get_signature(method.id);
            let mode = |ty: Ty<'ctx>| matches!(ty.kind(), TyKind::Reference(_));
            let interface = gcx.class_method_interface(context_class, method.id);
            let shape_candidates: Vec<_> = inherited_slots
                .iter()
                .enumerate()
                .filter_map(|(index, slot)| {
                    let inherited_interface =
                        gcx.class_method_interface(context_class, slot.family);
                    let same_family = match (interface, inherited_interface) {
                        (None, None) => true,
                        (Some(actual), Some(base)) => {
                            actual.id == base.id
                                && actual.arguments.get(1..) == base.arguments.get(1..)
                        }
                        _ => false,
                    };
                    if !same_family
                        || gcx.definition_ident(slot.family).symbol != name
                        || !gcx.is_definition_visible(slot.implementation, method.id)
                    {
                        return None;
                    }
                    let inherited_generics = gcx.generics_of(slot.implementation);
                    if inherited_generics.parameters.len() != generic.parameters.len()
                        || inherited_generics
                            .parameters
                            .iter()
                            .zip(&generic.parameters)
                            .any(|(base, actual)| {
                                std::mem::discriminant(&base.kind)
                                    != std::mem::discriminant(&actual.kind)
                            })
                    {
                        return None;
                    }
                    let args = gcx.class_method_arguments(slot.owner, slot.implementation, own)?;
                    let candidate = subscripts::method_type(gcx, slot.implementation, args);
                    let TyKind::FnPointer { inputs, output, .. } = candidate.kind() else {
                        return None;
                    };
                    if inputs.len() != actual_inputs.len() || inputs[1..] != actual_inputs[1..] {
                        return None;
                    }
                    let base_signature = gcx.get_signature(slot.implementation);
                    let exact_contract = mode(inputs[0]) == mode(actual_inputs[0])
                        && base_signature
                            .inputs
                            .iter()
                            .skip(1)
                            .map(|parameter| parameter.label)
                            .eq(actual_signature
                                .inputs
                                .iter()
                                .skip(1)
                                .map(|parameter| parameter.label))
                        && base_signature.abi == actual_signature.abi
                        && base_signature.is_variadic == actual_signature.is_variadic
                        && gcx.definition_is_async(slot.implementation)
                            == gcx.definition_is_async(method.id)
                        && gcx.definition_is_unsafe(slot.implementation)
                            == gcx.definition_is_unsafe(method.id);
                    // Exact results win. With single inheritance, the nearest
                    // covariant class result is the unique most specific match.
                    let result_rank = if output == actual_output {
                        Some(0)
                    } else if gcx.is_class_type(output) {
                        gcx.class_ancestry(actual_output)
                            .iter()
                            .position(|ancestor| *ancestor == output)
                    } else {
                        None
                    };
                    Some((index, exact_contract, result_rank))
                })
                .collect();
            let best_rank = shape_candidates
                .iter()
                .filter_map(|(_, exact, rank)| exact.then_some(*rank).flatten())
                .min();
            let best: Vec<_> = shape_candidates
                .iter()
                .filter(|(_, exact, rank)| *exact && rank.is_some() && *rank == best_rank)
                .map(|(index, _, _)| *index)
                .collect();
            if best.len() > 1 {
                gcx.dcx().emit_error(
                    "override is ambiguous between inherited method families".into(),
                    Some(gcx.definition_ident(method.id).span),
                );
                continue;
            }
            let inherited = best.first().copied().or_else(|| {
                method
                    .is_override
                    .then(|| {
                        shape_candidates
                            .iter()
                            .find(|(_, exact, _)| *exact)
                            .or_else(|| shape_candidates.first())
                            .map(|(index, _, _)| *index)
                    })
                    .flatten()
            });
            let error = |message: &str| {
                gcx.dcx()
                    .emit_error(message.into(), Some(gcx.definition_ident(method.id).span))
            };
            if let Some(index) = inherited {
                let base = inherited_slots[index];
                if gcx
                    .native_subscript_for_accessor(base.implementation)
                    .is_some()
                    != gcx.native_subscript_for_accessor(method.id).is_some()
                {
                    error(
                        "native subscript accessors must be overridden by a subscript declaration",
                    );
                }
                if !overridden.insert(base.family) {
                    error("a class cannot override the same inherited family twice");
                }
                if !method.is_override {
                    error("overriding an inherited method requires override");
                }
                if base.is_final
                    && !(gcx
                        .native_subscript_for_accessor(base.implementation)
                        .is_some()
                        && gcx.native_subscript_for_accessor(method.id).is_some())
                {
                    error("cannot override a final method");
                }
                let args = gcx
                    .class_method_arguments(base.owner, base.implementation, own)
                    .unwrap();
                let expected = subscripts::method_type(gcx, base.implementation, args);
                let TyKind::FnPointer { inputs, output, .. } = expected.kind() else {
                    unreachable!()
                };
                let mode = |ty: Ty<'ctx>| matches!(ty.kind(), TyKind::Reference(_));
                if mode(inputs[0]) != mode(actual_inputs[0]) {
                    error("override must preserve the base receiver mode exactly");
                }
                let constraints = |method, arguments| {
                    gcx.constraints_of(method).into_iter().map(|constraint|
                    crate::sema::tycheck::utils::normalize_aliases(gcx,
                        crate::sema::tycheck::utils::instantiate::instantiate_constraint_with_args(gcx,constraint.value,arguments))
                ).collect::<FxHashSet<_>>()
                };
                if constraints(method.id, actual_args) != constraints(base.implementation, args) {
                    error(
                        "override generic constraints must match the base after parameter renaming",
                    );
                }
                for (base_parameter, actual_parameter) in gcx
                    .generics_of(base.implementation)
                    .parameters
                    .iter()
                    .zip(&generic.parameters)
                {
                    if let (Some(base_ty), Some(actual_ty)) = (
                        gcx.try_generic_const_param_ty(base_parameter.id),
                        gcx.try_generic_const_param_ty(actual_parameter.id),
                    ) && instantiate_ty_with_args(gcx, base_ty, args)
                        != instantiate_ty_with_args(gcx, actual_ty, actual_args)
                    {
                        error("override must preserve generic const parameter types");
                    }
                }
                let base_signature = gcx.get_signature(base.implementation);
                let actual_signature = gcx.get_signature(method.id);
                if base_signature.abi != actual_signature.abi
                    || base_signature.is_variadic != actual_signature.is_variadic
                    || gcx.definition_is_unsafe(base.implementation)
                        != gcx.definition_is_unsafe(method.id)
                {
                    error("override must preserve the base calling convention and safety contract");
                }
                if matches!(
                    gcx.definition_visibility(base.implementation),
                    crate::sema::resolve::models::Visibility::Public
                ) && !matches!(
                    gcx.definition_visibility(method.id),
                    crate::sema::resolve::models::Visibility::Public
                ) {
                    error("an override of a public method must remain public");
                }
                if base_signature
                    .inputs
                    .iter()
                    .skip(1)
                    .map(|p| p.label)
                    .ne(actual_signature.inputs.iter().skip(1).map(|p| p.label))
                {
                    error("override must preserve parameter labels");
                }
                if output != actual_output && !gcx.is_class_subtype(actual_output, output) {
                    error("override result must match or be a more specific owned class handle");
                }
                if gcx.definition_is_async(base.implementation)
                    != gcx.definition_is_async(method.id)
                {
                    error("override must preserve async behavior");
                }
                slots[index] = ClassMethod {
                    returns_self: base.returns_self || method.returns_self,
                    family: base.family,
                    implementation: method.id,
                    owner: class,
                    is_final: method.is_final || info.is_final,
                };
            } else {
                if method.is_override {
                    error(
                        "override has no inherited method with matching parameter types and generic arity",
                    );
                }
                slots.push(ClassMethod {
                    returns_self: method.returns_self,
                    family: method.id,
                    implementation: method.id,
                    owner: class,
                    is_final: method.is_final || info.is_final,
                });
            }
        }
        for (_, entry) in &subscripts.entries {
            if entry.is_final {
                for slot in &mut slots {
                    if [entry.getter, entry.setter, entry.address]
                        .contains(&Some(slot.implementation))
                    {
                        slot.is_final = true;
                    }
                }
            }
        }
        subscripts::retain_inherited_defaults(gcx, class, &subscripts, &inherited_slots);
        gcx.with_session_type_database(|db| {
            db.class_subscripts.insert(id, subscripts.entries);
        });
        info.methods = gcx.store.arenas.global.alloc_slice_copy(&slots);
        definition.class_info = Some(info);
        gcx.cache_struct_definition(id, definition);
        active.remove(&id);
        done.insert(id);
    }
    let mut active = FxHashSet::default();
    let mut done = FxHashSet::default();
    for id in collector.classes {
        build(
            gcx,
            id,
            &collector.methods,
            &collector.subscripts,
            &mut active,
            &mut done,
        );
    }
    gcx.dcx().ok()
}

#[cfg(test)]
mod hierarchy_tests {
    use super::*;
    #[test]
    fn inherited_header_defaults_adapt_only_the_receiver_reference() {
        let errors = crate::test_support::analyze_script_diagnostics(
            "interface Readable { func read() -> int32 { 7 }; func twice() -> int32 { self.read() + self.read() }; }\nclass Base: Readable {}\nclass Derived: Base {}\nconform Derived to Readable { override func read() -> int32 { 17 }; }\nfunc use(_ value: &Derived) -> int32 { value.twice() }\nfunc main() {}",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn overloaded_methods_keep_distinct_families_and_select_exact_override_contracts() {
        crate::test_support::analyze_script(
            r#"
class Base {}
class Derived: Base {}
extend Base {
    func read() -> int32 { 1 }
    func read(_ value: int32) -> int32 { value }
    func number(_ value: int32) -> int32 { value }
    func number(_ value: int64) -> int64 { value }
    func choose(left value: int32) -> int32 { value }
    func choose(right value: int32) -> int32 { value }
}
extend Derived {
    override func read() -> int32 { 3 }
    override func number(_ value: int64) -> int64 { value }
    override func choose(right value: int32) -> int32 { value }
}
func main() {}
"#,
            |package, gcx| {
                let base = gcx
                    .class_info(gcx.get_type(package.root.declarations[0].id))
                    .unwrap();
                let derived = gcx
                    .class_info(gcx.get_type(package.root.declarations[1].id))
                    .unwrap();
                assert_eq!(base.methods.len(), 6);
                assert_eq!(derived.methods.len(), 6);
                for (index, (base, derived)) in base.methods.iter().zip(derived.methods).enumerate()
                {
                    assert_eq!(base.family, derived.family);
                    assert_eq!(
                        base.implementation != derived.implementation,
                        [0, 3, 5].contains(&index)
                    );
                }
            },
        );
    }
    #[test]
    fn conditional_methods_include_extension_bounds_without_narrowing_overrides() {
        crate::test_support::analyze_script(
            r#"
interface Available {}
conform int32 to Available {}
class Box[T] {}
extend[T: Available] Box[T] {
    func read() -> int32 { 1 }
}
func main() {}
"#,
            |package, gcx| {
                let definition = package
                    .root
                    .declarations
                    .iter()
                    .find(|declaration| declaration.identifier.symbol.as_str() == "Box")
                    .unwrap();
                let TyKind::Adt(class, _) = gcx.get_type(definition.id).kind() else {
                    unreachable!()
                };
                for (ty, expected) in [(gcx.types.int32, true), (gcx.types.int64, false)] {
                    let arguments = gcx
                        .store
                        .interners
                        .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(ty)]);
                    let class = Ty::new(TyKind::Adt(class, arguments), gcx);
                    let method = gcx.class_info(class).unwrap().methods[0].implementation;
                    let arguments = gcx
                        .class_method_arguments(
                            class,
                            method,
                            crate::sema::models::GenericArguments::empty(),
                        )
                        .unwrap();
                    assert_eq!(
                        crate::sema::lowering::classes::method_available(gcx, method, arguments),
                        expected
                    );
                }
            },
        );
        for (base_condition, valid) in [("", false), (": Available", true)] {
            let source = format!(
                "interface Available {{}}\nclass Base[T] {{}}\nclass Derived[T]: Base[T] {{}}\nextend[T{base_condition}] Base[T] {{ func read() -> int32 {{ 1 }}; }}\nextend[T: Available] Derived[T] {{ override func read() -> int32 {{ 2 }}; }}\nfunc main() {{}}"
            );
            let diagnostics = crate::test_support::analyze_script_diagnostics(&source);
            if valid {
                assert!(diagnostics.is_empty(), "{diagnostics:#?}");
            } else {
                assert!(
                    diagnostics
                        .iter()
                        .any(|diagnostic| diagnostic.message.contains("stronger conditions")),
                    "{diagnostics:#?}"
                );
            }
        }
    }
    #[test]
    fn super_selects_a_base_receiver_and_generic_bounds_cannot_strengthen() {
        let source = r#"
class Base {}
class Derived: Base {}
extend Base {
    func read() -> int32 { 11 }
    func echo[T](_ value: T) -> T { value }
}
extend Derived {
    override func read() -> int32 { return super.read() + 11; }
    override func echo[U](_ value: U) -> U { return super.echo(value); }
}
func main() {}
"#;
        let diagnostics = crate::test_support::analyze_script_diagnostics(source);
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
        for source in [
            "class Root {}\nextend Root { func read() -> int32 { super.read() }\n}\nfunc main() {}",
            "class Base {}\nclass Derived: Base {}\nextend Derived { func wrong() -> Base { super }\n}\nfunc main() {}",
            "interface Marker {}\nclass Base {}\nclass Derived: Base {}\nextend Base { func echo[T](_ value: T) -> T { value }\n}\nextend Derived { override func echo[U: Marker](_ value: U) -> U { value }\n}\nfunc main() {}",
        ] {
            assert!(
                !crate::test_support::analyze_script_diagnostics(source).is_empty(),
                "must reject {source}"
            );
        }
    }
    #[test]
    fn inherited_layout_and_generic_overrides_keep_families_and_substitutions() {
        crate::test_support::analyze_script(
            r#"
class Base[T] { first: T; marker: uint8 }
class Derived[T]: Base[T] { extra: int64 }
extend[T] Base[T] {
    func read() -> &T { &self.first }
    func echo[U](_ value: U) -> U { value }
    func object() -> Base[T] { self }
}
extend[T] Derived[T] {
    override func read() -> &T { &self.first }
    override func echo[V](_ value: V) -> V { value }
    override func object() -> Derived[T] { self }
}
func main() {}
"#,
            |package, gcx| {
                let base = gcx.get_type(package.root.declarations[0].id);
                let derived = gcx.get_type(package.root.declarations[1].id);
                assert!(gcx.is_class_subtype(derived, base));
                let base_methods = gcx.class_info(base).unwrap().methods;
                let derived_methods = gcx.class_info(derived).unwrap().methods;
                assert_eq!(base_methods.len(), 3);
                assert_eq!(derived_methods.len(), 3);
                for (base, derived) in base_methods.iter().zip(derived_methods) {
                    assert_eq!(base.family, derived.family);
                    assert_ne!(base.implementation, derived.implementation);
                }
                let definition = gcx.get_struct_definition(package.root.declarations[1].id);
                assert_eq!(definition.fields.len(), 3);
                assert_eq!(gcx.class_field_payload_path(derived, 0), Some(vec![0, 0]));
                assert_eq!(gcx.class_field_payload_path(derived, 2), Some(vec![1]));
                let payload = gcx.ensure_class_payload(derived).unwrap();
                let TyKind::Adt(payload, _) = payload.kind() else {
                    unreachable!()
                };
                assert_eq!(
                    gcx.get_struct_definition(payload.id).repr,
                    crate::sema::models::StructRepr::C
                );
            },
        );
    }

    #[test]
    fn inherited_calls_and_shared_slot_upcasts_do_not_admit_mutable_slot_conversion() {
        crate::test_support::analyze_script(
            r#"
class Base { count: int32 }
class Derived: Base { extra: int32 }
extend Base {
    func read() -> int32 { self.count }
    func change() { self.count += 1 }
}
func inspect(_ value: &Base) -> int32 { value.read() }
func use(_ value: &Derived) -> int32 {
    value.change()
    var handle: Base = *value
    inspect(&handle)
}
func main() {}
"#,
            |_, _| {},
        );
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            r#"
class Base {}
class Derived: Base {}
func replace(_ value: &Base, _ other: Base) { *value = other }
func invalid(_ value: &Derived, _ other: Base) { replace(value, other) }
func main() {}
"#,
        );
        assert!(
            !diagnostics.is_empty(),
            "mutable handle slots must be invariant"
        );
    }

    #[test]
    fn inheritance_rejects_cycles_final_and_invalid_override_shapes() {
        for (source, expected) in [
            ("class A: B {}\nclass B: A {}", "inheritance cycle"),
            (
                "class A {}\nclass B: A {}\nextend A { public func f() {}; }\nextend B { private override func f() {}; }",
                "remain public",
            ),
            (
                "class A {}\nclass B: A {}\nextend A { func f() {}; }\nextend B { override unsafe func f() {}; }",
                "safety contract",
            ),
            ("final class A {}\nclass B: A {}", "final class"),
            (
                "class A {}\nclass B: A {}\nextend A { func f() {}; }\nextend B { func f() {}; }",
                "requires override",
            ),
            (
                "class A {}\nclass B: A {}\nextend A { final func f() {}; }\nextend B { override func f() {}; }",
                "final method",
            ),
            (
                "class A {}\nclass B: A {}\nextend A { func f(_ x: A) {}; }\nextend B { override func f(_ x: B) {}; }",
                "matching parameter types",
            ),
        ] {
            let diagnostics = crate::test_support::analyze_script_diagnostics(&format!(
                "{source}\nfunc main() {{}}"
            ));
            assert!(
                diagnostics.iter().any(|d| d.message.contains(expected)),
                "expected {expected}: {diagnostics:#?}"
            );
        }
    }
}
