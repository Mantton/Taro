//! Register source initializers before conformance synthesis and body checking.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::models::{AdtKind, TyKind},
};

pub fn register(package: &hir::Package, gcx: Gcx<'_>) -> CompileResult<()> {
    hir::walk_package(&mut Collector { gcx }, package);
    gcx.dcx().ok()
}

struct Collector<'ctx> {
    gcx: Gcx<'ctx>,
}

impl HirVisitor for Collector<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) {
        if let hir::DeclarationKind::Impl(extension) = &declaration.kind {
            for member in &extension.declarations {
                if matches!(member.kind, hir::AssociatedDeclarationKind::Initializer(_)) {
                    let target = self.gcx.get_impl_target_ty(declaration.id);
                    if let Some(target) = target
                        && let TyKind::Adt(def, _) = target.kind()
                        && def.kind == AdtKind::Struct
                        && def.id.package() == declaration.id.package()
                        && extension.interface.is_none()
                    {
                        let output = self.gcx.get_signature(member.id).output;
                        if crate::sema::tycheck::utils::normalize_aliases(
                            self.gcx,
                            self.gcx.constructor_value(output),
                        ) != crate::sema::tycheck::utils::normalize_aliases(self.gcx, target)
                        {
                            self.gcx.dcx().emit_error(
                                "initializer result must be Self or Result[Self, Error]".into(),
                                Some(member.span),
                            );
                            continue;
                        }
                        let mut definition = self.gcx.get_struct_definition(def.id).clone();
                        definition.has_initializer = true;
                        self.gcx.cache_struct_definition(def.id, definition);
                        if self.gcx.is_class_type(target) {
                            let mut definition = self.gcx.get_struct_definition(def.id).clone();
                            let info = definition.class_info.as_mut().unwrap();
                            let hir::AssociatedDeclarationKind::Initializer(function) =
                                &member.kind
                            else {
                                unreachable!()
                            };
                            let kind = function
                                .initializer_kind
                                .expect("initializer category retained by HIR");
                            let mut initializers = info.initializers.to_vec();
                            initializers.push(crate::sema::models::ClassInitializer {
                                definition: member.id,
                                family: member.id,
                                implementation: member.id,
                                owner: self.gcx.get_type(def.id),
                                is_convenience: kind.is_convenience,
                                is_required: kind.is_required,
                                is_inherited: false,
                                delegations: &[],
                            });
                            info.initializers =
                                self.gcx.store.arenas.global.alloc_slice_copy(&initializers);
                            self.gcx.cache_struct_definition(def.id, definition);
                            self.gcx.class_payload_initializer(member.id);
                        }
                    } else {
                        self.gcx.dcx().emit_error(
                            "init requires a struct extension in the owning package".into(),
                            Some(member.span),
                        );
                    }
                }
            }
        }
        hir::walk_declaration(self, declaration);
    }
}

#[cfg(test)]
mod tests {
    use crate::hir;
    use crate::test_support::analyze_script;

    const CLASS_PAYLOAD_TEST_RUNTIME: &str = "struct Handle { owner: *const uint8 }\nnamespace runtime { func __classAllocatePayload[T](_ value: T) -> script::Handle { script::Handle { owner: unsafe { 0 as *const uint8 } } }; }\nnamespace intrinsic { func __intrinsic_class_from_handle[T](_ handle: script::Handle) -> T { loop {} }; }\n";

    #[test]
    fn initializer_rejects_an_unrelated_explicit_result() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            "struct Record { value: int32 }\nextend Record { init() -> int32 { 7 } }\nfunc main() {}",
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("initializer result must be Self or Result[Self, Error]")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn class_initializer_categories_survive_hir_and_declaration_collection() {
        analyze_script(
            "class Record[T] { value: T }\nextend[T] Record[T] { init(_ value: T) { self.value = value }; func read() -> &T { &self.value }; }\nfunc main() {}",
            |package, gcx| {
                let class = package.root.declarations[0].id;
                let hir::DeclarationKind::Impl(extension) = &package.root.declarations[1].kind
                else {
                    unreachable!()
                };
                let hir::AssociatedDeclarationKind::Initializer(initializer) =
                    &extension.declarations[0].kind
                else {
                    unreachable!()
                };
                assert_eq!(
                    initializer.initializer_kind,
                    Some(hir::InitializerKind::default())
                );
                let hir::AssociatedDeclarationKind::Function(method) =
                    &extension.declarations[1].kind
                else {
                    unreachable!()
                };
                assert!(method.initializer_kind.is_none());
                let entries = gcx.class_info(gcx.get_type(class)).unwrap().initializers;
                assert_eq!(entries.len(), 1);
                assert_eq!(entries[0].definition, extension.declarations[0].id);
                assert_eq!(entries[0].family, entries[0].definition);
                assert_eq!(entries[0].owner, gcx.get_type(class));
                assert!(
                    !entries[0].is_required
                        && !entries[0].is_convenience
                        && !entries[0].is_inherited
                );
            },
        );
    }

    #[test]
    fn derived_initialization_uses_a_private_base_prefix() {
        crate::test_support::analyze_script(
            "class Base { readonly first: int32 }\nextend Base { init(_ first: int32) { self.first = first } }\nclass Child: Base { second: int32 = 2 }\nextend Child { override init(_ first: int32) { super.init(first); self.second += self.first } }\nfunc main() {}",
            |_, _| {},
        );
    }

    #[test]
    fn derived_payload_mir_keeps_the_completed_base_as_one_owned_field() {
        let source = format!(
            "{}class Base {{ readonly first: int32 }}\nextend Base {{ init(_ first: int32) {{ self.first = first }} }}\nclass Child: Base {{ second: int32 = 2 }}\nextend Child {{ override init(_ first: int32) {{ super.init(first); observed := self.first; observe := () => observed; self.second += observe() }} }}\nfunc main() {{}}",
            CLASS_PAYLOAD_TEST_RUNTIME
        );
        crate::test_support::analyze_script_built_mir_with_items(
            &source,
            &[(hir::StdItem::ClassHandle, "Handle")],
            |bodies, gcx| {
                for body in &bodies {
                    assert!(crate::mir::analysis::constructor::validate(gcx, body).is_ok());
                }
                assert!(bodies.iter().any(|body| {
                    gcx.class_for_payload(body.locals[body.return_local].ty)
                        .is_some_and(|class| gcx.class_base(class).is_some())
                }));
            },
        );
    }

    #[test]
    fn derived_payload_rejects_prebase_access_and_reinitialization() {
        for (body, expected) in [
            (
                "self.own = 1; super.init(2)",
                "before accessing self fields",
            ),
            (
                "old := self.value; super.init(old); self.own = 3",
                "before accessing self fields",
            ),
            (
                "super.init(1); super.init(2); self.own = 3",
                "initialize the base only once",
            ),
            (
                "super.init(1); inspect(&self); self.own = 3",
                "cannot copy, capture, pass",
            ),
        ] {
            let source = format!(
                "{CLASS_PAYLOAD_TEST_RUNTIME}class Base {{ value: int32 }}\nextend Base {{ init(_ value: int32) {{ self.value = value }} }}\nclass Child: Base {{ own: int32 }}\nfunc inspect[T](_ value: &T) {{}}\nextend Child {{ init() {{ {body} }} }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir_with_items(
                &source,
                &[(hir::StdItem::ClassHandle, "Handle")],
                |bodies, gcx| {
                    for body in &bodies {
                        let _ = crate::mir::analysis::class_lifecycle::validate(gcx, body);
                        let _ = crate::mir::analysis::constructor::validate(gcx, body);
                    }
                    let diagnostics = gcx.dcx().take_recorded_diagnostics();
                    assert!(
                        diagnostics
                            .iter()
                            .any(|diagnostic| diagnostic.message.contains(expected)),
                        "{body}\n{diagnostics:#?}"
                    );
                },
            );
        }
    }

    #[test]
    fn value_initializers_use_result_storage_and_keep_self_for_defer() {
        for source in [
            "struct Counter { readonly value: int32 }\nextend Counter { init(_ value: int32) { self.value = value; defer { seen := self.value } } }\nfunc main() { counter := Counter(7); seen := counter.value }",
            "struct Pair[T] { first: T; second: int32 }\nextend[T] Pair[T] { init(_ first: T) { self.first = first; self.second = 2; return } }\nfunc main() { pair := Pair[int32](1) }",
            "struct Empty {}\nextend Empty { init() {} }\nfunc main() { empty := Empty() }",
            "struct View { item: &int32 }\nextend View { init(_ item: &int32) { self.item = item } }\nfunc main() { var value: int32 = 1; view := View(&value); seen := *view.item; value = 2 }",
        ] {
            crate::test_support::check_script(source, |_, _| {});
        }
    }

    #[test]
    fn value_initializers_reject_missing_fields_readonly_rewrites_and_literal_bypass() {
        for (body, main, expected) in [
            ("", "counter := Counter()", "uninitialized"),
            (
                "self.value = 1; self.value = 2",
                "counter := Counter()",
                "readonly field can only be initialized once",
            ),
            (
                "self.value = 1",
                "counter := Counter { value: 2 }",
                "must be constructed by calling",
            ),
            (
                "seen := self.value; self.value = 1",
                "counter := Counter()",
                "uninitialized",
            ),
        ] {
            let source = format!(
                "struct Counter {{ readonly value: int32 }}\nextend Counter {{ init() {{ {body} }} }}\nfunc main() {{ {main} }}"
            );
            let diagnostics = crate::test_support::analyze_script_mir_diagnostics(&source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(expected)),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
    #[test]
    fn stored_defaults_initialize_constructors_and_fill_literal_holes() {
        for source in [
            "struct Counter { readonly value: int32 = 7 }\nextend Counter { init() {} }\nfunc main() { counter := Counter() }",
            "struct Counter { value: int32 = 7 }\nextend Counter { init() { self.value = 8 } }\nfunc main() { counter := Counter() }",
            "struct Pair[T] { first: int32 = 7; second: T }\nextend[T] Pair[T] { init(_ second: T) { self.second = second } }\nfunc main() { pair := Pair[int32](8) }",
            "struct Record { value: int32 = 7; required: int32 }\nfunc main() { record := Record { required: 8 } }",
            "struct Record { value: int32 = 7 }\nfunc main() { record := Record { value: 8 } }",
            "func size[T]() -> usize { 7 }\nstruct Record[T] { size: usize = size[T]() }\nextend[T] Record[T] { init() {} }\nfunc main() { record := Record[int32]() }",
            "struct Record { compute: (int32) -> int32 = (value: int32) => value + 1 }\nextend Record { init() {} }\nfunc main() { record := Record() }",
        ] {
            crate::test_support::check_script(source, |_, _| {});
        }
    }

    #[test]
    fn stored_defaults_cannot_reinitialize_readonly_fields_or_read_self() {
        for (source, expected) in [
            (
                "struct Counter { readonly value: int32 = 7 }\nextend Counter { init() { self.value = 8 } }\nfunc main() {}",
                "readonly field can only be initialized once",
            ),
            (
                "struct Counter { value: int32 = false }\nfunc main() {}",
                "int32",
            ),
            (
                "struct Counter { first: int32; second: int32 = self.first }\nfunc main() {}",
                "self",
            ),
        ] {
            let diagnostics = crate::test_support::analyze_script_mir_diagnostics(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(expected)),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
    #[test]
    fn constructor_write_privilege_does_not_allow_setting_computed_properties() {
        let diagnostics = crate::test_support::analyze_script_mir_diagnostics(
            "struct Counter { value: int32 }\nextend Counter { var doubled: int32 { get { self.value * 2 } }; init() { self.value = 1; self.doubled = 4 } }\nfunc main() {}",
        );
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("read-only property")),
            "{diagnostics:#?}"
        );
    }
}
