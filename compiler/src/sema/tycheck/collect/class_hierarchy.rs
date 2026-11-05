//! Resolve nominal base links before payload layout. Logical fields are a
//! base-first flattened view; physical payloads keep a nested base prefix.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::{
        models::{StructField, TyKind},
        tycheck::{
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::instantiate::instantiate_ty_with_args,
        },
    },
};
use rustc_hash::{FxHashMap, FxHashSet};

pub fn run(package: &hir::Package, gcx: Gcx<'_>) -> CompileResult<()> {
    struct Collector {
        classes: Vec<(hir::DefinitionID, hir::Struct)>,
    }
    impl HirVisitor for Collector {
        fn visit_declaration(&mut self, node: &hir::Declaration) {
            if let hir::DeclarationKind::Struct(value) = &node.kind
                && value.class_header.is_some()
            {
                self.classes.push((node.id, value.clone()));
            }
            hir::walk_declaration(self, node);
        }
    }
    let mut collector = Collector { classes: vec![] };
    hir::walk_package(&mut collector, package);
    for (id, class) in &collector.classes {
        let Some(bounds) = &class.conformances else {
            continue;
        };
        let mut selected_base = None;
        for bound in &bounds.bounds {
            if is_interface_bound(gcx, &bound.path) {
                continue;
            }
            let node = hir::Type {
                id: bound.id,
                span: bound.span,
                kind: hir::TypeKind::Nominal(bound.path.clone()),
            };
            let ty = crate::sema::tycheck::utils::normalize_aliases(
                gcx,
                DefTyLoweringCtx::new(*id, gcx).lowerer().lower_type(&node),
            );
            let Some(base) = gcx.class_info(ty) else {
                gcx.dcx().emit_error(
                    "class inheritance requires a class base".into(),
                    Some(bound.span),
                );
                continue;
            };
            if selected_base.is_some() {
                gcx.dcx().emit_error(
                    "a class may inherit from only one base class".into(),
                    Some(bound.span),
                );
                continue;
            }
            if base.is_final {
                gcx.dcx()
                    .emit_error("cannot inherit from a final class".into(), Some(bound.span));
            }
            selected_base = Some(ty);
        }
        let mut definition = gcx.get_struct_definition(*id).clone();
        definition.class_info.as_mut().unwrap().base = selected_base;
        gcx.cache_struct_definition(*id, definition);
    }
    gcx.dcx().ok()?;
    let own: FxHashMap<_, _> = collector
        .classes
        .iter()
        .map(|(id, _)| (*id, gcx.get_struct_definition(*id).fields.to_vec()))
        .collect();
    fn flatten<'ctx>(
        gcx: Gcx<'ctx>,
        id: hir::DefinitionID,
        own: &FxHashMap<hir::DefinitionID, Vec<StructField<'ctx>>>,
        active: &mut FxHashSet<hir::DefinitionID>,
        done: &mut FxHashSet<hir::DefinitionID>,
    ) {
        if done.contains(&id) || !own.contains_key(&id) {
            return;
        }
        if !active.insert(id) {
            gcx.dcx().emit_error(
                "class inheritance cycle".into(),
                Some(gcx.definition_ident(id).span),
            );
            return;
        }
        let mut definition = gcx.get_struct_definition(id).clone();
        let mut fields = vec![];
        if let Some(base) = definition.class_info.unwrap().base
            && let TyKind::Adt(base_def, args) = base.kind()
        {
            flatten(gcx, base_def.id, own, active, done);
            if !gcx.dcx().has_error() {
                fields.extend(
                    gcx.get_struct_definition(base_def.id)
                        .fields
                        .iter()
                        .map(|field| StructField {
                            ty: instantiate_ty_with_args(gcx, field.ty, args),
                            ..*field
                        }),
                );
            }
        }
        for field in &own[&id] {
            if fields
                .iter()
                .any(|base: &StructField<'_>| base.name == field.name)
            {
                gcx.dcx().emit_error(
                    "stored field cannot redeclare an inherited field".into(),
                    Some(gcx.definition_ident(field.def_id).span),
                );
            }
            fields.push(*field);
        }
        definition.fields = gcx.store.arenas.global.alloc_slice_copy(&fields);
        gcx.cache_struct_definition(id, definition);
        active.remove(&id);
        done.insert(id);
    }
    let mut active = FxHashSet::default();
    let mut done = FxHashSet::default();
    for (id, _) in collector.classes {
        flatten(gcx, id, &own, &mut active, &mut done);
    }
    gcx.dcx().ok()
}

/// Keep interface paths out of nominal payload/base lowering. Interface aliases
/// are classified here too so conformance collection can issue its normal
/// explicit-target diagnostic rather than treating an alias as a class base.
pub(super) fn is_interface_bound(gcx: Gcx<'_>, path: &hir::ResolvedPath) -> bool {
    let resolution = match path {
        hir::ResolvedPath::Resolved(path) => &path.resolution,
        hir::ResolvedPath::Relative(_, segment) => &segment.resolution,
    };
    resolution.definition_id().is_some_and(|id| {
        matches!(
            gcx.try_definition_kind(id),
            Some(hir::DefinitionKind::Interface)
        ) || gcx.is_interface_alias(id)
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn final_headers_separate_a_base_from_multiple_default_interfaces() {
        crate::test_support::analyze_script(
            r#"
interface Readable { func current() -> int32 { 7 }; func twice() -> int32 { self.current() + self.current() }; }
interface Flagged { func flag() -> bool { true }; }
class Base { value: int32 }
final class Counter: Base, Readable, Flagged {}
extend Counter {
    func local() -> int32 { self.value }
}
func read[T: Readable](_ value: &T) -> int32 { value.twice() }
func check(_ value: &Counter) -> int32 { read(value) }
func main() {}
"#,
            |_, _| {},
        );
    }
    #[test]
    fn final_headers_still_reject_multiple_bases_and_missing_witnesses() {
        for (source, expected) in [
            (
                "class A {}\nclass B {}\nfinal class C: A, B {}",
                "only one base class",
            ),
            (
                "interface P { func read() -> int32; }\nfinal class C: P {}",
                "does not satisfy requirements",
            ),
        ] {
            let errors = crate::test_support::analyze_script_diagnostics(&format!(
                "{source}\nfunc main() {{}}"
            ));
            assert!(
                errors.iter().any(|error| error.message.contains(expected)),
                "{expected}: {errors:#?}"
            );
        }
    }
}
