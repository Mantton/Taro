use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor, walk_declaration},
    sema::models::{AdtKind, GenericArgument, Ty, TyKind},
    sema::tycheck::solve::ConstraintSystem,
    span::Span,
};
use rustc_hash::FxHashSet;

mod implied;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}
struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        match &node.kind {
            hir::DeclarationKind::Interface(..) => {
                self.check_constraints(node.id);
                if self.context.std_item_def(hir::StdItem::Deref) == Some(node.id) {
                    self.check_deref_contract(node.id);
                }
            }
            hir::DeclarationKind::Struct(_) => {
                self.check_struct(node.id);
            }
            hir::DeclarationKind::Enum(_) => {
                self.check_enum(node.id);
            }
            hir::DeclarationKind::Function(function) => {
                self.check_function(node.id, function);
            }
            hir::DeclarationKind::TypeAlias(..) => self.check_constraints(node.id),
            hir::DeclarationKind::Constant(..) => {}
            hir::DeclarationKind::StaticVariable(..) => self.check_static(node.id),
            hir::DeclarationKind::Import(..) => {}
            hir::DeclarationKind::Export(..) => {}
            hir::DeclarationKind::Namespace(..) => {}
            hir::DeclarationKind::Impl(..) => {
                self.check_impl(node.id);
            }
            hir::DeclarationKind::OpaqueType => {
                // Opaque types have no body to validate
            }
            hir::DeclarationKind::Malformed => unreachable!(),
        }

        walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        match &node.kind {
            hir::AssociatedDeclarationKind::Function(..)
            | hir::AssociatedDeclarationKind::Initializer(..)
            | hir::AssociatedDeclarationKind::Type(..) => {
                self.check_constraints(node.id);
            }
            _ => {}
        }

        hir::walk_assoc_declaration(self, node, context)
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_deref_contract(&self, id: DefinitionID) {
        let gcx = self.context;
        let Some(requirements) = gcx.get_interface_requirements(id) else {
            return;
        };
        let target = requirements
            .types
            .iter()
            .find(|target| target.name.as_str() == "Target");
        let method = requirements
            .methods
            .iter()
            .find(|method| method.name.as_str() == "deref");
        let valid = target.zip(method).is_some_and(|(target, method)| {
            let output = crate::sema::tycheck::utils::normalize_aliases(gcx, method.signature.output);
            method.has_self && method.signature.inputs.len() == 1
                && gcx.generics_of(method.id).parameters.is_empty()
                && !method.signature.is_variadic && !gcx.definition_is_async(method.id)
                && !gcx.definition_is_unsafe(method.id)
                && matches!(output.kind(), TyKind::Reference(inner) if matches!(inner.kind(), TyKind::Alias { kind: crate::sema::models::AliasKind::Projection, def_id, args } if def_id == target.id && args.len() == 1 && args[0].ty() == Some(gcx.types.self_type_parameter)))
        }) && gcx.generics_of(id).total_count() == 1;
        if !valid {
            gcx.dcx().emit_error(
                "Deref must declare type Target and a safe non-generic deref() -> &Self::Target"
                    .into(),
                Some(gcx.definition_ident(id).span),
            );
        }
    }

    fn check_static(&self, id: DefinitionID) {
        let gcx = self.context;
        let ty = gcx.get_type(id);
        let span = gcx.definition_ident(id).span;
        let mut cs = ConstraintSystem::new(gcx, id);
        self.check_type_wf(ty, span, &mut cs);
        cs.solve_all();
    }

    fn check_constraints(&self, id: DefinitionID) {
        // Basic declaration constraints (where clause) are checked here
        let mut cs = ConstraintSystem::new(self.context, id);
        if matches!(
            self.context.definition_kind(id),
            hir::DefinitionKind::TypeAlias | hir::DefinitionKind::AssociatedType
        ) && let Some(target) = self.context.try_get_alias_type(id)
        {
            self.check_type_wf(target, self.context.definition_ident(id).span, &mut cs);
        }
        cs.solve_all();
    }

    fn check_type_wf(&self, ty: Ty<'ctx>, span: Span, cs: &mut ConstraintSystem<'ctx>) {
        let _ = crate::sema::tycheck::utils::atomic_handle::validate(self.context, ty, span);
        self.check_type_wf_inner(ty, span, cs, false);
    }

    fn check_type_wf_inner(
        &self,
        ty: Ty<'ctx>,
        span: Span,
        cs: &mut ConstraintSystem<'ctx>,
        behind_pointer: bool,
    ) {
        match ty.kind() {
            TyKind::Alias { def_id, args, .. } => {
                cs.add_constraints_for_def(def_id, Some(args), span);
                let normalized = crate::sema::tycheck::utils::normalize_aliases(self.context, ty);
                if normalized != ty {
                    self.check_type_wf_inner(normalized, span, cs, behind_pointer);
                }
            }
            TyKind::Opaque(def_id) => {
                if !behind_pointer {
                    let ident = self.context.definition_ident(def_id);
                    self.context.dcx().emit_error(
                        format!(
                            "opaque type `{}` can only be used behind a pointer",
                            self.context.symbol_text(ident.symbol)
                        ),
                        Some(span),
                    );
                }
            }
            TyKind::Adt(def, args) => {
                cs.add_constraints_for_def(def.id, Some(args), span);
                for arg in args.iter() {
                    if let GenericArgument::Type(t) = arg {
                        self.check_type_wf_inner(*t, span, cs, false);
                    }
                }
            }
            TyKind::Tuple(items) => {
                for item in items.iter() {
                    self.check_type_wf_inner(*item, span, cs, false);
                }
            }
            TyKind::FnPointer { inputs, output, .. } => {
                for input in inputs.iter() {
                    self.check_type_wf_inner(*input, span, cs, false);
                }
                self.check_type_wf_inner(output, span, cs, false);
            }
            TyKind::Array { element, .. } => {
                self.check_type_wf_inner(element, span, cs, false);
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner) => {
                // Opaque types are allowed directly inside pointers/references
                self.check_type_wf_inner(inner, span, cs, true);
            }
            TyKind::BoxedExistential { interfaces } => {
                for iface in interfaces.iter() {
                    cs.add_constraints_for_existential(*iface, span);
                    for arg in iface.arguments.iter() {
                        if let GenericArgument::Type(t) = arg {
                            self.check_type_wf_inner(*t, span, cs, false);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn check_function(&self, id: DefinitionID, _: &hir::Function) {
        let sig = self.context.get_signature(id);
        let ident = self.context.definition_ident(id);
        if sig.abi == Some(hir::Abi::Intrinsic)
            && crate::sema::lowering::intrinsics::atomic::arity(ident.symbol.as_str()).is_some()
            && !crate::sema::lowering::intrinsics::atomic::valid(self.context, id)
        {
            self.context.dcx().emit_error(
                "invalid signature for unsafe scalar atomic intrinsic".into(),
                Some(ident.span),
            );
        }
        if sig.abi == Some(hir::Abi::Intrinsic)
            && matches!(
                ident.symbol.as_str(),
                "__intrinsic_ptr_read" | "__intrinsic_ptr_write"
            )
            && crate::sema::lowering::intrinsics::memory::transfer(self.context, id).is_none()
        {
            self.context.dcx().emit_error(
                "invalid signature for unsafe typed memory access intrinsic".into(),
                Some(ident.span),
            );
        }
        if sig.abi == Some(hir::Abi::Intrinsic)
            && crate::sema::lowering::intrinsics::is_borrow_projection(ident.symbol.as_str())
        {
            if !self.context.definition_is_unsafe(id) {
                self.context.dcx().emit_error(
                    "reference projection intrinsics must be declared unsafe".into(),
                    Some(ident.span),
                );
            } else if crate::sema::lowering::intrinsics::projection_signature(self.context, id)
                .is_none()
            {
                self.context.dcx().emit_error(
                    "invalid signature for reference projection intrinsic".into(),
                    Some(ident.span),
                );
            }
        }
        if sig.abi == Some(hir::Abi::Intrinsic)
            && crate::sema::lowering::intrinsics::is_string_borrow(ident.symbol.as_str())
            && crate::sema::lowering::intrinsics::value_signature(self.context, id).is_none()
        {
            self.context.dcx().emit_error(
                "invalid signature for borrowing string intrinsic".into(),
                Some(ident.span),
            );
        }
        if sig.abi == Some(hir::Abi::Intrinsic)
            && crate::sema::lowering::intrinsics::is_reference_address(ident.symbol.as_str())
            && crate::sema::lowering::intrinsics::value_signature(self.context, id).is_none()
        {
            self.context.dcx().emit_error(
                "invalid signature for reference address intrinsic".into(),
                Some(ident.span),
            );
        }
        if sig.abi == Some(hir::Abi::Intrinsic)
            && crate::sema::lowering::intrinsics::is_pure_address(ident.symbol.as_str())
            && crate::sema::lowering::intrinsics::value_signature(self.context, id).is_none()
        {
            self.context.dcx().emit_error(
                "invalid signature for address calculation intrinsic".into(),
                Some(ident.span),
            );
        }
        if sig.abi == Some(hir::Abi::Intrinsic)
            && crate::sema::lowering::intrinsics::is_class_handle_intrinsic(ident.symbol.as_str())
            && !crate::sema::lowering::intrinsics::class_handle_signature(self.context, id)
        {
            self.context.dcx().emit_error("invalid signature for class handle intrinsic (requires unsafe and an AnyObject type parameter)".into(), Some(ident.span));
        }
        if sig.is_variadic
            && matches!(
                sig.abi,
                Some(hir::Abi::C | hir::Abi::Runtime | hir::Abi::Blocking)
            )
            && sig
                .inputs
                .iter()
                .map(|input| input.ty)
                .chain(std::iter::once(sig.output))
                .any(|ty| {
                    matches!(
                        crate::sema::tycheck::utils::normalize_aliases(self.context, ty).kind(),
                        TyKind::Reference(..)
                    )
                })
        {
            self.context.dcx().emit_error(
                "foreign variadic declarations cannot use safe references; use raw pointers".into(),
                Some(ident.span),
            );
        }
        let mut cs = ConstraintSystem::new(self.context, id);

        for input in sig.inputs.iter() {
            self.check_type_wf(input.ty, ident.span, &mut cs);
        }
        self.check_type_wf(sig.output, ident.span, &mut cs);

        cs.solve_all();
    }

    fn check_struct(&self, id: DefinitionID) {
        let ident = self.context.definition_ident(id);

        if self.has_infinite_size(id) {
            self.context.dcx().emit_error(
                format!(
                    "recursive struct `{}` has infinite size",
                    self.context.symbol_text(ident.symbol)
                ),
                Some(ident.span),
            );
            return;
        }

        let def = self.context.get_struct_definition(id);
        crate::sema::lowering::classes::validate_override_extensions(
            self.context,
            self.context.get_type(id),
        );
        let mut cs = ConstraintSystem::new(self.context, id);
        if let Some(base) = def.class_info.and_then(|info| info.base) {
            self.check_type_wf(base, ident.span, &mut cs);
        }

        for field in def.fields {
            if !is_sized(field.ty) {
                self.context.dcx().emit_error(
                    format!(
                        "field `{}` of struct `{}` does not have a sized type",
                        self.context.symbol_text(field.name),
                        self.context.symbol_text(ident.symbol)
                    ),
                    Some(ident.span),
                );
            }
            self.check_type_wf(field.ty, ident.span, &mut cs);
        }

        implied::check_conformance_implied_bounds(self.context, id, ident.span, &mut cs);
        cs.solve_all();
    }

    fn check_enum(&self, id: DefinitionID) {
        let ident = self.context.definition_ident(id);

        if self.has_infinite_size(id) {
            self.context.dcx().emit_error(
                format!(
                    "recursive enum `{}` has infinite size",
                    self.context.symbol_text(ident.symbol)
                ),
                Some(ident.span),
            );
            return;
        }

        let def = self.context.get_enum_definition(id);
        let mut cs = ConstraintSystem::new(self.context, id);

        for variant in def.variants {
            let (crate::sema::models::EnumVariantKind::Tuple(fields)
            | crate::sema::models::EnumVariantKind::Struct(fields)) = variant.kind
            else {
                continue;
            };
            for (idx, field) in fields.iter().enumerate() {
                if !is_sized(field.ty) {
                    self.context.dcx().emit_error(
                        format!(
                            "field {} of enum variant '{}' in '{}' does not have a sized type",
                            idx,
                            self.context.symbol_text(variant.name),
                            self.context.symbol_text(ident.symbol)
                        ),
                        Some(ident.span),
                    );
                }
                self.check_type_wf(field.ty, ident.span, &mut cs);
            }
        }

        implied::check_conformance_implied_bounds(self.context, id, ident.span, &mut cs);

        cs.solve_all();
    }

    fn check_impl(&self, id: DefinitionID) {
        let ident = self.context.definition_ident(id);
        let mut cs = ConstraintSystem::new(self.context, id);

        implied::check_conformance_implied_bounds(self.context, id, ident.span, &mut cs);

        cs.solve_all();
    }

    fn has_infinite_size(&self, id: DefinitionID) -> bool {
        let mut visiting: FxHashSet<DefinitionID> = FxHashSet::default();
        let mut visited: FxHashSet<DefinitionID> = FxHashSet::default();
        self.dfs_adt_cycle(id, &mut visiting, &mut visited)
    }

    fn dfs_adt_cycle(
        &self,
        current: DefinitionID,
        visiting: &mut FxHashSet<DefinitionID>,
        visited: &mut FxHashSet<DefinitionID>,
    ) -> bool {
        if visiting.contains(&current) {
            return true;
        }
        if visited.contains(&current) {
            return false;
        }
        visited.insert(current);
        visiting.insert(current);

        match self.context.definition_kind(current) {
            crate::sema::resolve::models::DefinitionKind::Struct => {
                let def = self.context.get_struct_definition(current);
                for field in def.fields {
                    let mut deps: Vec<DefinitionID> = vec![];
                    collect_by_value_adt_deps(self.context, field.ty, &mut deps);
                    for dep in deps {
                        if dep.package() != current.package() {
                            continue;
                        }
                        if self.dfs_adt_cycle(dep, visiting, visited) {
                            return true;
                        }
                    }
                }
            }
            crate::sema::resolve::models::DefinitionKind::Enum => {
                let def = self.context.get_enum_definition(current);
                for variant in def.variants {
                    let (crate::sema::models::EnumVariantKind::Tuple(fields)
                    | crate::sema::models::EnumVariantKind::Struct(fields)) = variant.kind
                    else {
                        continue;
                    };
                    for field in fields.iter() {
                        let mut deps: Vec<DefinitionID> = vec![];
                        collect_by_value_adt_deps(self.context, field.ty, &mut deps);
                        for dep in deps {
                            if dep.package() != current.package() {
                                continue;
                            }
                            if self.dfs_adt_cycle(dep, visiting, visited) {
                                return true;
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        visiting.remove(&current);
        false
    }
}

fn is_sized(ty: Ty) -> bool {
    !matches!(
        ty.kind(),
        TyKind::Infer(_) | TyKind::Error | TyKind::Opaque(_)
    )
}

fn collect_by_value_adt_deps(context: GlobalContext, ty: Ty, out: &mut Vec<DefinitionID>) {
    match ty.kind() {
        TyKind::Adt(adt, _) => {
            // A class field stores a fixed-size owning handle, not the object's
            // inline payload. Following it would incorrectly reject recursive
            // enum/class trees and mutually linked class objects.
            if adt.kind == AdtKind::Struct
                && context.get_struct_definition(adt.id).class_info.is_some()
            {
                return;
            }
            if matches!(adt.kind, AdtKind::Struct | AdtKind::Enum) {
                out.push(adt.id);
            }
        }
        TyKind::Pointer(..) | TyKind::Reference(..) => {}
        TyKind::Tuple(items) => {
            for item in items {
                collect_by_value_adt_deps(context, *item, out);
            }
        }
        TyKind::FnPointer { .. } => {}
        _ => {}
    }
}

#[cfg(test)]
mod foreign_borrow_tests {

    #[test]
    fn foreign_variadic_reference_facades_are_rejected_before_codegen() {
        let diagnostics = crate::test_support::analyze_language_item_script(
            "struct Span[T] {}\nextern \"C\" { func native(_ value: &int32, _ args: int32...); }\nfunc main() {}",
            false,
            &[(crate::hir::StdItem::Span, "Span")],
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic.message
                == "foreign variadic declarations cannot use safe references; use raw pointers"),
            "{diagnostics:#?}"
        );
    }
}

#[cfg(test)]
mod projection_intrinsic_tests {

    #[test]
    fn projection_primitives_cannot_be_redeclared_as_safe_or_with_forged_shapes() {
        for (declaration, expected) in [
            (
                "func __intrinsic_ref_project(_ source: &int32, _ data: *const uint8) -> &uint8",
                "reference projection intrinsics must be declared unsafe",
            ),
            (
                "func __intrinsic_array_read_unchecked(_ source: &[int32; 2], _ index: usize) -> &int32",
                "reference projection intrinsics must be declared unsafe",
            ),
            (
                "unsafe func __intrinsic_ref_project_mut(_ source: &int32, _ data: *const uint8) -> &uint8",
                "invalid signature for reference projection intrinsic",
            ),
            (
                "unsafe func __intrinsic_ref_project(_ source: &int32, _ data: *const int32) -> &uint8",
                "invalid signature for reference projection intrinsic",
            ),
            (
                "unsafe func __intrinsic_array_read_unchecked(_ source: &[int32; 2], _ index: int32) -> &int32",
                "invalid signature for reference projection intrinsic",
            ),
            (
                "unsafe func __intrinsic_array_read_unchecked(_ source: &[int32; 2], _ index: usize) -> &int64",
                "invalid signature for reference projection intrinsic",
            ),
        ] {
            let source =
                format!("extern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}");
            let diagnostics =
                crate::test_support::analyze_language_item_script(&source, false, &[]);
            assert!(
                diagnostics.iter().any(|d| d.message == expected),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
}

#[cfg(test)]
mod string_intrinsic_tests {
    #[test]
    fn owning_string_intrinsics_require_the_reviewed_borrow_and_result_shapes() {
        for declaration in [
            "func __intrinsic_string_len(_ value: string) -> usize",
            "func __intrinsic_string_data(_ value: &string) -> &uint8",
            "func __intrinsic_string_slice(_ value: &string, _ start: usize, _ count: usize) -> string",
            "unsafe func __intrinsic_string_slice(_ value: &string, _ start: int32, _ count: usize) -> string",
        ] {
            let source =
                format!("extern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}");
            let diagnostics =
                crate::test_support::analyze_language_item_script(&source, false, &[]);
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message == "invalid signature for borrowing string intrinsic"),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
}

#[cfg(test)]
mod reference_address_intrinsic_tests {
    #[test]
    fn reference_address_protocol_requires_matching_pointee_and_mode() {
        for declaration in [
            "func __intrinsic_ref_to_ptr(_ value: &int32) -> *mut int32",
            "func __intrinsic_ref_to_ptr(_ value: &int32) -> *const int64",
            "func __intrinsic_mut_ref_to_ptr(_ value: &int32, _ extra: usize) -> *mut int32",
        ] {
            let source =
                format!("extern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}");
            let diagnostics =
                crate::test_support::analyze_language_item_script(&source, false, &[]);
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message == "invalid signature for reference address intrinsic"),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
}

#[cfg(test)]
mod pure_address_intrinsic_tests {
    #[test]
    fn address_contracts_require_the_exact_generic_layout_shape() {
        for declaration in [
            "func __intrinsic_size_of() -> usize",
            "func __intrinsic_align_of[T](_ value: &T) -> usize",
            "func __intrinsic_ptr_add[T](_ ptr: *const T, _ count: isize) -> *const T",
            "func __intrinsic_ptr_offset[T](_ ptr: *const T, _ count: usize) -> *const T",
            "func __intrinsic_ptr_sub[T](_ ptr: *mut T, _ count: usize) -> *const T",
            "func __intrinsic_ptr_add[T](_ ptr: *const int32, _ count: usize) -> *const int32",
            "func __intrinsic_ptr_byte_add[T](_ ptr: *const T, _ count: usize) -> &T",
        ] {
            let source =
                format!("extern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}");
            let diagnostics =
                crate::test_support::analyze_language_item_script(&source, false, &[]);
            assert!(
                diagnostics
                    .iter()
                    .any(|d| d.message == "invalid signature for address calculation intrinsic"),
                "{source}\n{diagnostics:#?}"
            );
        }
    }
}

#[cfg(test)]
mod class_handle_intrinsic_tests {
    use crate::{hir::StdItem, test_support::analyze_language_item_script};

    #[test]
    fn class_handle_intrinsics_require_exact_unsafe_class_only_transfers() {
        let items = [(StdItem::AnyObject, "AnyObject")];
        for declaration in [
            "unsafe func __intrinsic_class_owner[T: AnyObject](_ value: &T) -> *const uint8",
            "unsafe func __intrinsic_class_from_owner[T: AnyObject](_ value: *const uint8) -> T",
        ] {
            let source = format!(
                "interface AnyObject {{}}\nextern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}"
            );
            let diagnostics = analyze_language_item_script(&source, false, &items);
            assert!(diagnostics.is_empty(), "{declaration}: {diagnostics:#?}");
        }
        for declaration in [
            "func __intrinsic_class_owner[T: AnyObject](_ value: &T) -> *const uint8",
            "unsafe func __intrinsic_class_owner[T](_ value: &T) -> *const uint8",
            "unsafe func __intrinsic_class_owner[T: AnyObject](_ value: &T) -> *mut uint8",
            "unsafe func __intrinsic_class_owner[T: AnyObject, U](_ value: &T) -> *const uint8",
            "unsafe func __intrinsic_class_from_owner[T](_ value: *const uint8) -> T",
            "unsafe func __intrinsic_class_from_owner[T: AnyObject](_ value: *mut uint8) -> T",
            "unsafe func __intrinsic_class_from_owner[T: AnyObject](_ value: *const uint8) -> &T",
        ] {
            let source = format!(
                "interface AnyObject {{}}\nextern \"taro_intrinsic\" {{ {declaration}; }}\nfunc main() {{}}"
            );
            let diagnostics = analyze_language_item_script(&source, false, &items);
            assert!(
                diagnostics.iter().any(|diagnostic| diagnostic
                    .message
                    .contains("invalid signature for class handle intrinsic")),
                "{declaration}: {diagnostics:#?}"
            );
        }
    }
}

#[cfg(test)]
mod recursive_class_layout_tests {
    use crate::test_support::analyze_script_diagnostics;

    #[test]
    fn class_handles_break_inline_enum_layout_cycles() {
        let errors = analyze_script_diagnostics(
            "enum Tree { case leaf(int32); case node(Node) }\nfinal class Node { readonly value: Tree }\nextend Node { init(_ value: Tree) { self.value = value } }\nfunc main() {}",
        );
        assert!(errors.is_empty(), "{errors:?}");
    }

    #[test]
    fn ordinary_inline_struct_enum_cycles_still_reject() {
        let errors = analyze_script_diagnostics(
            "struct Owner { value: State }\nenum State { case nested(Owner) }\nfunc main() {}",
        );
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("infinite size")),
            "{errors:?}"
        );
    }
}
