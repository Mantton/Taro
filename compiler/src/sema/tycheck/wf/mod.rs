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
            hir::DeclarationKind::Interface(..) => self.check_constraints(node.id),
            hir::DeclarationKind::Struct(_) => {
                self.check_constraints(node.id);
                self.check_struct(node.id);
            }
            hir::DeclarationKind::Enum(_) => {
                self.check_constraints(node.id);
                self.check_enum(node.id);
            }
            hir::DeclarationKind::Function(function) => {
                self.check_constraints(node.id);
                self.check_function(node.id, function);
            }
            hir::DeclarationKind::TypeAlias(..) => self.check_constraints(node.id),
            hir::DeclarationKind::Constant(..) => {}
            hir::DeclarationKind::Variable(..) => {}
            hir::DeclarationKind::Import(..) => {}
            hir::DeclarationKind::Export(..) => {}
            hir::DeclarationKind::Namespace(..) => {}
            hir::DeclarationKind::Extension(..) => {
                self.check_constraints(node.id);
                self.check_extension(node.id);
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
            | hir::AssociatedDeclarationKind::Type(..)
            | hir::AssociatedDeclarationKind::Operator(..) => {
                self.check_constraints(node.id);
            }
            _ => {}
        }

        hir::walk_assoc_declaration(self, node, context)
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_constraints(&self, id: DefinitionID) {
        // Basic declaration constraints (where clause) are checked here
        let mut cs = ConstraintSystem::new(self.context, id);
        cs.solve_all();
    }

    fn check_type_wf(&self, ty: Ty<'ctx>, span: Span, cs: &mut ConstraintSystem<'ctx>) {
        match ty.kind() {
            TyKind::Adt(def, args) => {
                cs.add_constraints_for_def(def.id, Some(args), span);
                for arg in args.iter() {
                    if let GenericArgument::Type(t) = arg {
                        self.check_type_wf(*t, span, cs);
                    }
                }
            }
            TyKind::Tuple(items) => {
                for item in items.iter() {
                    self.check_type_wf(*item, span, cs);
                }
            }
            TyKind::FnPointer { inputs, output } => {
                for input in inputs.iter() {
                    self.check_type_wf(*input, span, cs);
                }
                self.check_type_wf(output, span, cs);
            }
            TyKind::Array { element, .. } => {
                self.check_type_wf(element, span, cs);
            }
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                self.check_type_wf(inner, span, cs);
            }
            TyKind::BoxedExistential { interfaces } => {
                for iface in interfaces.iter() {
                    cs.add_constraints_for_def(iface.id, Some(iface.arguments), span);
                    for arg in iface.arguments.iter() {
                        if let GenericArgument::Type(t) = arg {
                            self.check_type_wf(*t, span, cs);
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
                    ident.symbol.as_str()
                ),
                Some(ident.span),
            );
            return;
        }

        let def = self.context.get_struct_definition(id);
        let mut cs = ConstraintSystem::new(self.context, id);

        for field in def.fields {
            if !is_sized(field.ty) {
                self.context.dcx().emit_error(
                    format!(
                        "field `{}` of struct `{}` does not have a sized type",
                        field.name.as_str(),
                        ident.symbol.as_str()
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
                    ident.symbol.as_str()
                ),
                Some(ident.span),
            );
            return;
        }

        let def = self.context.get_enum_definition(id);
        let mut cs = ConstraintSystem::new(self.context, id);

        for variant in def.variants {
            let crate::sema::models::EnumVariantKind::Tuple(fields) = variant.kind else {
                continue;
            };
            for (idx, field) in fields.iter().enumerate() {
                if !is_sized(field.ty) {
                    self.context.dcx().emit_error(
                        format!(
                            "field {} of enum variant '{}' in '{}' does not have a sized type",
                            idx,
                            variant.name.as_str(),
                            ident.symbol.as_str()
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

    fn check_extension(&self, id: DefinitionID) {
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
                    collect_by_value_adt_deps(field.ty, &mut deps);
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
                    let crate::sema::models::EnumVariantKind::Tuple(fields) = variant.kind else {
                        continue;
                    };
                    for field in fields.iter() {
                        let mut deps: Vec<DefinitionID> = vec![];
                        collect_by_value_adt_deps(field.ty, &mut deps);
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
    !matches!(ty.kind(), TyKind::Infer(_) | TyKind::Error)
}

fn collect_by_value_adt_deps(ty: Ty, out: &mut Vec<DefinitionID>) {
    match ty.kind() {
        TyKind::Adt(adt, _) => {
            if matches!(adt.kind, AdtKind::Struct | AdtKind::Enum) {
                out.push(adt.id);
            }
        }
        TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::GcPtr => {}
        TyKind::Tuple(items) => {
            for item in items {
                collect_by_value_adt_deps(*item, out);
            }
        }
        TyKind::FnPointer { .. } => {}
        _ => {}
    }
}
