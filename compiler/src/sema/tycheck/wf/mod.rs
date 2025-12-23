use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::models::{AdtKind, Ty, TyKind},
};
use rustc_hash::FxHashSet;

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
            hir::DeclarationKind::Interface(..) => todo!(),
            hir::DeclarationKind::Struct(_) => self.check_struct(node.id),
            hir::DeclarationKind::Enum(_) => self.check_enum(node.id),
            hir::DeclarationKind::Function(function) => self.check_function(node.id, function),
            hir::DeclarationKind::TypeAlias(..) => todo!(),
            hir::DeclarationKind::Constant(..) => todo!(),
            hir::DeclarationKind::Variable(..) => todo!(),
            hir::DeclarationKind::Import(..) => {}
            hir::DeclarationKind::Export(..) => todo!(),
            hir::DeclarationKind::Namespace(..) => todo!(),
            hir::DeclarationKind::Extension(..) => {}
            hir::DeclarationKind::Malformed => unreachable!(),
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(&self, id: DefinitionID, _: &hir::Function) {
        let _ = self.context.get_signature(id);
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
        }
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
            }
        }
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
        TyKind::Adt(adt) => {
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
