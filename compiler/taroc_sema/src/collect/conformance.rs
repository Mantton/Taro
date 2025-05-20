use crate::{
    GlobalContext,
    ty::{ConformanceRecord, InterfaceReference, SimpleType},
    utils::{def_id_of_ty, interface_ref2str},
};
use crate::{
    lower::{ItemCtx, LoweringRequest, TypeLowerer},
    utils::ty_from_simple,
};
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, DefinitionKind, PackageIndex, visitor::HirVisitor};
use taroc_span::Span;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, declaration: &taroc_hir::Declaration) -> Self::Result {
        let def_id = self.context.def_id(declaration.id);
        let kind = self.context.def_kind(def_id);
        if !matches!(kind, DefinitionKind::Extension) {
            return;
        }

        //
        let node = match &declaration.kind {
            taroc_hir::DeclarationKind::Extend(node) => node,
            _ => unreachable!(),
        };

        self.collect(def_id, &node.generics);
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, extend_id: DefinitionID, node: &taroc_hir::Generics) {
        let Some(conformances) = &node.conformance else {
            return;
        };

        let interfaces = &conformances.interfaces;
        if interfaces.is_empty() {
            return;
        }

        let ty_key = self.context.with_type_database(extend_id.package(), |db| {
            *db.extension_ty_map.get(&extend_id).unwrap()
        });

        let self_ty = ty_from_simple(self.context, ty_key);

        let icx = ItemCtx::new(self.context);
        for interface in interfaces {
            let reference = icx.lowerer().lower_interface_reference(
                self_ty,
                interface,
                &LoweringRequest::default(),
            );
            let record = ConformanceRecord {
                target: ty_key,
                interface: reference,
                extension: extend_id,
                location: interface.path.span,
            };

            let parent_pkg = def_id_of_ty(self.context, self_ty)
                .map(|f| f.package())
                .unwrap_or(PackageIndex::new(0));
            if parent_pkg != extend_id.package() {
                if let Some(prev) = self.find_previous_conformance(parent_pkg, ty_key, reference) {
                    self.emit_redundant(interface.path.span, &prev);
                }
            }

            if let Some(prev) =
                self.find_previous_conformance(extend_id.package(), ty_key, reference)
            {
                self.emit_redundant(interface.path.span, &prev);
            } else {
                self.context.with_type_database(extend_id.package(), |db| {
                    db.conformances
                        .entry(ty_key)
                        .or_default()
                        .push(record.clone())
                });
            }
        }
    }

    fn find_previous_conformance(
        &self,
        package_id: PackageIndex,
        ty_key: SimpleType,
        interface: InterfaceReference<'ctx>,
    ) -> Option<ConformanceRecord<'ctx>> {
        self.context.with_type_database(package_id, |db| {
            db.conformances
                .get(&ty_key)
                .into_iter()
                .flat_map(|v| v.iter())
                .find(|rec| rec.interface == interface)
                .cloned()
        })
    }

    fn emit_redundant(&self, span: Span, prev: &ConformanceRecord<'ctx>) {
        let name = interface_ref2str(prev.interface, self.context);
        self.context
            .diagnostics
            .warn(format!("redundant conformance to '{}'", name), span);
        self.context
            .diagnostics
            .info("initial conformance is defined here".into(), prev.location);
    }
}
