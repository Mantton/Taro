use crate::{
    GlobalContext,
    lower::{ItemCtx, LoweringRequest, TypeLowerer},
    ty::{
        self, AssociatedTypeDefinition, InterfaceMethodRequirement, InterfaceOperatorRequirement,
    },
};
use std::cell::RefCell;
use taroc_error::CompileResult;
use taroc_hir::{NodeID, visitor::HirVisitor};

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

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        match &d.kind {
            taroc_hir::DeclarationKind::Interface(node) => self.collect(d.id, node),
            _ => {}
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&self, id: NodeID, node: &taroc_hir::InterfaceDefinition) {
        let def_id = self.context.def_id(id);
        let mut map = ty::InterfaceRequirements::default();
        for decl in &node.declarations {
            self.prepare(decl, &mut map);
        }

        // Save Requirements
        let map = self.context.alloc(map);
        self.context
            .with_session_type_database(|db| db.interface_requirements.insert(def_id, map));
    }

    fn prepare(
        &self,
        node: &taroc_hir::AssociatedDeclaration,
        map: &mut ty::InterfaceRequirements<'ctx>,
    ) {
        let gcx = self.context;
        let def_id = gcx.def_id(node.id);
        match &node.kind {
            taroc_hir::AssociatedDeclarationKind::Function(func) => {
                let signature = gcx.fn_signature(def_id);
                let is_required = func.block.is_none();
                let name = node.identifier.symbol;

                let req = InterfaceMethodRequirement {
                    id: def_id,
                    name,
                    signature,
                    is_required,
                };
                map.methods.push(req);
            }
            taroc_hir::AssociatedDeclarationKind::Type(alias) => {
                let req = AssociatedTypeDefinition {
                    id: def_id,
                    name: node.identifier.symbol,
                    default_type: alias.ty.as_ref().map(|hir_ty| {
                        let icx = ItemCtx::new(gcx);
                        icx.lowerer().lower_type(
                            hir_ty,
                            &LoweringRequest {
                                alias_visits: RefCell::new(vec![def_id]),
                            },
                        )
                    }),
                };
                map.types.push(req);
            }
            taroc_hir::AssociatedDeclarationKind::Operator(k, func) => {
                let req = InterfaceOperatorRequirement {
                    kind: *k,
                    signature: gcx.fn_signature(def_id),
                    is_required: func.block.is_none(),
                };

                map.operators.push(req);
            }
            taroc_hir::AssociatedDeclarationKind::Constant(_) => todo!(),
        }
    }
}
