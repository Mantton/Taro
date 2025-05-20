use crate::GlobalContext;
use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};
use crate::ty::Ty;
use taroc_error::CompileResult;
use taroc_hir::{DefinitionKind, visitor::HirVisitor};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

/// Extension Binding, Maps Extension Blocks to Nominal Types
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

impl HirVisitor for Actor<'_> {
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
        let ctx = ItemCtx::new(self.context);
        let ctx = ctx.lowerer();
        let res = self.context.resolution(node.ty.id).resolution();
        let (self_ty, arguments) = match res {
            taroc_hir::Resolution::PrimaryType(_) => {
                (ctx.lower_type(&node.ty, &LoweringRequest::default()), None)
            }
            taroc_hir::Resolution::Definition(ty_def_id, _) => {
                //
                let path = match &node.ty.kind {
                    taroc_hir::TypeKind::Path(path) => path,
                    _ => unreachable!("ICE: non path types should be caught by resolver "),
                };
                let segment = path.segments.last().unwrap();

                let arguments = if segment.arguments.is_some() {
                    let result =
                        ctx.lower_type_arguments(ty_def_id, segment, &LoweringRequest::default());
                    result.ok()
                } else {
                    None
                };

                // self.context
                //     .diagnostics
                //     .warn("Collecting Extension".into(), node.ty.span);

                let self_ty = self.context.type_of(ty_def_id);
                (self_ty, Some((ty_def_id, arguments, node.ty.span)))
            }
            _ => unreachable!(),
        };

        self.collect(self_ty, node);
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, ty: Ty<'ctx>, node: &taroc_hir::Extend) {
        let gcx = self.context;
        // println!("Collecting Extension Methods");

        // Generate Key
        let key = ty.to_simple_type();
        for member in &node.declarations {
            match &member.kind {
                taroc_hir::AssociatedDeclarationKind::Type(_) => {} // Pre-resolved
                taroc_hir::AssociatedDeclarationKind::Constant(_) => {
                    // always static member
                }
                taroc_hir::AssociatedDeclarationKind::Function(node) => {
                    let _ = gcx.predicates_of(gcx.def_id(member.id));
                    if node.has_self() {
                        // println!("Collect Func Method")
                    } else {
                        // static member
                    }
                }
                taroc_hir::AssociatedDeclarationKind::Operator(op, node) => {
                    let _ = gcx.predicates_of(gcx.def_id(member.id));
                    if !node.has_self() {
                        let message = format!("operator must have reciever 'self' parameter");
                        self.context.diagnostics.error(message, node.signature.span);
                        continue;
                    }
                }
            }
        }
    }
}
