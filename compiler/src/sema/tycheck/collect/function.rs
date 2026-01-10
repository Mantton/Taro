use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::{LabeledFunctionParameter, LabeledFunctionSignature, Ty},
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
    span::Symbol,
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
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

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_function(
        &mut self,
        id: hir::DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        let gcx = self.context;
        let signature = self.build_signature(id, node, fn_ctx);
        let ty = Ty::from_labeled_signature(gcx, &signature);
        gcx.cache_signature(id, signature);
        gcx.cache_type(id, ty);
        hir::walk_function(self, id, node, fn_ctx)
    }
}

impl<'ctx> Actor<'ctx> {
    fn build_signature(
        &self,
        id: DefinitionID,
        node: &hir::Function,
        _: hir::FunctionContext,
    ) -> LabeledFunctionSignature<'ctx> {
        let ctx = DefTyLoweringCtx::new(id, self.context);
        let mut inputs: Vec<LabeledFunctionParameter> = Vec::new();

        for (idx, node) in node.signature.prototype.inputs.iter().enumerate() {
            let ty = ctx.lowerer().lower_type(&node.annotated_type);

            let default_provider = if let Some(default_expr) = &node.default_value {
                // Allocate a synthetic ID for the provider function
                let provider_id = self
                    .context
                    .allocate_synthetic_id(self.context.package_index());

                // Register the default expression for lowering later
                // SAFETY: The HIR node is allocated in the arena and lives for 'ctx.
                // The visitor signature doesn't express this, so we transmute.
                let default_expr: &'ctx hir::Expression =
                    unsafe { std::mem::transmute(&**default_expr) };
                self.context
                    .register_default_value_expr(provider_id, default_expr);

                // Create and register signature for the provider.
                // Defaults cannot reference parameters, so providers take no inputs.
                let generics = self.context.generics_of(id);
                let provider_sig = LabeledFunctionSignature {
                    inputs: vec![],
                    output: ty,
                    is_variadic: false,
                    abi: None,
                };
                let provider_sig = self
                    .context
                    .store
                    .arenas
                    .function_signatures
                    .alloc(provider_sig);

                let fn_name = self.context.definition_ident(id).symbol;
                let def = crate::sema::models::SyntheticDefinition {
                    name: Symbol::new(&format!("{}$default_arg{}", fn_name, idx)),
                    generics,
                    signature: provider_sig,
                    span: node.span,
                };
                self.context.register_synthetic_definition(provider_id, def);

                Some(provider_id)
            } else {
                None
            };

            inputs.push(LabeledFunctionParameter {
                label: node.label.map(|n| n.identifier.symbol),
                name: node.name.symbol,
                ty,
                default_provider,
            });
        }

        let output = if let Some(node) = &node.signature.prototype.output {
            ctx.lowerer().lower_type(node)
        } else {
            self.context.types.void
        };

        LabeledFunctionSignature {
            inputs,
            output,
            is_variadic: false,
            abi: node.abi,
        }
    }
}
