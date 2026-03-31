use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor, StdItem},
    sema::{
        models::{LabeledFunctionParameter, LabeledFunctionSignature, Ty},
        tycheck::{
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::instantiate::instantiate_ty_with_args,
        },
    },
};
use rustc_hash::FxHashMap;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    getter_output_tys: FxHashMap<DefinitionID, hir::Type>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            getter_output_tys: FxHashMap::default(),
        }
    }

    fn run(package: &hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Property(property) = &node.kind {
            self.getter_output_tys
                .insert(property.getter_id, *property.ty.clone());
        }
        hir::walk_assoc_declaration(self, node, context)
    }

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

        for (idx, param) in node.signature.prototype.inputs.iter().enumerate() {
            let mut ty = ctx.lowerer().lower_type(&param.annotated_type);

            // Handle variadic parameters
            if param.is_variadic {
                if idx != node.signature.prototype.inputs.len() - 1 {
                    self.context.dcx().emit_error(
                        "only the last parameter can be variadic".into(),
                        Some(param.span),
                    );
                }

                // Desugar T... to Span[T]
                if let Some(span_id) = self.context.std_item_def(StdItem::Span) {
                    let span_ty = self.context.get_type(span_id);
                    let args = vec![crate::sema::models::GenericArgument::Type(ty)];
                    let args = self.context.store.interners.intern_generic_args(args);
                    ty = instantiate_ty_with_args(self.context, span_ty, args);
                } else {
                    self.context.dcx().emit_error(
                        "variadic functions require the standard library 'Span' type".into(),
                        Some(param.span),
                    );
                }
            }

            let default_provider = if let Some(default_expr) = &param.default_value {
                // Variadic parameters cannot have default values
                if param.is_variadic {
                    self.context.dcx().emit_error(
                        "variadic parameters cannot have default values".into(),
                        Some(param.span),
                    );
                }

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
                let fn_name_text = self.context.symbol_text(fn_name);
                let def = crate::sema::models::SyntheticDefinition {
                    name: self
                        .context
                        .intern_symbol(&format!("{}$default_arg{}", fn_name_text, idx)),
                    generics,
                    signature: provider_sig,
                    span: param.span,
                };
                self.context.register_synthetic_definition(provider_id, def);

                Some(provider_id)
            } else {
                None
            };

            inputs.push(LabeledFunctionParameter {
                label: param.label.map(|n| n.identifier.symbol),
                name: param.name.symbol,
                ty,
                default_provider,
            });
        }

        let declared_output = if let Some(property_output) = self.getter_output_tys.get(&id) {
            ctx.lowerer().lower_type(property_output)
        } else if let Some(node) = &node.signature.prototype.output {
            ctx.lowerer().lower_type(node)
        } else {
            self.context.types.void
        };
        let output = if node.is_async {
            self.context.cache_async_body_output(id, declared_output);
            declared_output
        } else {
            declared_output
        };

        // Determine if the function is variadic based on the last parameter
        let is_variadic = node
            .signature
            .prototype
            .inputs
            .last()
            .map_or(false, |p| p.is_variadic);

        LabeledFunctionSignature {
            inputs,
            output,
            is_variadic,
            abi: node.abi,
        }
    }
}
