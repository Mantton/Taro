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

/// A declaration header may ask for a handwritten decoder before the normal
/// lifecycle pass registers constructors. Retain signatures only, in source order.
pub(crate) struct InitializerHeader {
    extension: DefinitionID,
    id: DefinitionID,
    target: hir::Type,
    function: hir::Function,
}

pub(crate) fn register_decoder_headers(
    gcx: GlobalContext<'_>,
    owner: DefinitionID,
    extension: DefinitionID,
    node: &hir::Impl,
) {
    for member in &node.declarations {
        let hir::AssociatedDeclarationKind::Initializer(function) = &member.kind else {
            continue;
        };
        let [input] = function.signature.prototype.inputs.as_slice() else {
            continue;
        };
        if !input
            .label
            .is_some_and(|label| gcx.symbol_eq(label.identifier.symbol, "from"))
            || gcx.generics_of(member.id).parameters.len() != 1
        {
            continue;
        }
        let header = InitializerHeader {
            extension,
            id: member.id,
            target: (*node.target).clone(),
            function: hir::Function {
                block: None,
                ..function.clone()
            },
        };
        gcx.store
            .decoder_headers
            .borrow_mut()
            .entry(owner)
            .or_default()
            .push(header);
    }
}

pub(crate) fn find_decoder_header<'ctx>(
    gcx: GlobalContext<'ctx>,
    owner: DefinitionID,
    matches: impl Fn(DefinitionID, &LabeledFunctionSignature<'ctx>) -> bool,
) -> Option<DefinitionID> {
    let headers = gcx.store.decoder_headers.borrow_mut().remove(&owner)?;
    let actor = Actor::new(gcx);
    let result = headers.iter().find_map(|header| {
        if gcx.get_impl_target_ty(header.extension).is_none() {
            super::super::impls::target::cache_target(gcx, header.extension, &header.target);
        }
        if let Some(signature) = gcx.try_get_signature(header.id) {
            return matches(header.id, signature).then_some(header.id);
        }
        if !gcx.with_type_database(header.id.package(), |db| {
            db.def_to_constraints.contains_key(&header.id)
        }) {
            super::constraints::collect_header_constraints(
                gcx,
                header.id,
                &header.function.generics,
            );
        }
        let context = hir::FunctionContext::Initializer(hir::AssocContext::Impl(header.extension));
        let signature = actor.build_signature(header.id, &header.function, context, false);
        matches(header.id, &signature).then_some(header.id)
    });
    gcx.store
        .decoder_headers
        .borrow_mut()
        .insert(owner, headers);
    result
}

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
        let signature = self.build_signature(id, node, fn_ctx, true);
        let base = Ty::from_labeled_signature(gcx, &signature);
        let crate::sema::models::TyKind::FnPointer { inputs, output, .. } = base.kind() else {
            unreachable!()
        };
        let ty = Ty::new(
            crate::sema::models::TyKind::FnPointer {
                inputs,
                output,
                effects: crate::sema::models::FunctionPointerEffects {
                    kind: if node.is_async {
                        crate::sema::models::ClosureKind::AsyncFn
                    } else {
                        crate::sema::models::ClosureKind::Fn
                    },
                    is_unsafe: node.is_unsafe,
                    abi: signature.abi,
                },
            },
            gcx,
        );
        gcx.cache_signature(id, signature);
        gcx.cache_type(id, ty);
        #[cfg(test)]
        gcx.dcx()
            .analysis_work
            .collected_callable_headers
            .update(|count| count + 1);
        hir::walk_function(self, id, node, fn_ctx)
    }
}

impl<'ctx> Actor<'ctx> {
    /// The declaration spells the result type. Inside the body the parameter
    /// has the canonical boxed callable type, including across package imports.
    fn lazy_parameter_type(&self, result: Ty<'ctx>, span: crate::span::Span) -> Ty<'ctx> {
        use crate::sema::models::{GenericArgument, InterfaceReference, TyKind};
        let gcx = self.context;
        let Some(id) = gcx.std_item_def(StdItem::Fn) else {
            gcx.dcx().emit_error(
                "lazy parameters require the standard library Fn interface".into(),
                Some(span),
            );
            return Ty::error(gcx);
        };
        let arguments = gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(gcx.types.existential_self),
            GenericArgument::Type(gcx.types.void),
            GenericArgument::Type(result),
        ]);
        let interfaces = gcx
            .store
            .arenas
            .global
            .alloc_slice_clone(&[InterfaceReference {
                id,
                arguments,
                bindings: &[],
            }]);
        Ty::new(TyKind::BoxedExistential { interfaces }, gcx)
    }

    fn build_signature(
        &self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
        register_defaults: bool,
    ) -> LabeledFunctionSignature<'ctx> {
        let ctx = DefTyLoweringCtx::new(id, self.context);
        let mut inputs: Vec<LabeledFunctionParameter> = Vec::new();

        for (idx, param) in node.signature.prototype.inputs.iter().enumerate() {
            let mut ty = ctx.lowerer().lower_type(&param.annotated_type);

            if param.is_lazy {
                ty = self.lazy_parameter_type(ty, param.span);
                if param.is_variadic {
                    self.context.dcx().emit_error(
                        "a lazy parameter cannot be variadic".into(),
                        Some(param.span),
                    );
                }
            }

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

            let default_provider =
                if register_defaults && let Some(default_expr) = &param.default_value {
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
                    self.context.register_default_value_expr(
                        provider_id,
                        default_expr,
                        param.caller_bindings,
                    );

                    // Create and register signature for the provider.
                    // A location-sensitive default receives the omitted argument's call site.
                    let generics = self.context.generics_of(id);
                    let provider_sig = LabeledFunctionSignature {
                        inputs: param
                            .caller_bindings
                            .map(|_| self.context.caller_parameters().to_vec())
                            .unwrap_or_default(),
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
                        kind: crate::sema::models::SyntheticDefinitionKind::Ordinary,
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
                is_lazy: param.is_lazy,
                default_provider,
            });
        }

        let declared_output = if let Some(property_output) = self.getter_output_tys.get(&id) {
            ctx.lowerer().lower_type(property_output)
        } else if let Some(output) = &node.signature.prototype.output {
            if matches!(output.kind, hir::TypeKind::ImplTrait { .. }) {
                if crate::sema::tycheck::opaque::opaque_return_is_supported(node, fn_ctx) {
                    crate::sema::tycheck::opaque::opaque_return_ty(self.context, id)
                } else {
                    self.context.dcx().emit_error(
                        "'some Interface' requires a concrete function or method body and is not allowed in interface requirements or extern declarations"
                            .into(),
                        Some(output.span),
                    );
                    self.context.types.error
                }
            } else {
                ctx.lowerer().lower_type(output)
            }
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
