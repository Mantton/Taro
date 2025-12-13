use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        models::{LabeledFunctionParameter, LabeledFunctionSignature, Ty},
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
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
        fn_ctx: hir::FunctionContext,
    ) -> LabeledFunctionSignature<'ctx> {
        let ctx = DefTyLoweringCtx::new(id, self.context);
        let mut inputs: Vec<LabeledFunctionParameter> = Vec::new();

        let has_explicit_self = node
            .signature
            .prototype
            .inputs
            .first()
            .is_some_and(|param| param.name.symbol.as_str() == "self");

        if let hir::FunctionContext::Assoc(hir::AssocContext::Extension(extension_id)) = fn_ctx {
            if node.is_static {
                if has_explicit_self {
                    self.context.dcx().emit_error(
                        "static functions cannot declare a `self` parameter".to_string(),
                        Some(node.signature.span),
                    );
                }
            } else if !has_explicit_self {
                let self_inner = self.implicit_self_inner_ty(extension_id);
                let self_ty = Ty::new(
                    crate::sema::models::TyKind::Reference(self_inner, hir::Mutability::Immutable),
                    self.context,
                );
                inputs.push(LabeledFunctionParameter {
                    label: None,
                    name: crate::span::Symbol::new("self"),
                    ty: self_ty,
                    has_default: false,
                });
            }
        }

        inputs.extend(node.signature.prototype.inputs.iter().map(|node| {
            LabeledFunctionParameter {
                label: node.label.map(|n| n.identifier.symbol),
                name: node.name.symbol,
                ty: ctx.lowerer().lower_type(&node.annotated_type),
                has_default: node.default_value.is_some(),
            }
        }));

        let output = match fn_ctx {
            hir::FunctionContext::Initializer => {
                if node.signature.prototype.output.is_some() {
                    self.context.dcx().emit_error(
                        "initializers implicitly return `Self` and cannot declare a return type"
                            .to_string(),
                        Some(node.signature.span),
                    );
                }
                self.initializer_return_ty(id)
            }
            _ => {
                if let Some(node) = &node.signature.prototype.output {
                    ctx.lowerer().lower_type(&node)
                } else {
                    self.context.types.void
                }
            }
        };

        LabeledFunctionSignature {
            inputs,
            output,
            is_variadic: false,
            abi: node.abi,
        }
    }

    fn initializer_return_ty(&self, initializer_id: DefinitionID) -> Ty<'ctx> {
        let gcx = self.context;
        let Some(parent) = gcx.definition_parent(initializer_id) else {
            let ident = gcx.definition_ident(initializer_id);
            gcx.dcx().emit_error(
                "internal error: initializer is missing a parent definition".to_string(),
                Some(ident.span),
            );
            return gcx.types.error;
        };

        match gcx.definition_kind(parent) {
            crate::sema::resolve::models::DefinitionKind::Struct => gcx.get_type(parent),
            crate::sema::resolve::models::DefinitionKind::Extension => {
                let Some(head) = gcx.get_extension_type_head(parent) else {
                    let ident = gcx.definition_ident(parent);
                    gcx.dcx().emit_error(
                        "internal error: missing extension identity for initializer".to_string(),
                        Some(ident.span),
                    );
                    return gcx.types.error;
                };
                match head {
                    crate::sema::resolve::models::TypeHead::Nominal(id) => gcx.get_type(id),
                    crate::sema::resolve::models::TypeHead::Primary(p) => match p {
                        crate::sema::resolve::models::PrimaryType::Int(k) => Ty::new_int(gcx, k),
                        crate::sema::resolve::models::PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                        crate::sema::resolve::models::PrimaryType::Float(k) => {
                            Ty::new_float(gcx, k)
                        }
                        crate::sema::resolve::models::PrimaryType::String => todo!(),
                        crate::sema::resolve::models::PrimaryType::Bool => gcx.types.bool,
                        crate::sema::resolve::models::PrimaryType::Rune => gcx.types.rune,
                    },
                    other => todo!("initializer return type for extension target {other:?}"),
                }
            }
            other => todo!("initializer parent kind {other:?}"),
        }
    }

    fn implicit_self_inner_ty(&self, extension_id: DefinitionID) -> Ty<'ctx> {
        let gcx = self.context;
        let Some(head) = gcx.get_extension_type_head(extension_id) else {
            let ident = gcx.definition_ident(extension_id);
            gcx.dcx().emit_error(
                "internal error: missing extension identity for implicit self".to_string(),
                Some(ident.span),
            );
            return gcx.types.error;
        };

        match head {
            crate::sema::resolve::models::TypeHead::Nominal(id) => gcx.get_type(id),
            crate::sema::resolve::models::TypeHead::Primary(p) => match p {
                crate::sema::resolve::models::PrimaryType::Int(k) => Ty::new_int(gcx, k),
                crate::sema::resolve::models::PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                crate::sema::resolve::models::PrimaryType::Float(k) => Ty::new_float(gcx, k),
                crate::sema::resolve::models::PrimaryType::String => todo!(),
                crate::sema::resolve::models::PrimaryType::Bool => gcx.types.bool,
                crate::sema::resolve::models::PrimaryType::Rune => gcx.types.rune,
            },
            _ => todo!("implicit self type for extension target {head:?}"),
        }
    }
}
