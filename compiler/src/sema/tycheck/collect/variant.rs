use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::{
        models::{
            EnumDefinition, EnumVariant, EnumVariantField, EnumVariantKind,
            LabeledFunctionParameter, LabeledFunctionSignature, Ty, TyKind,
        },
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
};
use rustc_hash::FxHashSet;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Enum(e) = &node.kind {
            self.collect_enum_definition(node.id, e);
        }
        hir::walk_declaration(self, node)
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_enum_definition(&self, id: hir::DefinitionID, node: &hir::Enum) {
        let adt_ty = self.context.get_type(id);
        let TyKind::Adt(adt_def, _) = adt_ty.kind() else {
            self.context
                .dcx()
                .emit_error("expected cached ADT type for enum".into(), None);
            return;
        };

        let ctx = DefTyLoweringCtx::new(id, self.context);
        let mut next_discriminant: u64 = 0;
        let mut used_discriminants: FxHashSet<u64> = FxHashSet::default();
        let mut variants: Vec<EnumVariant<'ctx>> = Vec::with_capacity(node.variants.len());

        for variant in &node.variants {
            let explicit = variant
                .discriminant
                .as_ref()
                .and_then(|disc| self.eval_discriminant(disc));

            if let Some(value) = explicit {
                next_discriminant = value;
            }

            let discriminant = next_discriminant;
            if !used_discriminants.insert(discriminant) {
                self.context.dcx().emit_error(
                    format!("duplicate enum discriminant value {discriminant}").into(),
                    Some(variant.span),
                );
            }
            next_discriminant = next_discriminant.saturating_add(1);

            let kind = match &variant.kind {
                hir::VariantKind::Unit => EnumVariantKind::Unit,
                hir::VariantKind::Tuple(fields) => {
                    let mut out: Vec<EnumVariantField<'ctx>> = Vec::with_capacity(fields.len());
                    for field in fields {
                        let ty = ctx.lowerer().lower_type(&field.ty);
                        let label = field.label.map(|l| l.identifier.symbol);
                        out.push(EnumVariantField { label, ty });
                    }
                    let fields = self.context.store.arenas.global.alloc_slice_clone(&out);
                    EnumVariantKind::Tuple(fields)
                }
            };

            variants.push(EnumVariant {
                name: variant.identifier.symbol,
                def_id: variant.def_id,
                ctor_def_id: variant.ctor_def_id,
                kind,
                discriminant,
            });
        }

        let variants = self
            .context
            .store
            .arenas
            .global
            .alloc_slice_clone(&variants);
        let def = EnumDefinition { adt_def, variants };
        self.cache_variant_constructors(id, &def);
        self.context.cache_enum_definition(id, def);
    }

    fn cache_variant_constructors(&self, enum_id: hir::DefinitionID, def: &EnumDefinition<'ctx>) {
        let enum_ty = self.context.get_type(enum_id);

        for variant in def.variants {
            match variant.kind {
                EnumVariantKind::Unit => {
                    self.context.cache_type(variant.ctor_def_id, enum_ty);
                }
                EnumVariantKind::Tuple(fields) => {
                    let mut inputs: Vec<LabeledFunctionParameter<'ctx>> =
                        Vec::with_capacity(fields.len());
                    let mut input_tys: Vec<Ty<'ctx>> = Vec::with_capacity(fields.len());

                    for (idx, field) in fields.iter().enumerate() {
                        let name = field
                            .label
                            .unwrap_or_else(|| self.context.intern_symbol(&format!("arg{}", idx)));
                        inputs.push(LabeledFunctionParameter {
                            label: field.label,
                            name,
                            ty: field.ty,
                            default_provider: None,
                        });
                        input_tys.push(field.ty);
                    }

                    let signature = LabeledFunctionSignature {
                        inputs,
                        output: enum_ty,
                        is_variadic: false,
                        abi: None,
                    };

                    self.context.cache_signature(variant.ctor_def_id, signature);

                    let inputs = self.context.store.interners.intern_ty_list(input_tys);
                    let fn_ty = Ty::new(
                        TyKind::FnPointer {
                            inputs,
                            output: enum_ty,
                        },
                        self.context,
                    );

                    self.context.cache_type(variant.ctor_def_id, fn_ty);
                }
            }
        }
    }

    fn eval_discriminant(&self, disc: &hir::AnonConst) -> Option<u64> {
        match disc.value.kind {
            hir::ExpressionKind::Literal(hir::Literal::Integer(value)) => Some(value),
            _ => {
                self.context.dcx().emit_error(
                    "enum discriminant must be an integer literal".into(),
                    Some(disc.value.span),
                );
                None
            }
        }
    }
}
