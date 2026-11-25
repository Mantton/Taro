//! Bodies for derived `PartialOrd.partialCmp` and `Ord.cmp`.
//!
//! Structs compare their stored fields in declaration order. Enums compare
//! case positions first and, for two values of the same case, the payload
//! fields in order. The first component result that is not "equal" is the
//! answer: `.some(.equal)` for `partialCmp` (so a `.none` also ends the
//! comparison) and `.equal` for `cmp`.

use super::{ThirBuilder, make_zst_callee, synthetic_node_id, synthetic_span};
use crate::{
    compile::context::GlobalContext,
    hir::{DefinitionID, StdItem},
    mir::BinaryOperator,
    sema::{
        models::{
            AdtDef, EnumDefinition, EnumVariant, EnumVariantKind, GenericArgument,
            GenericArguments, SyntheticMethodKind, Ty, TyKind,
        },
        resolve::models::TypeHead,
        tycheck::derive::SyntheticMethodInfo,
    },
    thir::{
        AdtExpression, Arm, ArmId, Constant, ConstantKind, ExprId, ExprKind, FieldExpression,
        FieldIndex, FieldPattern, Param, Pattern, PatternKind, StmtKind, ThirFunction,
        VariantIndex,
    },
};
use rustc_hash::FxHashMap;

/// The result type's shape: `Ordering` or `Optional[Ordering]`.
struct OrderingShape<'ctx> {
    /// The method's result type.
    output: Ty<'ctx>,
    ordering_ty: Ty<'ctx>,
    ordering: AdtDef,
    ordering_variants: &'ctx [EnumVariant<'ctx>],
    /// `Optional` and its `some` case when the result is partial.
    optional: Option<(AdtDef, GenericArguments<'ctx>, usize)>,
}

impl<'ctx> OrderingShape<'ctx> {
    fn new(gcx: GlobalContext<'ctx>, output: Ty<'ctx>, partial: bool) -> Option<Self> {
        let (ordering_ty, optional) = if partial {
            let TyKind::Adt(optional, arguments) = output.kind() else {
                return None;
            };
            let some = gcx.std_item_def(StdItem::OptionalSomeVariant)?;
            let index = gcx
                .get_enum_definition(optional.id)
                .variants
                .iter()
                .position(|variant| variant.def_id == some)?;
            (arguments.first()?.ty()?, Some((optional, arguments, index)))
        } else {
            (output, None)
        };
        let TyKind::Adt(ordering, _) = ordering_ty.kind() else {
            return None;
        };
        Some(OrderingShape {
            output,
            ordering_ty,
            ordering,
            ordering_variants: gcx.get_enum_definition(ordering.id).variants,
            optional,
        })
    }

    fn ordering_index(&self, gcx: GlobalContext<'ctx>, name: &str) -> Option<usize> {
        self.ordering_variants
            .iter()
            .position(|variant| gcx.symbol_eq(variant.name, name))
    }

    /// `.less`, `.equal` or `.greater`, wrapped in `.some` for `partialCmp`.
    fn value(
        &self,
        gcx: GlobalContext<'ctx>,
        builder: &mut ThirBuilder<'ctx>,
        name: &str,
    ) -> Option<ExprId> {
        let index = self.ordering_index(gcx, name)?;
        let ordering = builder.push_expr(
            ExprKind::Adt(AdtExpression {
                base: None,
                definition: self.ordering,
                variant_index: Some(VariantIndex::from_usize(index)),
                generic_args: GenericArguments::empty(),
                fields: vec![],
            }),
            self.ordering_ty,
        );
        let Some((optional, arguments, some)) = self.optional else {
            return Some(ordering);
        };
        Some(builder.push_expr(
            ExprKind::Adt(AdtExpression {
                base: None,
                definition: optional,
                variant_index: Some(VariantIndex::from_usize(some)),
                generic_args: arguments,
                fields: vec![FieldExpression {
                    index: FieldIndex::from_usize(0),
                    expression: ordering,
                }],
            }),
            self.output,
        ))
    }

    /// The pattern for an "equal" component result.
    fn equal_pattern(&self, gcx: GlobalContext<'ctx>) -> Option<Pattern<'ctx>> {
        let span = synthetic_span();
        let index = self.ordering_index(gcx, "equal")?;
        let equal = Pattern {
            ty: self.ordering_ty,
            span,
            kind: PatternKind::Variant {
                definition: self.ordering,
                variant: self.ordering_variants[index],
                subpatterns: vec![],
            },
        };
        let Some((optional, _, some)) = self.optional else {
            return Some(equal);
        };
        Some(Pattern {
            ty: self.output,
            span,
            kind: PatternKind::Variant {
                definition: optional,
                variant: gcx.get_enum_definition(optional.id).variants[some],
                subpatterns: vec![FieldPattern {
                    index: FieldIndex::from_usize(0),
                    pattern: equal,
                }],
            },
        })
    }
}

struct OrderBuilder<'ctx> {
    gcx: GlobalContext<'ctx>,
    builder: ThirBuilder<'ctx>,
    shape: OrderingShape<'ctx>,
    syn_id: DefinitionID,
    method_id: DefinitionID,
    partial: bool,
    next_local: u32,
}

impl<'ctx> OrderBuilder<'ctx> {
    fn local(&mut self, name: &str, ty: Ty<'ctx>) -> (crate::hir::NodeID, Pattern<'ctx>) {
        let id = synthetic_node_id(self.syn_id, self.next_local);
        self.next_local += 1;
        let pattern = Pattern {
            ty,
            span: synthetic_span(),
            kind: PatternKind::Binding {
                name: self
                    .gcx
                    .intern_symbol(&format!("${name}{}", self.next_local)),
                local: id,
                ty,
            },
        };
        (id, pattern)
    }

    fn arm(&mut self, pattern: Pattern<'ctx>, body: ExprId) -> ArmId {
        let id = ArmId::from_raw(self.builder.arms.len() as u32);
        self.builder.arms.push(Arm {
            pattern: Box::new(pattern),
            guard: None,
            body,
            span: synthetic_span(),
        });
        id
    }

    /// Call the component's own `partialCmp` or `cmp`.
    fn compare(&mut self, lhs: ExprId, rhs: ExprId, ty: Ty<'ctx>) -> ExprId {
        let arguments = if self.partial {
            vec![GenericArgument::Type(ty), GenericArgument::Type(ty)]
        } else {
            vec![GenericArgument::Type(ty)]
        };
        let arguments = self.gcx.store.interners.intern_generic_args(arguments);
        let callee = make_zst_callee(self.gcx, &mut self.builder, self.method_id, arguments);
        self.builder.push_expr(
            ExprKind::Call {
                callee,
                args: vec![lhs, rhs],
                is_async: false,
                argument_evaluation_order: None,
            },
            self.shape.output,
        )
    }

    /// `match compare(l0, r0) { case EQUAL => <rest>, case result => result }`,
    /// nested so each later component is compared only after an equal one.
    fn chain(&mut self, components: &[(ExprId, ExprId, Ty<'ctx>)]) -> Option<ExprId> {
        let Some(((lhs, rhs, ty), rest)) = components.split_first() else {
            return self.shape.value(self.gcx, &mut self.builder, "equal");
        };
        let comparison = self.compare(*lhs, *rhs, *ty);
        let next = self.chain(rest)?;
        let equal = self.shape.equal_pattern(self.gcx)?;
        let equal = self.arm(equal, next);
        let (result, pattern) = self.local("order", self.shape.output);
        let value = self
            .builder
            .push_expr(ExprKind::Local(result), self.shape.output);
        let other = self.arm(pattern, value);
        Some(self.builder.push_expr(
            ExprKind::Match {
                scrutinee: comparison,
                arms: vec![equal, other],
                binding_condition: false,
            },
            self.shape.output,
        ))
    }

    fn finish(
        self,
        params: Vec<Param<'ctx>>,
        value: ExprId,
        stmts: Vec<crate::thir::StmtId>,
    ) -> ThirFunction<'ctx> {
        let mut builder = self.builder;
        let body = builder.push_block(stmts, Some(value));
        ThirFunction {
            id: self.syn_id,
            body: Some(body),
            constructor_self: None,
            span: synthetic_span(),
            params,
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: builder.arms,
            match_reports: FxHashMap::default(),
            is_async: false,
        }
    }
}

pub(super) fn synthesize<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(owner) = type_head else {
        return None;
    };
    let partial = info.kind == SyntheticMethodKind::MemberwisePartialOrder;
    let output = gcx.get_signature(syn_id).output;
    let span = synthetic_span();
    let self_id = synthetic_node_id(syn_id, 0);
    let other_id = synthetic_node_id(syn_id, 1);
    let params = vec![
        Param {
            id: self_id,
            name: gcx.intern_symbol("self"),
            ty: info.self_ty,
            span,
        },
        Param {
            id: other_id,
            name: gcx.intern_symbol("other"),
            ty: info.self_ty,
            span,
        },
    ];
    let mut order = OrderBuilder {
        gcx,
        builder: ThirBuilder::new(gcx, span),
        shape: OrderingShape::new(gcx, output, partial)?,
        syn_id,
        method_id: info.method_id,
        partial,
        next_local: 2,
    };

    if let Some(definition) = gcx.try_get_struct_definition(owner) {
        let mut components = Vec::new();
        for (index, field) in definition.fields.iter().enumerate() {
            let mut access = |id| {
                let receiver = order.builder.push_expr(ExprKind::Local(id), info.self_ty);
                order.builder.push_expr(
                    ExprKind::Field {
                        lhs: receiver,
                        index: FieldIndex::from_usize(index),
                    },
                    field.ty,
                )
            };
            let lhs = access(self_id);
            let rhs = access(other_id);
            components.push((lhs, rhs, field.ty));
        }
        let value = order.chain(&components)?;
        return Some(order.finish(params, value, vec![]));
    }

    let definition = gcx.try_get_enum_definition(owner)?;
    let (value, stmts) = enum_order(&mut order, info.self_ty, definition, self_id, other_id)?;
    Some(order.finish(params, value, stmts))
}

/// Compare case positions, then the payloads of two values of one case.
fn enum_order<'ctx>(
    order: &mut OrderBuilder<'ctx>,
    self_ty: Ty<'ctx>,
    definition: &EnumDefinition<'ctx>,
    self_id: crate::hir::NodeID,
    other_id: crate::hir::NodeID,
) -> Option<(ExprId, Vec<crate::thir::StmtId>)> {
    let gcx = order.gcx;
    let span = synthetic_span();
    if definition.variants.is_empty() {
        return Some((order.shape.value(gcx, &mut order.builder, "equal")?, vec![]));
    }
    let tag_ty = gcx.types.uint32;
    let mut stmts = Vec::new();
    let mut tags = Vec::new();
    for (name, id) in [("lhsCase", self_id), ("rhsCase", other_id)] {
        let scrutinee = order.builder.push_expr(ExprKind::Local(id), self_ty);
        let mut arms = Vec::new();
        for (index, variant) in definition.variants.iter().enumerate() {
            let subpatterns = payload(variant)
                .iter()
                .enumerate()
                .map(|(field, entry)| FieldPattern {
                    index: FieldIndex::from_usize(field),
                    pattern: Pattern {
                        ty: entry.ty,
                        span,
                        kind: PatternKind::Wild,
                    },
                })
                .collect();
            let pattern = variant_pattern(definition, *variant, self_ty, subpatterns);
            let position = order.builder.push_expr(
                ExprKind::Literal(Constant {
                    ty: tag_ty,
                    value: ConstantKind::Integer(index as u64),
                }),
                tag_ty,
            );
            arms.push(order.arm(pattern, position));
        }
        let tag = order.builder.push_expr(
            ExprKind::Match {
                scrutinee,
                arms,
                binding_condition: false,
            },
            tag_ty,
        );
        let (local, pattern) = order.local(name, tag_ty);
        stmts.push(order.builder.push_stmt(StmtKind::Let {
            id: local,
            pattern,
            expr: Some(tag),
            ty: tag_ty,
            mutable: false,
        }));
        tags.push(local);
    }

    let same_case = if definition
        .variants
        .iter()
        .all(|variant| payload(variant).is_empty())
    {
        order.shape.value(gcx, &mut order.builder, "equal")?
    } else {
        payload_order(order, self_ty, definition, self_id, other_id)?
    };

    let mut compare_tags = |op| {
        let lhs = order.builder.push_expr(ExprKind::Local(tags[0]), tag_ty);
        let rhs = order.builder.push_expr(ExprKind::Local(tags[1]), tag_ty);
        order
            .builder
            .push_expr(ExprKind::Binary { op, lhs, rhs }, gcx.types.bool)
    };
    let is_less = compare_tags(BinaryOperator::Lt);
    let is_greater = compare_tags(BinaryOperator::Gt);
    let less = order.shape.value(gcx, &mut order.builder, "less")?;
    let greater = order.shape.value(gcx, &mut order.builder, "greater")?;
    let output = order.shape.output;
    let otherwise = order.builder.push_expr(
        ExprKind::If {
            cond: is_greater,
            then_expr: greater,
            else_expr: Some(same_case),
        },
        output,
    );
    let value = order.builder.push_expr(
        ExprKind::If {
            cond: is_less,
            then_expr: less,
            else_expr: Some(otherwise),
        },
        output,
    );
    Some((value, stmts))
}

/// `match self { case .c(l..) => match other { case .c(r..) => chain, case _ => EQUAL } }`.
/// Only reached when both values have the same case, so the fallback is dead.
fn payload_order<'ctx>(
    order: &mut OrderBuilder<'ctx>,
    self_ty: Ty<'ctx>,
    definition: &EnumDefinition<'ctx>,
    self_id: crate::hir::NodeID,
    other_id: crate::hir::NodeID,
) -> Option<ExprId> {
    let gcx = order.gcx;
    let span = synthetic_span();
    let scrutinee = order.builder.push_expr(ExprKind::Local(self_id), self_ty);
    let mut outer = Vec::new();
    for variant in definition.variants.iter() {
        let fields = payload(variant);
        let mut bind = |side: &str| {
            let mut subpatterns = Vec::new();
            let mut locals = Vec::new();
            for (index, field) in fields.iter().enumerate() {
                let (local, pattern) = order.local(side, field.ty);
                subpatterns.push(FieldPattern {
                    index: FieldIndex::from_usize(index),
                    pattern,
                });
                locals.push(local);
            }
            (subpatterns, locals)
        };
        let (lhs_patterns, lhs) = bind("lhs");
        let (rhs_patterns, rhs) = bind("rhs");
        let body = if fields.is_empty() {
            order.shape.value(gcx, &mut order.builder, "equal")?
        } else {
            let components: Vec<_> = fields
                .iter()
                .zip(lhs.iter().zip(rhs.iter()))
                .map(|(field, (lhs, rhs))| {
                    (
                        order.builder.push_expr(ExprKind::Local(*lhs), field.ty),
                        order.builder.push_expr(ExprKind::Local(*rhs), field.ty),
                        field.ty,
                    )
                })
                .collect();
            let same = order.chain(&components)?;
            let same = order.arm(
                variant_pattern(definition, *variant, self_ty, rhs_patterns),
                same,
            );
            let unreachable = order.shape.value(gcx, &mut order.builder, "equal")?;
            let fallback = order.arm(
                Pattern {
                    ty: self_ty,
                    span,
                    kind: PatternKind::Wild,
                },
                unreachable,
            );
            let other = order.builder.push_expr(ExprKind::Local(other_id), self_ty);
            order.builder.push_expr(
                ExprKind::Match {
                    scrutinee: other,
                    arms: vec![same, fallback],
                    binding_condition: false,
                },
                order.shape.output,
            )
        };
        let pattern = variant_pattern(
            definition,
            *variant,
            self_ty,
            if fields.is_empty() {
                vec![]
            } else {
                lhs_patterns
            },
        );
        outer.push(order.arm(pattern, body));
    }
    Some(order.builder.push_expr(
        ExprKind::Match {
            scrutinee,
            arms: outer,
            binding_condition: false,
        },
        order.shape.output,
    ))
}

fn payload<'ctx>(
    variant: &EnumVariant<'ctx>,
) -> &'ctx [crate::sema::models::EnumVariantField<'ctx>] {
    match variant.kind {
        EnumVariantKind::Unit => &[],
        EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => fields,
    }
}

fn variant_pattern<'ctx>(
    definition: &EnumDefinition<'ctx>,
    variant: EnumVariant<'ctx>,
    self_ty: Ty<'ctx>,
    subpatterns: Vec<FieldPattern<'ctx>>,
) -> Pattern<'ctx> {
    Pattern {
        ty: self_ty,
        span: synthetic_span(),
        kind: PatternKind::Variant {
            definition: definition.adt_def,
            variant,
            subpatterns,
        },
    }
}
