//! Body for a derived `Debug.debug`.
//!
//! A struct writes `Name { field: <debug>, other: <debug> }`, or just `Name`
//! when it has no fields. An enum value writes its case name, then its
//! payload: `key('a')` for positional fields, `resize(width: 3, height: 4)`
//! for labeled tuple fields and `click { x: 1, y: 2 }` for record fields. The
//! enum's own name and any generic arguments are not written. Fixed text goes
//! through `std::fmt::__debug_write`; each component uses its own `debug`.

use super::{ThirBuilder, make_zst_callee, synthetic_node_id, synthetic_span};
use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{
            EnumVariantField, EnumVariantKind, GenericArgument, GenericArguments, Ty,
        },
        resolve::models::TypeHead,
        tycheck::derive::SyntheticMethodInfo,
    },
    thir::{
        Arm, ArmId, Constant, ConstantKind, ExprId, ExprKind, FieldIndex, FieldPattern, Param,
        Pattern, PatternKind, StmtId, StmtKind, ThirFunction,
    },
};
use rustc_hash::FxHashMap;

/// Text and component values in the order they are written.
enum Piece<'ctx> {
    Text(String),
    Value(ExprId, Ty<'ctx>),
}

struct DebugBuilder<'ctx> {
    gcx: GlobalContext<'ctx>,
    builder: ThirBuilder<'ctx>,
    syn_id: DefinitionID,
    method_id: DefinitionID,
    write_id: DefinitionID,
    into_id: crate::hir::NodeID,
    into_ty: Ty<'ctx>,
    next_local: u32,
}

impl<'ctx> DebugBuilder<'ctx> {
    fn local(&mut self, ty: Ty<'ctx>) -> (crate::hir::NodeID, Pattern<'ctx>) {
        let id = synthetic_node_id(self.syn_id, self.next_local);
        self.next_local += 1;
        let pattern = Pattern {
            ty,
            span: synthetic_span(),
            kind: PatternKind::Binding {
                name: self
                    .gcx
                    .intern_symbol(&format!("$debug{}", self.next_local)),
                local: id,
                ty,
            },
        };
        (id, pattern)
    }

    fn into(&mut self) -> ExprId {
        self.builder
            .push_expr(ExprKind::Local(self.into_id), self.into_ty)
    }

    fn call(&mut self, callee: ExprId, args: Vec<ExprId>) -> StmtId {
        let call = self.builder.push_expr(
            ExprKind::Call {
                callee,
                args,
                is_async: false,
                argument_evaluation_order: None,
            },
            self.gcx.types.void,
        );
        self.builder.push_stmt_expr(call)
    }

    fn write_text(&mut self, text: &str) -> StmtId {
        let ty = self.gcx.types.string;
        let text = self.builder.push_expr(
            ExprKind::Literal(Constant {
                ty,
                value: ConstantKind::String(self.gcx.intern_symbol(text)),
            }),
            ty,
        );
        let callee = make_zst_callee(
            self.gcx,
            &mut self.builder,
            self.write_id,
            GenericArguments::empty(),
        );
        let into = self.into();
        self.call(callee, vec![into, text])
    }

    fn write_value(&mut self, value: ExprId, ty: Ty<'ctx>) -> StmtId {
        let arguments = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(ty)]);
        let callee = make_zst_callee(self.gcx, &mut self.builder, self.method_id, arguments);
        let into = self.into();
        self.call(callee, vec![value, into])
    }

    /// One statement per run of text and per component.
    fn emit(&mut self, pieces: Vec<Piece<'ctx>>) -> Vec<StmtId> {
        let mut stmts = Vec::new();
        let mut text = String::new();
        for piece in pieces {
            match piece {
                Piece::Text(more) => text.push_str(&more),
                Piece::Value(value, ty) => {
                    if !text.is_empty() {
                        stmts.push(self.write_text(&std::mem::take(&mut text)));
                    }
                    stmts.push(self.write_value(value, ty));
                }
            }
        }
        if !text.is_empty() {
            stmts.push(self.write_text(&text));
        }
        stmts
    }
}

/// `name { a: <a>, b: <b> }` or `name(a: <a>, <b>)`; just `name` without fields.
fn named_fields<'ctx>(
    name: &str,
    record: bool,
    fields: Vec<(Option<String>, ExprId, Ty<'ctx>)>,
) -> Vec<Piece<'ctx>> {
    let mut pieces = vec![Piece::Text(name.to_string())];
    if fields.is_empty() {
        return pieces;
    }
    pieces.push(Piece::Text(if record { " { " } else { "(" }.into()));
    for (index, (label, value, ty)) in fields.into_iter().enumerate() {
        if index > 0 {
            pieces.push(Piece::Text(", ".into()));
        }
        if let Some(label) = label {
            pieces.push(Piece::Text(format!("{label}: ")));
        }
        pieces.push(Piece::Value(value, ty));
    }
    pieces.push(Piece::Text(if record { " }" } else { ")" }.into()));
    pieces
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
    let span = synthetic_span();
    let write_id =
        crate::mir::optimize::async_transform::find_std_function(gcx, "fmt", "__debug_write", span)
            .ok()?;
    let signature = gcx.get_signature(syn_id);
    let into_ty = signature.inputs.get(1)?.ty;
    let self_id = synthetic_node_id(syn_id, 0);
    let into_id = synthetic_node_id(syn_id, 1);
    let params = vec![
        Param {
            id: self_id,
            name: gcx.intern_symbol("self"),
            ty: info.self_ty,
            span,
        },
        Param {
            id: into_id,
            name: gcx.intern_symbol("into"),
            ty: into_ty,
            span,
        },
    ];
    let mut debug = DebugBuilder {
        gcx,
        builder: ThirBuilder::new(gcx, span),
        syn_id,
        method_id: info.method_id,
        write_id,
        into_id,
        into_ty,
        next_local: 2,
    };

    let stmts = if let Some(definition) = gcx.try_get_struct_definition(owner) {
        let name = gcx.symbol_text(gcx.definition_ident(owner).symbol).to_string();
        let fields = definition
            .fields
            .iter()
            .enumerate()
            .map(|(index, field)| {
                let receiver = debug
                    .builder
                    .push_expr(ExprKind::Local(self_id), info.self_ty);
                let value = debug.builder.push_expr(
                    ExprKind::Field {
                        lhs: receiver,
                        index: FieldIndex::from_usize(index),
                    },
                    field.ty,
                );
                (
                    Some(gcx.symbol_text(field.name).to_string()),
                    value,
                    field.ty,
                )
            })
            .collect();
        let pieces = named_fields(&name, true, fields);
        debug.emit(pieces)
    } else if gcx
        .try_get_enum_definition(owner)?
        .variants
        .is_empty()
    {
        // No value of an enum without cases exists to print.
        vec![]
    } else {
        let definition = gcx.try_get_enum_definition(owner)?;
        let scrutinee = debug
            .builder
            .push_expr(ExprKind::Local(self_id), info.self_ty);
        let mut arms = Vec::new();
        for variant in definition.variants.iter() {
            let (record, fields): (bool, &[EnumVariantField<'ctx>]) = match variant.kind {
                EnumVariantKind::Unit => (false, &[]),
                EnumVariantKind::Tuple(fields) => (false, fields),
                EnumVariantKind::Struct(fields) => (true, fields),
            };
            let mut subpatterns = Vec::new();
            let mut components = Vec::new();
            for (index, field) in fields.iter().enumerate() {
                let (local, pattern) = debug.local(field.ty);
                subpatterns.push(FieldPattern {
                    index: FieldIndex::from_usize(index),
                    pattern,
                });
                let value = debug.builder.push_expr(ExprKind::Local(local), field.ty);
                components.push((
                    field.label.map(|label| gcx.symbol_text(label).to_string()),
                    value,
                    field.ty,
                ));
            }
            let name = gcx.symbol_text(variant.name).to_string();
            let pieces = named_fields(&name, record, components);
            let stmts = debug.emit(pieces);
            let block = debug.builder.push_block(stmts, None);
            let body = debug
                .builder
                .push_expr(ExprKind::Block(block), gcx.types.void);
            let pattern = Pattern {
                ty: info.self_ty,
                span,
                kind: PatternKind::Variant {
                    definition: definition.adt_def,
                    variant: *variant,
                    subpatterns,
                },
            };
            let arm = ArmId::from_raw(debug.builder.arms.len() as u32);
            debug.builder.arms.push(Arm {
                pattern: Box::new(pattern),
                guard: None,
                body,
                span,
            });
            arms.push(arm);
        }
        let matched = debug.builder.push_expr(
            ExprKind::Match {
                scrutinee,
                arms,
                binding_condition: false,
            },
            gcx.types.void,
        );
        vec![debug.builder.push_stmt(StmtKind::Expr(matched))]
    };

    let mut builder = debug.builder;
    let body = builder.push_block(stmts, None);
    Some(ThirFunction {
        id: syn_id,
        body: Some(body),
        constructor_self: None,
        span,
        params,
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_reports: FxHashMap::default(),
        is_async: false,
    })
}
