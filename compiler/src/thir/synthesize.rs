//! THIR synthesis for compiler-generated method bodies.
//!
//! This module generates actual THIR function bodies for synthesized interface methods
//! (like Clone.clone) that flow through the normal MIR/codegen pipeline.

use crate::{
    compile::context::GlobalContext,
    hir::{DefinitionID, StdInterface},
    sema::{
        models::{GenericArgument, InterfaceReference, SyntheticMethodKind, Ty, TyKind},
        resolve::models::TypeHead,
        tycheck::derive::SyntheticMethodInfo,
    },
    span::{FileID, Span, Symbol},
    thir::{
        AdtExpression, Arm, ArmId, BindingMode, Block, BlockId, Expr, ExprId, ExprKind,
        FieldExpression, FieldIndex, FieldPattern, Param, Pattern, PatternKind, Stmt, StmtId,
        ThirFunction, VariantIndex,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

/// Generate THIR functions for all registered synthetic methods.
pub fn synthesize_all<'ctx>(gcx: GlobalContext<'ctx>) -> Vec<ThirFunction<'ctx>> {
    let synthetic_methods = gcx.get_synthetic_methods();
    let mut functions = Vec::new();

    // We collect them first to avoid borrow conflicts
    let methods: Vec<_> = synthetic_methods.into_iter().collect();

    for ((type_head, method_id), info) in methods {
        // 1. Resolve and validate the conformance witness.
        // We must ensure the witness ID is consistent across compiler phases.
        let syn_id = gcx.with_session_type_database(|db| {
            // Attempt to look up the witness using empty arguments first.
            let interface_ref_empty = crate::sema::models::InterfaceReference {
                id: info.interface_id,
                arguments: &[],
            };

            let mut key = (type_head, interface_ref_empty);

            if !db.conformance_witnesses.contains_key(&key) {
               // Fallback: try looking up with `Self` as a type argument.
               // This handles cases where the interface is parameterized by `Self`.
                let args = gcx.store.interners.intern_generic_args(vec![crate::sema::models::GenericArgument::Type(info.self_ty)]);
                let interface_ref_self = crate::sema::models::InterfaceReference {
                    id: info.interface_id,
                    arguments: args,
                };
                key = (type_head, interface_ref_self);
            }

            if !db.conformance_witnesses.contains_key(&key) {
                panic!("Key missing: unable to find conformance witness for synthetic method synthesis.");
            }

            let witness = db
                .conformance_witnesses
                .get_mut(&key)
                .expect("conformance witness must exist for synthetic method");

            let method_witness = witness
                .method_witnesses
                .get_mut(&method_id)
                .expect("method witness must exist");

            match &mut method_witness.implementation {
                crate::sema::models::MethodImplementation::Synthetic(_, id_opt) => {
                    if let Some(id) = id_opt {
                        *id
                    } else {
                        // Allocate new ID
                        let new_id = gcx.allocate_synthetic_id(gcx.package_index());
                        *id_opt = Some(new_id);
                        new_id
                    }
                }
                _ => panic!("expected synthetic implementation"),
            }
        });

        // Update the info in the database with the allocated ID
        gcx.with_session_type_database(|db| {
            if let Some(entry) = db.synthetic_methods.get_mut(&(type_head, method_id)) {
                entry.syn_id = Some(syn_id);
            }
        });

        // 2. Register Definition (Generics, Signature)
        register_definition(gcx, syn_id, type_head, info);

        // 3. Synthesize Body
        if let Some(func) = synthesize_method(gcx, type_head, method_id, info, syn_id) {
            functions.push(func);
        }
    }

    functions
}

fn register_definition<'ctx>(
    gcx: GlobalContext<'ctx>,
    syn_id: DefinitionID,
    type_head: TypeHead,
    info: SyntheticMethodInfo<'ctx>,
) {
    // Construct Generics
    // For Clone, we usually inherit generics from the Self type.
    // If Self is `Foo[T]`, generics are `[T]`.
    let generics = match info.self_ty.kind() {
        TyKind::Adt(def, _) => gcx.generics_of(def.id).clone(),
        _ => crate::sema::models::Generics {
            parameters: vec![],
            has_self: false,
            parent: None,
            parent_count: 0,
        },
    };

    // Construct Signature
    // func clone(&self) -> Self
    let self_ty = info.self_ty;
    let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        self_ty,
        crate::hir::Mutability::Immutable,
    ));

    let signature = crate::sema::models::LabeledFunctionSignature {
        inputs: vec![crate::sema::models::LabeledFunctionParameter {
            name: Symbol::new("self"),
            ty: self_ref_ty,
            label: None,
            has_default: false,
        }],
        output: self_ty,
        is_variadic: false,
        abi: None,
    };
    let labeled_sig = gcx.store.arenas.function_signatures.alloc(signature);

    // Alloc generics on arena
    let generics = gcx.store.arenas.generics.alloc(generics);

    let def = crate::sema::models::SyntheticDefinition {
        name: info.method_name,
        generics,
        signature: labeled_sig,
        span: synthetic_span(),
    };

    gcx.register_synthetic_definition(syn_id, def);
}

/// Synthesize a single THIR function for a synthetic method.
fn synthesize_method<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    match info.kind {
        SyntheticMethodKind::CopyClone => {
            synthesize_copy_clone(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseClone => {
            synthesize_memberwise_clone(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseHash | SyntheticMethodKind::MemberwiseEquality => {
            // TODO: Implement these
            None
        }
    }
}

/// Create a synthetic span for generated code.
fn synthetic_span() -> Span {
    // Use FileID 0 as a synthetic/builtin file
    Span::empty(FileID::from_raw(0))
}

/// Create a synthetic NodeID for generated code elements.
/// The syn_id is unique per synthetic method, and offset differentiates within a method.
fn synthetic_node_id(syn_id: DefinitionID, offset: u32) -> crate::hir::NodeID {
    // Use the synthetic ID's raw representation as base, which is unique per method.
    // The offset differentiates multiple nodes within the same method.
    // Use high values to avoid collision with user code.
    let base = syn_id.package().raw().wrapping_mul(0x1000);
    let seed = base.wrapping_add(offset);
    crate::hir::NodeID::from_raw(u32::MAX - seed)
}

/// Builder helper for constructing THIR functions.
struct ThirBuilder<'ctx> {
    gcx: GlobalContext<'ctx>,
    stmts: IndexVec<StmtId, Stmt<'ctx>>,
    blocks: IndexVec<BlockId, Block>,
    exprs: IndexVec<ExprId, Expr<'ctx>>,
    arms: IndexVec<ArmId, Arm<'ctx>>,
    span: Span,
}

impl<'ctx> ThirBuilder<'ctx> {
    fn new(gcx: GlobalContext<'ctx>, span: Span) -> Self {
        ThirBuilder {
            gcx,
            stmts: IndexVec::new(),
            blocks: IndexVec::new(),
            exprs: IndexVec::new(),
            arms: IndexVec::new(),
            span,
        }
    }

    fn push_expr(&mut self, kind: ExprKind<'ctx>, ty: Ty<'ctx>) -> ExprId {
        let id = ExprId::from_raw(self.exprs.len() as u32);
        self.exprs.push(Expr {
            kind,
            ty,
            span: self.span,
        });
        id
    }

    fn push_block(&mut self, stmts: Vec<StmtId>, expr: Option<ExprId>) -> BlockId {
        let id = BlockId::from_raw(self.blocks.len() as u32);
        self.blocks.push(Block { id, stmts, expr });
        id
    }
}

/// Synthesize `clone` for Copy types: just dereference self.
/// ```
/// func clone(&self) -> Self {
///     *self
/// }
/// ```
fn synthesize_copy_clone<'ctx>(
    gcx: GlobalContext<'ctx>,
    _type_head: TypeHead,
    _method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    // Create self parameter with synthetic NodeID
    let self_node_id = synthetic_node_id(syn_id, 0);
    let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        info.self_ty,
        crate::hir::Mutability::Immutable,
    ));

    let self_param = Param {
        id: self_node_id,
        name: Symbol::new("self"),
        ty: self_ref_ty,
        span,
    };

    // Build: *self
    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let deref_self = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);

    // Create block with just the deref expression as the return value
    let body_block = builder.push_block(vec![], Some(deref_self));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        span,
        params: vec![self_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: IndexVec::new(),
        match_trees: FxHashMap::default(),
    })
}

/// Synthesize `clone` for non-Copy types: memberwise clone each field.
/// ```
/// func clone(&self) -> Self {
///     Self {
///         field1: self.field1.clone(),
///         field2: self.field2.clone(),
///         ...
///     }
/// }
/// ```
fn synthesize_memberwise_clone<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    _method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(def_id) = type_head else {
        return None;
    };

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    // Create self parameter
    let self_node_id = synthetic_node_id(syn_id, 0);
    let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        info.self_ty,
        crate::hir::Mutability::Immutable,
    ));

    let self_param = Param {
        id: self_node_id,
        name: Symbol::new("self"),
        ty: self_ref_ty,
        span,
    };

    // Get Clone interface for method calls
    let clone_def = gcx.std_interface_def(StdInterface::Clone)?;

    // Build the body based on whether this is a struct or enum
    let struct_def = gcx.try_get_struct_definition(def_id);

    if let Some(struct_def) = struct_def {
        // Struct: create Self { field1: self.field1.clone(), ... }
        let adt_def = struct_def.adt_def;
        let mut field_exprs = Vec::new();

        // Get generic args from self_ty if it's an ADT
        let generic_args = match info.self_ty.kind() {
            TyKind::Adt(_, args) => args,
            _ => &[],
        };

        for (idx, field) in struct_def.fields.iter().enumerate() {
            // Build: self.field_i
            let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
            let deref_self = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);
            let field_access = builder.push_expr(
                ExprKind::Field {
                    lhs: deref_self,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );

            // If field is Copy, just use the value directly; otherwise call clone
            let cloned_field = if gcx.is_type_copyable(field.ty) {
                field_access
            } else {
                // If it's an ADT, we can try to clone it
                match field.ty.kind() {
                    TyKind::Adt(field_def, _) => clone_adt_field(
                        gcx,
                        &mut builder,
                        field_access,
                        field.ty,
                        clone_def,
                        field_def.id,
                    ),
                    _ => {
                        // For non-ADT non-Copy types, just use the field access (shouldn't happen if type checking passed)
                        field_access
                    }
                }
            };

            field_exprs.push(FieldExpression {
                index: FieldIndex::from_usize(idx),
                expression: cloned_field,
            });
        }

        // Build: Self { ... }
        let adt_expr = builder.push_expr(
            ExprKind::Adt(AdtExpression {
                definition: adt_def,
                variant_index: None,
                generic_args,
                fields: field_exprs,
            }),
            info.self_ty,
        );

        let body_block = builder.push_block(vec![], Some(adt_expr));

        return Some(ThirFunction {
            id: syn_id,
            body: Some(body_block),
            span,
            params: vec![self_param],
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: IndexVec::new(),
            match_trees: FxHashMap::default(),
        });
    }

    // Handle enums with match expression
    let enum_def = gcx.try_get_enum_definition(def_id)?;

    synthesize_enum_clone(
        gcx,
        builder,
        self_param,
        self_node_id,
        self_ref_ty,
        info,
        syn_id,
        enum_def,
        clone_def,
    )
}

/// Synthesize `clone` for enum types using a match expression.
/// ```
/// func clone(&self) -> Self {
///     match *self {
///         .Variant1 => .Variant1,
///         .Variant2(a, b) => .Variant2(a.clone(), b.clone()),
///         ...
///     }
/// }
/// ```
fn synthesize_enum_clone<'ctx>(
    gcx: GlobalContext<'ctx>,
    mut builder: ThirBuilder<'ctx>,
    self_param: Param<'ctx>,
    self_node_id: crate::hir::NodeID,
    self_ref_ty: Ty<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enum_def: &crate::sema::models::EnumDefinition<'ctx>,
    clone_def: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    use crate::sema::models::EnumVariantKind;

    let span = synthetic_span();
    let adt_def = enum_def.adt_def;

    // Get generic args from self_ty
    let generic_args = match info.self_ty.kind() {
        TyKind::Adt(_, args) => args,
        _ => &[],
    };

    // Build: *self (the scrutinee)
    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let scrutinee = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);

    // Create match arms for each variant
    let mut arm_ids = Vec::new();
    let mut node_offset = 1u32; // Start after self_node_id

    for (variant_idx, variant) in enum_def.variants.iter().enumerate() {
        let variant_index = VariantIndex::from_usize(variant_idx);

        match &variant.kind {
            EnumVariantKind::Unit => {
                // Unit variant: pattern is just `.Variant`, body returns `.Variant`
                let pattern = Pattern {
                    ty: info.self_ty,
                    span,
                    kind: PatternKind::Variant {
                        definition: adt_def,
                        variant: *variant,
                        subpatterns: vec![],
                    },
                };

                // Body: Self.Variant (unit variant constructor)
                let body_expr = builder.push_expr(
                    ExprKind::Adt(AdtExpression {
                        definition: adt_def,
                        variant_index: Some(variant_index),
                        generic_args,
                        fields: vec![],
                    }),
                    info.self_ty,
                );

                let arm_id = ArmId::from_raw(builder.arms.len() as u32);
                builder.arms.push(Arm {
                    pattern: Box::new(pattern),
                    guard: None,
                    body: body_expr,
                    span,
                });
                arm_ids.push(arm_id);
            }
            EnumVariantKind::Tuple(fields) => {
                // Tuple variant: pattern binds each field, body clones and reconstructs
                let mut subpatterns = Vec::new();
                let mut field_exprs = Vec::new();

                for (field_idx, field) in fields.iter().enumerate() {
                    // Create a binding pattern for this field
                    let binding_node_id = synthetic_node_id(syn_id, node_offset);
                    node_offset += 1;

                    let binding_name = Symbol::new(&format!("_f{}", field_idx));

                    subpatterns.push(FieldPattern {
                        index: FieldIndex::from_usize(field_idx),
                        pattern: Pattern {
                            ty: field.ty,
                            span,
                            kind: PatternKind::Binding {
                                name: binding_name,
                                local: binding_node_id,
                                ty: field.ty,
                                mode: BindingMode::ByValue,
                            },
                        },
                    });

                    // Build expression for cloning this field
                    let field_local = builder.push_expr(ExprKind::Local(binding_node_id), field.ty);

                    let cloned_field = if gcx.is_type_copyable(field.ty) {
                        field_local
                    } else {
                        match field.ty.kind() {
                            TyKind::Adt(field_def, _) => clone_adt_field(
                                gcx,
                                &mut builder,
                                field_local,
                                field.ty,
                                clone_def,
                                field_def.id,
                            ),
                            _ => field_local,
                        }
                    };

                    field_exprs.push(FieldExpression {
                        index: FieldIndex::from_usize(field_idx),
                        expression: cloned_field,
                    });
                }

                let pattern = Pattern {
                    ty: info.self_ty,
                    span,
                    kind: PatternKind::Variant {
                        definition: adt_def,
                        variant: *variant,
                        subpatterns,
                    },
                };

                // Body: Self.Variant(cloned_fields...)
                let body_expr = builder.push_expr(
                    ExprKind::Adt(AdtExpression {
                        definition: adt_def,
                        variant_index: Some(variant_index),
                        generic_args,
                        fields: field_exprs,
                    }),
                    info.self_ty,
                );

                let arm_id = ArmId::from_raw(builder.arms.len() as u32);
                builder.arms.push(Arm {
                    pattern: Box::new(pattern),
                    guard: None,
                    body: body_expr,
                    span,
                });
                arm_ids.push(arm_id);
            }
        }
    }

    // Build the match expression
    let match_expr = builder.push_expr(
        ExprKind::Match {
            scrutinee,
            arms: arm_ids,
        },
        info.self_ty,
    );

    let body_block = builder.push_block(vec![], Some(match_expr));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        span,
        params: vec![self_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_trees: FxHashMap::default(),
    })
}

/// Helper function to generate a call to `clone()` for an ADT field.
fn clone_adt_field<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    field_access: ExprId,
    field_ty: Ty<'ctx>,
    clone_def: DefinitionID,
    field_def_id: DefinitionID,
) -> ExprId {
    let field_type_head = TypeHead::Nominal(field_def_id);

    // Build: field.clone()
    let field_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        field_ty,
        crate::hir::Mutability::Immutable,
    ));
    let field_ref = builder.push_expr(
        ExprKind::Reference {
            mutable: false,
            expr: field_access,
        },
        field_ref_ty,
    );

    let clone_ref = InterfaceReference {
        id: clone_def,
        arguments: &[],
    };

    // Get the clone method from conformance witness
    let Some(witness) =
        crate::sema::tycheck::resolve_conformance_witness(gcx, field_type_head, clone_ref)
    else {
        return field_access;
    };

    // Find the clone method definition
    let Some(reqs) = gcx.get_interface_requirements(clone_def) else {
        return field_access;
    };

    let Some(clone_method) = reqs.methods.iter().find(|m| m.name.as_str() == "clone") else {
        return field_access;
    };

    let Some(method_witness) = witness.method_witnesses.get(&clone_method.id) else {
        return field_access;
    };

    let impl_id = method_witness.implementation.impl_id();

    // If it's synthetic or concrete, use appropriate callee
    let callee_id = impl_id.unwrap_or(clone_method.id);

    let generic_args = gcx
        .store
        .interners
        .intern_generic_args(vec![GenericArgument::Type(field_ty)]);

    let callee_ty = gcx.get_type(callee_id);
    let callee = builder.push_expr(
        ExprKind::Zst {
            id: callee_id,
            generic_args: Some(generic_args),
        },
        callee_ty,
    );

    builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![field_ref],
        },
        field_ty,
    )
}
