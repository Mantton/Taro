//! THIR synthesis for compiler-generated method bodies.
//!
//! This module generates actual THIR function bodies for synthesized interface methods
//! (like Clone.clone) that flow through the normal MIR/codegen pipeline.

use crate::{
    compile::context::GlobalContext,
    hir::{DefinitionID, StdInterface},
    sema::{
        models::{
            GenericArgument, GenericArguments, GenericParameter, InterfaceReference,
            SyntheticMethodKind, Ty, TyKind, TyList,
        },
        resolve::models::TypeHead,
        tycheck::derive::SyntheticMethodInfo,
    },
    span::{FileID, Span},
    thir::{
        AdtExpression, Arm, ArmId, BindingMode, Block, BlockId, Constant, ConstantKind, Expr,
        ExprId, ExprKind, FieldExpression, FieldIndex, FieldPattern, Param, Pattern, PatternKind,
        Stmt, StmtId, StmtKind, ThirFunction, VariantIndex,
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
            // Reconstruct the interface reference used to build the witness
            let interface_ref = crate::sema::models::InterfaceReference {
                id: info.interface_id,
                arguments: info.interface_args,
                bindings: info.interface_bindings,
            };
            let key = (type_head, interface_ref);

            if !db.conformance_witnesses.contains_key(&key) {
                panic!("Key missing: unable to find conformance witness for synthetic method synthesis. Key: {:?}", key);
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
    _type_head: TypeHead,
    info: SyntheticMethodInfo<'ctx>,
) {
    let (generics, signature) = match info.kind {
        SyntheticMethodKind::ClosureCall
        | SyntheticMethodKind::ClosureCallMut
        | SyntheticMethodKind::ClosureCallOnce => {
            let TyKind::Closure { inputs, output, .. } = info.self_ty.kind() else {
                return;
            };
            let args_ty = closure_args_ty(gcx, inputs);

            let self_ty = match info.kind {
                SyntheticMethodKind::ClosureCallOnce => info.self_ty,
                SyntheticMethodKind::ClosureCallMut => gcx.store.interners.intern_ty(
                    TyKind::Reference(info.self_ty, crate::hir::Mutability::Mutable),
                ),
                SyntheticMethodKind::ClosureCall => gcx.store.interners.intern_ty(
                    TyKind::Reference(info.self_ty, crate::hir::Mutability::Immutable),
                ),
                _ => info.self_ty,
            };

            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("self"),
                        ty: self_ty,
                        label: None,
                        default_provider: None,
                    },
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("args"),
                        ty: args_ty,
                        label: None,
                        default_provider: None,
                    },
                ],
                output,
                is_variadic: false,
                abi: None,
            };

            let generics = crate::sema::models::Generics {
                parameters: vec![],
                has_self: false,
                parent: None,
                parent_count: 0,
            };
            (generics, signature)
        }
        SyntheticMethodKind::CopyClone | SyntheticMethodKind::MemberwiseClone => {
            let generics = self_type_generics(gcx, info.self_ty);
            let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
                info.self_ty,
                crate::hir::Mutability::Immutable,
            ));
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![crate::sema::models::LabeledFunctionParameter {
                    name: gcx.intern_symbol("self"),
                    ty: self_ref_ty,
                    label: None,
                    default_provider: None,
                }],
                output: info.self_ty,
                is_variadic: false,
                abi: None,
            };
            (generics, signature)
        }
        SyntheticMethodKind::MemberwiseEquality => {
            let rhs_ty = match partial_eq_rhs_ty(info.interface_args, info.self_ty) {
                Some(rhs) => rhs,
                None => return,
            };
            let generics = self_type_generics(gcx, info.self_ty);
            let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
                info.self_ty,
                crate::hir::Mutability::Immutable,
            ));
            let rhs_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
                rhs_ty,
                crate::hir::Mutability::Immutable,
            ));
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("self"),
                        ty: self_ref_ty,
                        label: None,
                        default_provider: None,
                    },
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("other"),
                        ty: rhs_ref_ty,
                        label: None,
                        default_provider: None,
                    },
                ],
                output: gcx.types.bool,
                is_variadic: false,
                abi: None,
            };
            (generics, signature)
        }
        SyntheticMethodKind::MemberwiseHash => {
            let mut generics = self_type_generics(gcx, info.self_ty);
            let method_generics = gcx.generics_of(info.method_id);
            if method_generics.parameters.is_empty() {
                return;
            }

            let mut hasher_param = None;
            for param in &method_generics.parameters {
                let mut cloned = param.clone();
                cloned.index = generics.parent_count + generics.parameters.len();
                if hasher_param.is_none() {
                    hasher_param = Some(GenericParameter {
                        index: cloned.index,
                        name: cloned.name,
                    });
                }
                generics.parameters.push(cloned);
            }

            let hasher_param = hasher_param.expect("hash synthesis requires method generic");
            let hasher_ty = Ty::new(TyKind::Parameter(hasher_param), gcx);
            let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
                info.self_ty,
                crate::hir::Mutability::Immutable,
            ));
            let hasher_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
                hasher_ty,
                crate::hir::Mutability::Mutable,
            ));
            let signature = crate::sema::models::LabeledFunctionSignature {
                inputs: vec![
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("self"),
                        ty: self_ref_ty,
                        label: None,
                        default_provider: None,
                    },
                    crate::sema::models::LabeledFunctionParameter {
                        name: gcx.intern_symbol("hasher"),
                        ty: hasher_ref_ty,
                        label: Some(gcx.intern_symbol("into")),
                        default_provider: None,
                    },
                ],
                output: gcx.types.void,
                is_variadic: false,
                abi: None,
            };
            (generics, signature)
        }
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
        SyntheticMethodKind::MemberwiseHash => {
            synthesize_memberwise_hash(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::MemberwiseEquality => {
            synthesize_memberwise_equality(gcx, type_head, method_id, info, syn_id)
        }
        SyntheticMethodKind::ClosureCall
        | SyntheticMethodKind::ClosureCallMut
        | SyntheticMethodKind::ClosureCallOnce => synthesize_closure_call(gcx, info, syn_id),
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
    _gcx: GlobalContext<'ctx>,
    stmts: IndexVec<StmtId, Stmt<'ctx>>,
    blocks: IndexVec<BlockId, Block>,
    exprs: IndexVec<ExprId, Expr<'ctx>>,
    arms: IndexVec<ArmId, Arm<'ctx>>,
    span: Span,
}

impl<'ctx> ThirBuilder<'ctx> {
    fn new(gcx: GlobalContext<'ctx>, span: Span) -> Self {
        ThirBuilder {
            _gcx: gcx,
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

    fn push_stmt(&mut self, kind: StmtKind<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.stmts.len() as u32);
        self.stmts.push(Stmt {
            kind,
            span: self.span,
        });
        id
    }

    fn push_stmt_expr(&mut self, expr: ExprId) -> StmtId {
        self.push_stmt(StmtKind::Expr(expr))
    }
}

fn self_type_generics<'ctx>(
    gcx: GlobalContext<'ctx>,
    self_ty: Ty<'ctx>,
) -> crate::sema::models::Generics {
    match self_ty.kind() {
        TyKind::Adt(def, _) => gcx.generics_of(def.id).clone(),
        _ => crate::sema::models::Generics {
            parameters: vec![],
            has_self: false,
            parent: None,
            parent_count: 0,
        },
    }
}

fn partial_eq_rhs_ty<'ctx>(
    interface_args: GenericArguments<'ctx>,
    self_ty: Ty<'ctx>,
) -> Option<Ty<'ctx>> {
    match interface_args.get(1) {
        Some(GenericArgument::Type(ty)) => match ty.kind() {
            TyKind::Infer(_) | TyKind::Parameter(_) => Some(self_ty),
            _ => Some(*ty),
        },
        Some(GenericArgument::Const(_)) => None,
        None => Some(self_ty),
    }
}

fn bool_literal<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    value: bool,
) -> ExprId {
    builder.push_expr(
        ExprKind::Literal(Constant {
            ty: gcx.types.bool,
            value: ConstantKind::Bool(value),
        }),
        gcx.types.bool,
    )
}

fn make_zst_callee<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    callee_id: DefinitionID,
    generic_args: GenericArguments<'ctx>,
) -> ExprId {
    let sig = gcx.get_signature(callee_id);
    let inputs: Vec<_> = sig.inputs.iter().map(|p| p.ty).collect();
    let inputs = gcx.store.interners.intern_ty_list(inputs);
    let callee_ty = gcx.store.interners.intern_ty(TyKind::FnPointer {
        inputs,
        output: sig.output,
    });
    builder.push_expr(
        ExprKind::Zst {
            id: callee_id,
            generic_args: Some(generic_args),
        },
        callee_ty,
    )
}

fn emit_hash_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    hash_method_id: DefinitionID,
    value_expr: ExprId,
    value_ty: Ty<'ctx>,
    hasher_param_id: crate::hir::NodeID,
    hasher_ref_ty: Ty<'ctx>,
    hasher_ty: Ty<'ctx>,
) -> ExprId {
    let value_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        value_ty,
        crate::hir::Mutability::Immutable,
    ));
    let value_ref = builder.push_expr(
        ExprKind::Reference {
            mutable: false,
            expr: value_expr,
        },
        value_ref_ty,
    );
    let hasher_local = builder.push_expr(ExprKind::Local(hasher_param_id), hasher_ref_ty);

    let generic_args = gcx.store.interners.intern_generic_args(vec![
        GenericArgument::Type(value_ty),
        GenericArgument::Type(hasher_ty),
    ]);
    let callee = make_zst_callee(gcx, builder, hash_method_id, generic_args);

    builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![value_ref, hasher_local],
        },
        gcx.types.void,
    )
}

fn emit_eq_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    builder: &mut ThirBuilder<'ctx>,
    eq_method_id: DefinitionID,
    lhs_expr: ExprId,
    rhs_expr: ExprId,
    value_ty: Ty<'ctx>,
) -> ExprId {
    let value_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        value_ty,
        crate::hir::Mutability::Immutable,
    ));
    let lhs_ref = builder.push_expr(
        ExprKind::Reference {
            mutable: false,
            expr: lhs_expr,
        },
        value_ref_ty,
    );
    let rhs_ref = builder.push_expr(
        ExprKind::Reference {
            mutable: false,
            expr: rhs_expr,
        },
        value_ref_ty,
    );

    let generic_args = gcx.store.interners.intern_generic_args(vec![
        GenericArgument::Type(value_ty),
        GenericArgument::Type(value_ty),
    ]);
    let callee = make_zst_callee(gcx, builder, eq_method_id, generic_args);
    builder.push_expr(
        ExprKind::Call {
            callee,
            args: vec![lhs_ref, rhs_ref],
        },
        gcx.types.bool,
    )
}

/// Synthesize `clone` for Copy types: just dereference self.
/// ```text
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
        name: gcx.intern_symbol("self"),
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
/// ```text
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
        name: gcx.intern_symbol("self"),
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
            _ => GenericArguments::empty(),
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

fn synthesize_memberwise_hash<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(def_id) = type_head else {
        return None;
    };

    let method_generics = gcx.generics_of(method_id);
    let hasher_name = method_generics
        .parameters
        .first()
        .map(|param| param.name)
        .unwrap_or_else(|| gcx.intern_symbol("H"));

    let self_generics = self_type_generics(gcx, info.self_ty);
    let hasher_index = self_generics.parent_count + self_generics.parameters.len();
    let hasher_ty = Ty::new(
        TyKind::Parameter(GenericParameter {
            index: hasher_index,
            name: hasher_name,
        }),
        gcx,
    );

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let self_node_id = synthetic_node_id(syn_id, 0);
    let hasher_node_id = synthetic_node_id(syn_id, 1);

    let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        info.self_ty,
        crate::hir::Mutability::Immutable,
    ));
    let hasher_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        hasher_ty,
        crate::hir::Mutability::Mutable,
    ));

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_ref_ty,
        span,
    };
    let hasher_param = Param {
        id: hasher_node_id,
        name: gcx.intern_symbol("hasher"),
        ty: hasher_ref_ty,
        span,
    };

    if let Some(struct_def) = gcx.try_get_struct_definition(def_id) {
        let mut stmts = Vec::new();
        for (idx, field) in struct_def.fields.iter().enumerate() {
            let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
            let deref_self = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);
            let field_value = builder.push_expr(
                ExprKind::Field {
                    lhs: deref_self,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );
            let call = emit_hash_call(
                gcx,
                &mut builder,
                method_id,
                field_value,
                field.ty,
                hasher_node_id,
                hasher_ref_ty,
                hasher_ty,
            );
            stmts.push(builder.push_stmt_expr(call));
        }

        let body_block = builder.push_block(stmts, None);
        return Some(ThirFunction {
            id: syn_id,
            body: Some(body_block),
            span,
            params: vec![self_param, hasher_param],
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: IndexVec::new(),
            match_trees: FxHashMap::default(),
        });
    }

    let enum_def = gcx.try_get_enum_definition(def_id)?;
    synthesize_enum_hash(
        gcx,
        builder,
        self_param,
        self_node_id,
        self_ref_ty,
        hasher_param,
        hasher_node_id,
        hasher_ref_ty,
        hasher_ty,
        info,
        syn_id,
        enum_def,
        method_id,
    )
}

fn synthesize_memberwise_equality<'ctx>(
    gcx: GlobalContext<'ctx>,
    type_head: TypeHead,
    method_id: DefinitionID,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TypeHead::Nominal(def_id) = type_head else {
        return None;
    };
    let rhs_ty = partial_eq_rhs_ty(info.interface_args, info.self_ty)?;
    if rhs_ty != info.self_ty {
        return None;
    }

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let self_node_id = synthetic_node_id(syn_id, 0);
    let other_node_id = synthetic_node_id(syn_id, 1);

    let self_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        info.self_ty,
        crate::hir::Mutability::Immutable,
    ));
    let other_ref_ty = gcx.store.interners.intern_ty(TyKind::Reference(
        rhs_ty,
        crate::hir::Mutability::Immutable,
    ));

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_ref_ty,
        span,
    };
    let other_param = Param {
        id: other_node_id,
        name: gcx.intern_symbol("other"),
        ty: other_ref_ty,
        span,
    };

    if let Some(struct_def) = gcx.try_get_struct_definition(def_id) {
        let mut result = bool_literal(gcx, &mut builder, true);
        for (idx, field) in struct_def.fields.iter().enumerate() {
            let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
            let self_deref = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);
            let lhs = builder.push_expr(
                ExprKind::Field {
                    lhs: self_deref,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );

            let other_local = builder.push_expr(ExprKind::Local(other_node_id), other_ref_ty);
            let other_deref = builder.push_expr(ExprKind::Deref(other_local), rhs_ty);
            let rhs = builder.push_expr(
                ExprKind::Field {
                    lhs: other_deref,
                    index: FieldIndex::from_usize(idx),
                },
                field.ty,
            );

            let field_eq = emit_eq_call(gcx, &mut builder, method_id, lhs, rhs, field.ty);
            result = builder.push_expr(
                ExprKind::Logical {
                    op: crate::mir::LogicalOperator::And,
                    lhs: result,
                    rhs: field_eq,
                },
                gcx.types.bool,
            );
        }

        let body_block = builder.push_block(vec![], Some(result));
        return Some(ThirFunction {
            id: syn_id,
            body: Some(body_block),
            span,
            params: vec![self_param, other_param],
            stmts: builder.stmts,
            blocks: builder.blocks,
            exprs: builder.exprs,
            arms: IndexVec::new(),
            match_trees: FxHashMap::default(),
        });
    }

    let enum_def = gcx.try_get_enum_definition(def_id)?;
    synthesize_enum_equality(
        gcx,
        builder,
        self_param,
        self_node_id,
        self_ref_ty,
        other_param,
        other_node_id,
        other_ref_ty,
        info,
        syn_id,
        enum_def,
        method_id,
    )
}

fn synthesize_enum_hash<'ctx>(
    gcx: GlobalContext<'ctx>,
    mut builder: ThirBuilder<'ctx>,
    self_param: Param<'ctx>,
    self_node_id: crate::hir::NodeID,
    self_ref_ty: Ty<'ctx>,
    hasher_param: Param<'ctx>,
    hasher_node_id: crate::hir::NodeID,
    hasher_ref_ty: Ty<'ctx>,
    hasher_ty: Ty<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enum_def: &crate::sema::models::EnumDefinition<'ctx>,
    hash_method_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    use crate::sema::models::EnumVariantKind;

    let span = synthetic_span();
    let adt_def = enum_def.adt_def;
    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let scrutinee = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);

    let mut node_offset = 2u32;
    let mut arm_ids = Vec::new();

    for (variant_idx, variant) in enum_def.variants.iter().enumerate() {
        let mut subpatterns = Vec::new();
        let mut field_binding_ids = Vec::new();
        let mut field_tys = Vec::new();

        if let EnumVariantKind::Tuple(fields) = &variant.kind {
            for (field_idx, field) in fields.iter().enumerate() {
                let binding_node_id = synthetic_node_id(syn_id, node_offset);
                node_offset += 1;
                let binding_name = gcx.intern_symbol(&format!("_f{}", field_idx));
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
                field_binding_ids.push(binding_node_id);
                field_tys.push(field.ty);
            }
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

        let tag_ty = gcx.types.uint32;
        let tag_expr = builder.push_expr(
            ExprKind::Literal(Constant {
                ty: tag_ty,
                value: ConstantKind::Integer(variant_idx as u64),
            }),
            tag_ty,
        );

        let mut stmts = Vec::new();
        let tag_hash = emit_hash_call(
            gcx,
            &mut builder,
            hash_method_id,
            tag_expr,
            tag_ty,
            hasher_node_id,
            hasher_ref_ty,
            hasher_ty,
        );
        stmts.push(builder.push_stmt_expr(tag_hash));

        for (binding_id, field_ty) in field_binding_ids.into_iter().zip(field_tys.into_iter()) {
            let field_local = builder.push_expr(ExprKind::Local(binding_id), field_ty);
            let field_hash = emit_hash_call(
                gcx,
                &mut builder,
                hash_method_id,
                field_local,
                field_ty,
                hasher_node_id,
                hasher_ref_ty,
                hasher_ty,
            );
            stmts.push(builder.push_stmt_expr(field_hash));
        }

        let block = builder.push_block(stmts, None);
        let body = builder.push_expr(ExprKind::Block(block), gcx.types.void);

        let arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(pattern),
            guard: None,
            body,
            span,
        });
        arm_ids.push(arm_id);
    }

    let match_expr = builder.push_expr(
        ExprKind::Match {
            scrutinee,
            arms: arm_ids,
        },
        gcx.types.void,
    );
    let body_block = builder.push_block(vec![], Some(match_expr));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        span,
        params: vec![self_param, hasher_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_trees: FxHashMap::default(),
    })
}

fn synthesize_enum_equality<'ctx>(
    gcx: GlobalContext<'ctx>,
    mut builder: ThirBuilder<'ctx>,
    self_param: Param<'ctx>,
    self_node_id: crate::hir::NodeID,
    self_ref_ty: Ty<'ctx>,
    other_param: Param<'ctx>,
    other_node_id: crate::hir::NodeID,
    other_ref_ty: Ty<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
    enum_def: &crate::sema::models::EnumDefinition<'ctx>,
    eq_method_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    use crate::sema::models::EnumVariantKind;

    let span = synthetic_span();
    let adt_def = enum_def.adt_def;
    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_ref_ty);
    let self_scrutinee = builder.push_expr(ExprKind::Deref(self_local), info.self_ty);

    let mut node_offset = 2u32;
    let mut outer_arms = Vec::new();

    for variant in enum_def.variants.iter() {
        let mut self_subpatterns = Vec::new();
        let mut self_binding_ids = Vec::new();
        let mut field_tys = Vec::new();

        if let EnumVariantKind::Tuple(fields) = &variant.kind {
            for (field_idx, field) in fields.iter().enumerate() {
                let binding_node_id = synthetic_node_id(syn_id, node_offset);
                node_offset += 1;
                let binding_name = gcx.intern_symbol(&format!("_lhs{}", field_idx));
                self_subpatterns.push(FieldPattern {
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
                self_binding_ids.push(binding_node_id);
                field_tys.push(field.ty);
            }
        }

        let outer_pattern = Pattern {
            ty: info.self_ty,
            span,
            kind: PatternKind::Variant {
                definition: adt_def,
                variant: *variant,
                subpatterns: self_subpatterns,
            },
        };

        let other_local = builder.push_expr(ExprKind::Local(other_node_id), other_ref_ty);
        let other_scrutinee = builder.push_expr(ExprKind::Deref(other_local), info.self_ty);

        let mut inner_arms = Vec::new();
        let mut other_subpatterns = Vec::new();
        let mut other_binding_ids = Vec::new();

        if let EnumVariantKind::Tuple(fields) = &variant.kind {
            for (field_idx, field) in fields.iter().enumerate() {
                let binding_node_id = synthetic_node_id(syn_id, node_offset);
                node_offset += 1;
                let binding_name = gcx.intern_symbol(&format!("_rhs{}", field_idx));
                other_subpatterns.push(FieldPattern {
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
                other_binding_ids.push(binding_node_id);
            }
        }

        let mut same_variant_result = bool_literal(gcx, &mut builder, true);
        for ((lhs_id, rhs_id), field_ty) in self_binding_ids
            .iter()
            .zip(other_binding_ids.iter())
            .zip(field_tys.iter())
        {
            let lhs = builder.push_expr(ExprKind::Local(*lhs_id), *field_ty);
            let rhs = builder.push_expr(ExprKind::Local(*rhs_id), *field_ty);
            let field_eq = emit_eq_call(gcx, &mut builder, eq_method_id, lhs, rhs, *field_ty);
            same_variant_result = builder.push_expr(
                ExprKind::Logical {
                    op: crate::mir::LogicalOperator::And,
                    lhs: same_variant_result,
                    rhs: field_eq,
                },
                gcx.types.bool,
            );
        }

        let same_pattern = Pattern {
            ty: info.self_ty,
            span,
            kind: PatternKind::Variant {
                definition: adt_def,
                variant: *variant,
                subpatterns: other_subpatterns,
            },
        };
        let same_arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(same_pattern),
            guard: None,
            body: same_variant_result,
            span,
        });
        inner_arms.push(same_arm_id);

        let false_expr = bool_literal(gcx, &mut builder, false);
        let fallback_arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(Pattern {
                ty: info.self_ty,
                span,
                kind: PatternKind::Wild,
            }),
            guard: None,
            body: false_expr,
            span,
        });
        inner_arms.push(fallback_arm_id);

        let inner_match = builder.push_expr(
            ExprKind::Match {
                scrutinee: other_scrutinee,
                arms: inner_arms,
            },
            gcx.types.bool,
        );

        let outer_arm_id = ArmId::from_raw(builder.arms.len() as u32);
        builder.arms.push(Arm {
            pattern: Box::new(outer_pattern),
            guard: None,
            body: inner_match,
            span,
        });
        outer_arms.push(outer_arm_id);
    }

    let outer_match = builder.push_expr(
        ExprKind::Match {
            scrutinee: self_scrutinee,
            arms: outer_arms,
        },
        gcx.types.bool,
    );
    let body_block = builder.push_block(vec![], Some(outer_match));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        span,
        params: vec![self_param, other_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: builder.arms,
        match_trees: FxHashMap::default(),
    })
}

fn synthesize_closure_call<'ctx>(
    gcx: GlobalContext<'ctx>,
    info: SyntheticMethodInfo<'ctx>,
    syn_id: DefinitionID,
) -> Option<ThirFunction<'ctx>> {
    let TyKind::Closure { inputs, output, .. } = info.self_ty.kind() else {
        return None;
    };

    let span = synthetic_span();
    let mut builder = ThirBuilder::new(gcx, span);

    let args_ty = closure_args_ty(gcx, inputs);

    let (self_param_ty, needs_deref) = match info.kind {
        SyntheticMethodKind::ClosureCallOnce => (info.self_ty, false),
        SyntheticMethodKind::ClosureCallMut => (
            gcx.store.interners.intern_ty(TyKind::Reference(
                info.self_ty,
                crate::hir::Mutability::Mutable,
            )),
            true,
        ),
        _ => (
            gcx.store.interners.intern_ty(TyKind::Reference(
                info.self_ty,
                crate::hir::Mutability::Immutable,
            )),
            true,
        ),
    };

    let self_node_id = synthetic_node_id(syn_id, 0);
    let args_node_id = synthetic_node_id(syn_id, 1);

    let self_param = Param {
        id: self_node_id,
        name: gcx.intern_symbol("self"),
        ty: self_param_ty,
        span,
    };

    let args_param = Param {
        id: args_node_id,
        name: gcx.intern_symbol("args"),
        ty: args_ty,
        span,
    };

    let self_local = builder.push_expr(ExprKind::Local(self_node_id), self_param_ty);
    let callee = if needs_deref {
        builder.push_expr(ExprKind::Deref(self_local), info.self_ty)
    } else {
        self_local
    };

    let mut call_args = Vec::new();
    match inputs.len() {
        0 => {}
        1 => {
            let args_local = builder.push_expr(ExprKind::Local(args_node_id), args_ty);
            call_args.push(args_local);
        }
        _ => {
            for (idx, &input_ty) in inputs.iter().enumerate() {
                let args_local = builder.push_expr(ExprKind::Local(args_node_id), args_ty);
                let field = builder.push_expr(
                    ExprKind::Field {
                        lhs: args_local,
                        index: FieldIndex::from_usize(idx),
                    },
                    input_ty,
                );
                call_args.push(field);
            }
        }
    }

    let call_expr = builder.push_expr(
        ExprKind::Call {
            callee,
            args: call_args,
        },
        output,
    );

    let body_block = builder.push_block(vec![], Some(call_expr));

    Some(ThirFunction {
        id: syn_id,
        body: Some(body_block),
        span,
        params: vec![self_param, args_param],
        stmts: builder.stmts,
        blocks: builder.blocks,
        exprs: builder.exprs,
        arms: IndexVec::new(),
        match_trees: FxHashMap::default(),
    })
}

fn closure_args_ty<'ctx>(gcx: GlobalContext<'ctx>, inputs: TyList<'ctx>) -> Ty<'ctx> {
    match inputs.len() {
        0 => gcx.types.void,
        1 => inputs[0],
        _ => Ty::new(TyKind::Tuple(inputs), gcx),
    }
}

/// Synthesize `clone` for enum types using a match expression.
/// ```text
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
        _ => GenericArguments::empty(),
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

                    let binding_name = gcx.intern_symbol(&format!("_f{}", field_idx));

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
        arguments: GenericArguments::empty(),
        bindings: &[],
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

    let Some(clone_method) = reqs
        .methods
        .iter()
        .find(|m| gcx.symbol_eq(m.name, "clone"))
    else {
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

    // Get the function type from the signature (works for both synthetic and concrete methods)
    let sig = gcx.get_signature(callee_id);
    let inputs: Vec<_> = sig.inputs.iter().map(|p| p.ty).collect();
    let inputs = gcx.store.interners.intern_ty_list(inputs);
    let callee_ty = gcx.store.interners.intern_ty(TyKind::FnPointer {
        inputs,
        output: sig.output,
    });

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
