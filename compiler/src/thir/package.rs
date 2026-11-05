use crate::{
    compile::{context::GlobalContext, entry::validate_entry_point},
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, Mutability, Resolution},
    mir::{self, LogicalOperator},
    sema::{
        models::{ConstKind, ConstValue, GenericArgument, GenericArguments, Ty, TyKind},
        resolve::models::VariantCtorKind,
        tycheck::{
            lower::{TypeLowerer, item::DefTyLoweringCtx},
            results::TypeCheckResults,
            solve::Adjustment,
            utils::{
                arguments::match_arguments_to_parameters,
                instantiate::{instantiate_signature_with_args, instantiate_ty_with_args},
            },
        },
    },
    thir::{
        self, Block, BlockId, ClosureCapture, Constant, ConstantKind, Expr, ExprId, ExprKind,
        FieldIndex, Param, Stmt, StmtId, StmtKind, ThirFunction, ThirPackage, VariantIndex,
        pattern::pattern_from_hir,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

#[path = "fallible_init.rs"]
mod fallible_init;

pub fn build_package<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: TypeCheckResults<'ctx>,
) -> CompileResult<ThirPackage<'ctx>> {
    // Generated test and benchmark harnesses provide their own entry points.
    let entry = if gcx.config.harness_mode.is_enabled() {
        None
    } else {
        validate_entry_point(&package, gcx)?
    };
    let mut package = Actor::run(package, gcx, results, entry)?;
    thir::passes::exhaustiveness::run(&mut package, gcx)?;
    thir::passes::flow::run(&mut package, gcx)?;
    gcx.dcx().ok()?;
    Ok(package)
}

/// Codec synthesis reuses the ordinary class publication wrapper. Its private
/// decoder body returns a complete payload or an error, never partial storage.
pub(super) fn class_codec_wrapper<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
    helper: DefinitionID,
    body: &ThirFunction<'ctx>,
) -> ThirFunction<'ctx> {
    FunctionLower::class_initializer_wrapper(
        gcx,
        std::rc::Rc::new(TypeCheckResults::default()),
        id,
        helper,
        body,
    )
}

struct Actor<'ctx> {
    gcx: GlobalContext<'ctx>,
    results: std::rc::Rc<TypeCheckResults<'ctx>>,
    functions: FxHashMap<DefinitionID, ThirFunction<'ctx>>,
    entry: Option<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(
        gcx: GlobalContext<'ctx>,
        results: TypeCheckResults<'ctx>,
        entry: Option<DefinitionID>,
    ) -> Self {
        Actor {
            gcx,
            results: std::rc::Rc::new(results),
            functions: FxHashMap::default(),
            entry,
        }
    }

    fn run(
        package: &hir::Package,
        gcx: GlobalContext<'ctx>,
        results: TypeCheckResults<'ctx>,
        entry: Option<DefinitionID>,
    ) -> CompileResult<ThirPackage<'ctx>> {
        let mut actor = Actor::new(gcx, results, entry);
        hir::walk_package(&mut actor, package);

        // Inherited constructors have no HIR declaration. Their private body
        // initializes this exact class's base prefix and defaults before the
        // ordinary publication wrapper exposes any strong handle.
        let inherited: Vec<_> = gcx.store.synthetic_definitions.borrow().iter()
            .filter_map(|(id, definition)| {
                (id.package() == gcx.package_index() && matches!(definition.kind,
                    crate::sema::models::SyntheticDefinitionKind::InheritedClassInitializer { .. }
                    | crate::sema::models::SyntheticDefinitionKind::InheritedInitializerDefault { .. }
                )).then_some((*id, definition.kind))
            }).collect();
        for (id, kind) in inherited {
            for function in
                FunctionLower::inherited_initializer(gcx, actor.results.clone(), id, kind)
            {
                actor.functions.insert(function.id, function);
            }
        }

        // Synthesize THIR for any registered synthetic methods (e.g., derived Clone)
        let synthetic_functions = crate::thir::synthesize::synthesize_all(gcx);
        for func in synthetic_functions {
            actor.functions.insert(func.id, func);
        }

        // Synthesize default value providers
        let default_exprs = gcx.store.default_value_exprs.borrow();
        for (id, expr) in default_exprs.iter() {
            if id.package() != gcx.package_index() {
                continue;
            }
            let (func, nested_closures) =
                FunctionLower::lower_default_provider(gcx, actor.results.clone(), *id, expr);
            actor.functions.insert(*id, func);
            for closure_func in nested_closures {
                actor.functions.insert(closure_func.id, closure_func);
            }
        }
        crate::thir::erased_async_self::run(gcx, &mut actor.functions);
        // Default expressions can themselves introduce opened default calls.
        // Materialize these adapters after lowering every provider expression.
        for function in crate::thir::synthesize::synthesize_opened_defaults(gcx) {
            actor.functions.insert(function.id, function);
        }

        let pkg = ThirPackage {
            functions: actor.functions,
            entry: actor.entry,
        };
        gcx.dcx().ok()?;
        Ok(pkg)
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::StaticVariable(storage) = &node.kind {
            let id = self.gcx.static_initializer_function(node.id);
            let (function, closures) = FunctionLower::lower_default_provider(
                self.gcx,
                self.results.clone(),
                id,
                &storage.initializer,
            );
            self.functions.insert(id, function);
            for closure in closures {
                self.functions.insert(closure.id, closure);
            }
        }
        hir::walk_declaration(self, node);
    }

    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        let (func, nested_closures) =
            FunctionLower::lower(self.gcx, self.results.clone(), id, node, fn_ctx);
        self.functions.insert(id, func);
        // Insert any nested closure bodies
        for closure_func in nested_closures {
            self.functions.insert(closure_func.id, closure_func);
        }
        hir::walk_function(self, id, node, fn_ctx);
    }
}

#[path = "dynamic_self.rs"]
mod dynamic_self;
#[path = "subscript.rs"]
mod subscript;

struct FunctionLower<'ctx> {
    gcx: GlobalContext<'ctx>,
    results: std::rc::Rc<TypeCheckResults<'ctx>>,
    func: ThirFunction<'ctx>,
    /// Nested closure bodies collected during lowering
    nested_closures: Vec<ThirFunction<'ctx>>,
    /// Captured source places; sibling fields may share a root local.
    captures_map: Option<Vec<crate::sema::models::CapturedVar<'ctx>>>,
    /// Remaps source local node ids to synthetic parameter node ids.
    local_remap: Option<FxHashMap<crate::hir::NodeID, crate::hir::NodeID>>,
    next_synthetic_local_raw: u32,
    convenience: Option<(hir::NodeID, hir::NodeID)>,
}

impl<'ctx> FunctionLower<'ctx> {
    fn lower(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        node: &hir::Function,
        function_context: hir::FunctionContext,
    ) -> (ThirFunction<'ctx>, Vec<ThirFunction<'ctx>>) {
        let convenience = node
            .initializer_kind
            .is_some_and(|kind| kind.is_convenience);
        let class_body = if matches!(function_context, hir::FunctionContext::Initializer(_)) {
            if convenience {
                gcx.class_convenience_initializer(id)
            } else {
                gcx.class_payload_initializer(id)
            }
        } else {
            None
        };
        let body_id = class_body.unwrap_or(id);
        let mut lower = FunctionLower {
            gcx,
            results,
            func: ThirFunction {
                id: body_id,
                body: None,
                constructor_self: None,
                span: node.signature.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_reports: FxHashMap::default(),
                is_async: node.is_async,
            },
            nested_closures: Vec::new(),
            captures_map: None,
            local_remap: None,
            next_synthetic_local_raw: u32::MAX,
            convenience: None,
        };

        if lower.results.dynamic_self_contexts.contains_key(&id) {
            let context = lower.fresh_synthetic_local();
            debug_assert_eq!(
                context.raw(),
                crate::sema::tycheck::results::DYNAMIC_SELF_CONTEXT_LOCAL_RAW
            );
        }
        if matches!(function_context, hir::FunctionContext::Initializer(_)) {
            let binding = &node.block.as_ref().expect("initializer body").statements[0];
            let hir::StatementKind::Variable(local) = &binding.kind else {
                unreachable!("constructor self binding")
            };
            if convenience {
                let context = lower.fresh_synthetic_local();
                lower.convenience = Some((local.pattern.id, context));
            } else {
                lower.func.constructor_self = Some(local.pattern.id);
            }
        }
        lower.lower_params(node);
        if let Some((_, context)) = lower.convenience {
            let parameter = gcx.get_signature(body_id).inputs[0];
            lower.func.params.insert(
                0,
                Param {
                    id: context,
                    name: parameter.name,
                    ty: parameter.ty,
                    span: node.signature.span,
                },
            );
        }
        lower.lower_body(node);
        if lower.func.body.is_some() {
            lower.install_dynamic_self_context(id);
        }
        if let Some((binding, _)) = lower.convenience {
            let body = lower.func.body.expect("convenience body");
            if let Some(expression) = lower.func.blocks[body].expr.take() {
                let statement = lower.push_stmt(Stmt {
                    kind: StmtKind::Expr(expression),
                    span: node.signature.span,
                });
                lower.func.blocks[body].stmts.push(statement);
            }
            let value = lower.push_expr(
                ExprKind::Local(binding),
                gcx.initializer_target(body_id),
                node.signature.span,
            );
            let value = if gcx
                .result_parts(gcx.get_signature(body_id).output)
                .is_some()
            {
                lower.initializer_variant(
                    gcx.get_signature(body_id).output,
                    hir::StdItem::ResultOkVariant,
                    value,
                    node.signature.span,
                )
            } else {
                value
            };
            lower.func.blocks[body].expr = Some(value);
        }
        // Derived defaults are installed immediately after successful base
        // initialization, not at the entry of this level's body.
        let derived = gcx
            .class_for_payload(gcx.initializer_target(body_id))
            .is_some_and(|class| gcx.class_base(class).is_some());
        if lower.func.constructor_self.is_some() && !derived {
            lower.lower_constructor_defaults();
        }
        lower.finish_fallible_initializer();
        if let Some(helper) = class_body {
            let wrapper = if convenience {
                Self::class_convenience_wrapper(gcx, lower.results.clone(), id, helper, &lower.func)
            } else {
                Self::class_initializer_wrapper(gcx, lower.results.clone(), id, helper, &lower.func)
            };
            lower.nested_closures.push(lower.func);
            return (wrapper, lower.nested_closures);
        }
        (lower.func, lower.nested_closures)
    }

    /// Inherited entries use the source constructor pipeline and GC roots for
    /// partial fields. Base helpers return private payload values; only the
    /// final designated wrapper allocates the requested class object.
    fn inherited_initializer(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        kind: crate::sema::models::SyntheticDefinitionKind,
    ) -> Vec<ThirFunction<'ctx>> {
        use crate::sema::{
            models::SyntheticDefinitionKind, tycheck::utils::generics::GenericsBuilder,
        };
        let span = gcx.definition_ident(id).span;
        let default = match kind {
            SyntheticDefinitionKind::InheritedInitializerDefault {
                initializer,
                provider,
            } => Some((initializer, provider)),
            _ => None,
        };
        let convenience = default.is_none()
            && gcx
                .class_initializer(gcx.initializer_target(id), id)
                .is_some_and(|entry| entry.is_convenience);
        let helper = if default.is_some() {
            id
        } else if convenience {
            gcx.class_convenience_initializer(id)
                .expect("inherited convenience helper")
        } else {
            gcx.class_payload_initializer(id)
                .expect("inherited payload helper")
        };
        let signature = gcx.get_signature(helper);
        let binding = hir::NodeID::from_raw(u32::MAX);
        let mut lower = Self {
            gcx,
            results,
            func: ThirFunction {
                id: helper,
                body: None,
                constructor_self: (default.is_none() && !convenience).then_some(binding),
                span,
                params: signature
                    .inputs
                    .iter()
                    .enumerate()
                    .map(|(index, parameter)| Param {
                        id: hir::NodeID::from_raw(u32::MAX - 1 - index as u32),
                        name: parameter.name,
                        ty: parameter.ty,
                        span,
                    })
                    .collect(),
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_reports: FxHashMap::default(),
                is_async: false,
            },
            nested_closures: vec![],
            captures_map: None,
            local_remap: None,
            next_synthetic_local_raw: u32::MAX - 1 - signature.inputs.len() as u32,
            convenience: None,
        };
        let identity = GenericsBuilder::identity_for_item(gcx, id);
        let owner = default.map_or(id, |(initializer, _)| initializer);
        let (source, arguments) = gcx
            .inherited_initializer_target(owner, identity)
            .expect("inherited base arguments");
        let target = default.map_or_else(
            || {
                if convenience {
                    gcx.class_convenience_initializer(source)
                        .expect("inherited base convenience helper")
                } else {
                    gcx.class_payload_initializer(source)
                        .expect("inherited base payload helper")
                }
            },
            |(_, provider)| provider,
        );
        let target_signature =
            instantiate_signature_with_args(gcx, gcx.get_signature(target), arguments);
        let callee = lower.push_expr(
            ExprKind::Zst {
                id: target,
                generic_args: Some(arguments),
            },
            Ty::from_labeled_signature(gcx, &target_signature),
            span,
        );
        let args = lower
            .func
            .params
            .clone()
            .iter()
            .map(|parameter| lower.push_expr(ExprKind::Local(parameter.id), parameter.ty, span))
            .collect();
        let value = lower.push_expr(
            ExprKind::Call {
                callee,
                args,
                is_async: false,
                argument_evaluation_order: None,
            },
            target_signature.output,
            span,
        );
        let mut stmts = vec![];
        let result = if default.is_some() {
            Some(value)
        } else if convenience {
            Some(
                lower.map_initializer_success(value, signature.output, span, |lower, value| {
                    lower.checked_construction_result(
                        value,
                        gcx.constructor_value(signature.output),
                        span,
                    )
                }),
            )
        } else {
            let ty = gcx.constructor_value(signature.output);
            let value = lower.propagate_initializer(value, span);
            let declaration = lower.push_stmt(Stmt {
                kind: StmtKind::Let {
                    id: binding,
                    pattern: thir::Pattern {
                        ty,
                        span,
                        kind: thir::PatternKind::Binding {
                            name: gcx.intern_symbol("self"),
                            local: binding,
                            ty,
                        },
                    },
                    expr: None,
                    ty,
                    mutable: true,
                },
                span,
            });
            stmts.push(declaration);
            let TyKind::Adt(payload, arguments) = ty.kind() else {
                unreachable!()
            };
            let base_storage = instantiate_ty_with_args(
                gcx,
                gcx.get_struct_definition(payload.id).fields[0].ty,
                arguments,
            );
            let storage = lower.push_expr(ExprKind::Local(binding), ty, span);
            let target = lower.push_expr(
                ExprKind::Field {
                    lhs: storage,
                    index: FieldIndex::from_raw(0),
                },
                base_storage,
                span,
            );
            let assignment =
                lower.push_expr(ExprKind::Assign { target, value }, gcx.types.void, span);
            stmts.push(lower.push_stmt(Stmt {
                kind: StmtKind::Expr(assignment),
                span,
            }));
            if gcx.is_decoding_initializer(id) {
                // An inherited Swift-style decoder evaluates this level's
                // defaults before calling the inherited decoder. Stage them
                // independently so partial self still obeys base-first access.
                let (early, assignments) = lower.constructor_default_parts(true);
                stmts.splice(1..1, early);
                stmts.extend(assignments);
            } else {
                stmts.extend(lower.constructor_default_statements());
            }
            None
        };
        let block = BlockId::from_raw(0);
        lower.func.blocks.push(Block {
            id: block,
            stmts,
            expr: result,
        });
        lower.func.body = Some(block);
        if default.is_some() {
            return vec![lower.func];
        }
        lower.finish_fallible_initializer();
        let wrapper = if convenience {
            Self::class_convenience_wrapper(gcx, lower.results.clone(), id, helper, &lower.func)
        } else {
            Self::class_initializer_wrapper(gcx, lower.results.clone(), id, helper, &lower.func)
        };
        vec![wrapper, lower.func]
    }

    /// Delegation constructed the requested descriptor, even though the base
    /// convenience body has a statically base-typed result. Use the ordinary
    /// checked owned cast boundary rather than publishing a fixed base payload.
    fn checked_construction_result(
        &mut self,
        value: ExprId,
        target: Ty<'ctx>,
        span: crate::span::Span,
    ) -> ExprId {
        let gcx = self.gcx;
        let optional = gcx
            .std_item_def(hir::StdItem::Optional)
            .expect("inherited convenience construction requires Optional");
        let args = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(target)]);
        let optional_ty = instantiate_ty_with_args(gcx, gcx.get_type(optional), args);
        let checked = self.push_expr(
            ExprKind::ExistentialTryCast { value, target },
            optional_ty,
            span,
        );
        let head = crate::sema::tycheck::utils::type_head_from_value_ty(optional_ty).unwrap();
        let name = gcx.intern_symbol("unwrap");
        let methods = gcx.collect_from_databases(|database| {
            database
                .type_head_to_members
                .get(&head)
                .and_then(|members| members.inherent_instance.get(&name))
                .map(|members| members.members.iter().copied().collect())
                .unwrap_or_default()
        });
        let unwrap = *methods.first().expect("Optional.unwrap");
        let arguments = crate::sema::impl_engine::deduce_impl_subst(
            gcx,
            gcx.definition_parent(unwrap).unwrap(),
            optional_ty,
            &[],
        )
        .expect("Optional unwrap arguments");
        let callee = self.push_expr(
            ExprKind::Zst {
                id: unwrap,
                generic_args: Some(arguments),
            },
            gcx.get_type(unwrap),
            span,
        );
        self.push_expr(
            ExprKind::Call {
                callee,
                args: vec![checked],
                is_async: false,
                argument_evaluation_order: None,
            },
            target,
            span,
        )
    }

    fn class_convenience_wrapper(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        helper: DefinitionID,
        body: &ThirFunction<'ctx>,
    ) -> ThirFunction<'ctx> {
        let span = gcx.definition_ident(id).span;
        let mut lower = Self {
            gcx,
            results,
            func: ThirFunction {
                id,
                body: None,
                constructor_self: None,
                span,
                params: body.params[1..].to_vec(),
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_reports: FxHashMap::default(),
                is_async: false,
            },
            nested_closures: vec![],
            captures_map: None,
            local_remap: None,
            next_synthetic_local_raw: u32::MAX,
            convenience: None,
        };
        let class = gcx.initializer_target(id);
        let TyKind::Adt(_, class_args) = class.kind() else {
            unreachable!()
        };
        let descriptor = gcx
            .class_construction_descriptor(class)
            .expect("class descriptor factory");
        let descriptor_fn = lower.push_expr(
            ExprKind::Zst {
                id: descriptor,
                generic_args: Some(class_args),
            },
            gcx.get_type(descriptor),
            span,
        );
        let context = lower.push_expr(
            ExprKind::Call {
                callee: descriptor_fn,
                args: vec![],
                is_async: false,
                argument_evaluation_order: None,
            },
            gcx.get_signature(descriptor).output,
            span,
        );
        let mut args = vec![context];
        for parameter in body.params[1..].iter() {
            args.push(lower.push_expr(ExprKind::Local(parameter.id), parameter.ty, span));
        }
        let identity =
            crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(gcx, id);
        let callee = lower.push_expr(
            ExprKind::Zst {
                id: helper,
                generic_args: Some(identity),
            },
            gcx.get_type(helper),
            span,
        );
        let result = lower.push_expr(
            ExprKind::Call {
                callee,
                args,
                is_async: false,
                argument_evaluation_order: None,
            },
            gcx.get_signature(id).output,
            span,
        );
        let block = lower.func.blocks.push(Block {
            id: BlockId::from_raw(0),
            stmts: vec![],
            expr: Some(result),
        });
        lower.func.body = Some(block);
        lower.func
    }

    fn class_initializer_wrapper(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        helper: DefinitionID,
        payload_body: &ThirFunction<'ctx>,
    ) -> ThirFunction<'ctx> {
        let span = payload_body.span;
        let mut lower = Self {
            gcx,
            results,
            func: ThirFunction {
                id,
                body: None,
                constructor_self: None,
                span,
                params: payload_body.params.clone(),
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_reports: FxHashMap::default(),
                is_async: false,
            },
            nested_closures: vec![],
            captures_map: None,
            local_remap: None,
            next_synthetic_local_raw: u32::MAX,
            convenience: None,
        };
        let signature = gcx.get_signature(id);
        let payload = gcx.get_signature(helper).output;
        let identity =
            crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(gcx, id);
        let arguments: Vec<_> = lower
            .func
            .params
            .clone()
            .iter()
            .map(|param| lower.push_expr(ExprKind::Local(param.id), param.ty, param.span))
            .collect();
        let callee = lower.push_expr(
            ExprKind::Zst {
                id: helper,
                generic_args: Some(identity),
            },
            gcx.get_type(helper),
            span,
        );
        let initialized = lower.push_expr(
            ExprKind::Call {
                callee,
                args: arguments,
                is_async: false,
                argument_evaluation_order: None,
            },
            payload,
            span,
        );
        let result =
            lower.map_initializer_success(initialized, signature.output, span, |lower, payload| {
                lower.publish_class_payload(payload, gcx.constructor_value(signature.output), span)
            });
        let block = BlockId::from_raw(0);
        lower.func.blocks.push(Block {
            id: block,
            stmts: vec![],
            expr: Some(result),
        });
        lower.func.body = Some(block);
        lower.func
    }

    /// Publish complete private payload storage exactly once.
    fn publish_class_payload(
        &mut self,
        initialized: ExprId,
        class: Ty<'ctx>,
        span: crate::span::Span,
    ) -> ExprId {
        let gcx = self.gcx;
        let payload = self.func.exprs[initialized].ty;
        let allocate = crate::mir::optimize::async_transform::find_std_function(
            gcx,
            "runtime",
            "__classAllocatePayload",
            span,
        )
        .unwrap_or_else(|_| panic!("class publication requires std runtime"));
        let allocate_arguments = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(payload)]);
        let allocator = self.push_expr(
            ExprKind::Zst {
                id: allocate,
                generic_args: Some(allocate_arguments),
            },
            gcx.get_type(allocate),
            span,
        );
        let handle_ty = gcx.get_type(
            gcx.std_item_def(hir::StdItem::ClassHandle)
                .expect("ClassHandle lang item"),
        );
        let handle = self.push_expr(
            ExprKind::Call {
                callee: allocator,
                args: vec![initialized],
                is_async: false,
                argument_evaluation_order: None,
            },
            handle_ty,
            span,
        );
        let transfer = crate::mir::optimize::async_transform::find_std_function(
            gcx,
            "intrinsic",
            "__intrinsic_class_from_handle",
            span,
        )
        .unwrap_or_else(|_| panic!("class publication requires class handle intrinsic"));
        let transfer_arguments = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(class)]);
        let transfer = self.push_expr(
            ExprKind::Zst {
                id: transfer,
                generic_args: Some(transfer_arguments),
            },
            gcx.get_type(transfer),
            span,
        );
        self.push_expr(
            ExprKind::Call {
                callee: transfer,
                args: vec![handle],
                is_async: false,
                argument_evaluation_order: None,
            },
            class,
            span,
        )
    }

    fn lower_default_provider(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        expr: &hir::Expression,
    ) -> (ThirFunction<'ctx>, Vec<ThirFunction<'ctx>>) {
        let mut lower = FunctionLower {
            gcx,
            results,
            func: ThirFunction {
                id,
                body: None,
                constructor_self: None,
                span: expr.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_reports: FxHashMap::default(),
                is_async: false,
            },
            nested_closures: Vec::new(),
            captures_map: None,
            local_remap: None,
            next_synthetic_local_raw: u32::MAX,
            convenience: None,
        };

        let expr_id = lower.lower_expr(expr);

        let block_id = BlockId::from_raw(lower.func.blocks.len() as u32);
        lower.func.blocks.push(Block {
            id: block_id,
            stmts: vec![],
            expr: Some(expr_id),
        });

        lower.func.body = Some(block_id);
        (lower.func, lower.nested_closures)
    }

    fn lower_indirect_call(
        &mut self,
        callee: ExprId,
        args: Vec<ExprId>,
        argument_evaluation_order: Option<Vec<usize>>,
        is_async: bool,
        span: crate::span::Span,
    ) -> ExprKind<'ctx> {
        if let Some(callable) = crate::sema::tycheck::utils::callable::existential_callable(
            self.gcx,
            self.func.exprs[callee].ty,
        ) {
            assert!(
                argument_evaluation_order.is_none(),
                "dynamic callables have no named/default argument arrangement"
            );
            // Invocation syntax is the callable interface's ordinary
            // method call. Its implicit receiver is the erased value, so
            // ordinary argument copying must snapshot its payload as well.
            let mut receiver = callee;
            while let TyKind::Reference(inner) = self.func.exprs[receiver].ty.kind() {
                receiver = self.push_expr(ExprKind::Deref(receiver), inner, span);
            }
            let args_ty = callable.interface.arguments[1].ty().unwrap();
            let packed_args = if matches!(args_ty.kind(), TyKind::Tuple(_)) {
                self.push_expr(ExprKind::Tuple { fields: args }, args_ty, span)
            } else {
                // An abstract Args: Tuple parameter is already a pack;
                // its arity only becomes known after instantiation.
                let [argument] = args.as_slice() else {
                    unreachable!("abstract callable pack arity was checked")
                };
                *argument
            };
            let method_id = callable
                .method_id(self.gcx)
                .expect("callable method missing");
            let signature = instantiate_signature_with_args(
                self.gcx,
                self.gcx.get_signature(method_id),
                callable.interface.arguments,
            );
            let method_ty = Ty::from_labeled_signature(self.gcx, &signature);
            let method = self.push_expr(
                ExprKind::Zst {
                    id: method_id,
                    generic_args: Some(callable.interface.arguments),
                },
                method_ty,
                span,
            );
            return ExprKind::Call {
                argument_evaluation_order: None,
                callee: method,
                args: vec![receiver, packed_args],
                is_async: callable.is_async(),
            };
        }
        ExprKind::Call {
            argument_evaluation_order,
            callee,
            args,
            is_async,
        }
    }

    fn lower_call_args(
        &mut self,
        arguments: &[hir::ExpressionArgument],
        leading_args: &[ExprId],
    ) -> Vec<ExprId> {
        let mut args = Vec::with_capacity(arguments.len() + leading_args.len());
        args.extend_from_slice(leading_args);
        args.extend(arguments.iter().map(|arg| self.lower_expr(&arg.expression)));
        args
    }

    fn lower_call_args_with_defaults(
        &mut self,
        signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
        callee_generic_node: hir::NodeID,
        arguments: &[hir::ExpressionArgument],
        leading_args: &[ExprId],
        span: crate::span::Span,
    ) -> Option<(Vec<ExprId>, Option<Vec<usize>>)> {
        let generic_args = self.results.instantiation(callee_generic_node);
        let opening = generic_args.and_then(|arguments| {
            let source =
                self.results
                    .overload_source(callee_generic_node)
                    .or_else(
                        || match self.results.value_resolution(callee_generic_node) {
                            Some(Resolution::Definition(
                                id,
                                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
                            )) => Some(id),
                            _ => None,
                        },
                    )?;
            crate::sema::lowering::erased_opening::plan(self.gcx, source, arguments)
                .ok()
                .flatten()
                .map(|plan| (source, plan))
        });
        let signature = if let Some(args) = generic_args {
            instantiate_signature_with_args(self.gcx, signature, args)
        } else {
            signature.clone()
        };

        let param_offset = leading_args.len();
        let params = signature.inputs.get(param_offset..)?;
        let positions = match_arguments_to_parameters(
            params,
            signature.is_variadic,
            arguments
                .iter()
                .map(|arg| (arg.label.map(|label| label.identifier), arg.expression.span)),
            false,
        )
        .ok()?;
        let mut final_args =
            Vec::with_capacity(signature.inputs.len().max(arguments.len() + param_offset));
        final_args.extend_from_slice(leading_args);
        let supplied: Vec<_> = arguments
            .iter()
            .map(|argument| self.lower_expr(&argument.expression))
            .collect();
        let mut supplied_positions = vec![usize::MAX; arguments.len()];
        let mut defaults = Vec::new();
        let mut opened_default = false;

        for (param_idx, arg_indices) in positions.iter().enumerate() {
            let param = &signature.inputs[param_offset + param_idx];
            if !arg_indices.is_empty() {
                for &argument in arg_indices {
                    supplied_positions[argument] = final_args.len();
                    final_args.push(supplied[argument]);
                }
            } else if let Some(provider_id) = param.default_provider {
                if let Some((source, plan)) = opening {
                    let argument = if plan.input < param_offset {
                        leading_args[plan.input]
                    } else {
                        supplied[*positions.get(plan.input - param_offset)?.first()?]
                    };
                    let referent = if plan.borrow.is_some() {
                        self.push_expr(ExprKind::Deref(argument), plan.erased, span)
                    } else {
                        argument
                    };
                    let ty = Ty::new(TyKind::Reference(plan.erased), self.gcx);
                    let source_ref =
                        self.push_expr(ExprKind::Reference { expr: referent }, ty, span);
                    let helper = self.gcx.erased_default(source, provider_id, plan.parameter);
                    let signature = instantiate_signature_with_args(
                        self.gcx,
                        self.gcx.get_signature(helper),
                        generic_args?,
                    );
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: helper,
                            generic_args,
                        },
                        Ty::from_labeled_signature(self.gcx, &signature),
                        span,
                    );
                    let call = self.push_expr(
                        ExprKind::Call {
                            callee,
                            args: vec![source_ref],
                            is_async: false,
                            argument_evaluation_order: None,
                        },
                        param.ty,
                        span,
                    );
                    opened_default = true;
                    defaults.push(final_args.len());
                    final_args.push(call);
                    continue;
                }
                let inputs = self.gcx.store.interners.intern_ty_list(Vec::new());
                let provider_ty = self.gcx.store.interners.intern_ty(TyKind::FnPointer {
                    effects: Default::default(),
                    inputs,
                    output: param.ty,
                });
                let provider = self.push_expr(
                    ExprKind::Zst {
                        id: provider_id,
                        generic_args,
                    },
                    provider_ty,
                    span,
                );
                let call = self.push_expr(
                    ExprKind::Call {
                        argument_evaluation_order: None,
                        callee: provider,
                        args: vec![],
                        is_async: false,
                    },
                    param.ty,
                    span,
                );
                defaults.push(final_args.len());
                final_args.push(call);
            } else {
                let is_variadic_param = signature.is_variadic
                    && (param_offset + param_idx + 1 == signature.inputs.len());
                if is_variadic_param {
                    continue;
                }
                return None;
            }
        }

        let evaluation_order: Vec<_> = (0..leading_args.len())
            .chain(supplied_positions)
            .chain(defaults)
            .collect();
        debug_assert_eq!(evaluation_order.len(), final_args.len());
        let identity = evaluation_order.iter().copied().eq(0..final_args.len());
        Some((
            final_args,
            (!identity || opened_default).then_some(evaluation_order),
        ))
    }

    fn resolve_direct_callee_id(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        let hir::ExpressionKind::Path(path) = &callee.kind else {
            return None;
        };

        let resolution = if let Some(def_id) = self.results.overload_source(callee.id) {
            Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
        } else if let Some(resolution) = self.results.value_resolution(callee.id) {
            resolution
        } else {
            match path {
                hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                _ => Resolution::Error,
            }
        };

        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
            ) => Some(id),
            _ => None,
        }
    }

    fn lower_params(&mut self, node: &hir::Function) {
        let signature = self.gcx.get_signature(self.func.id);
        self.func.params = node
            .signature
            .prototype
            .inputs
            .iter()
            .zip(
                signature
                    .inputs
                    .iter()
                    .skip(usize::from(self.convenience.is_some())),
            )
            .map(|(param, lowered)| Param {
                id: param.id,
                name: param.name.symbol,
                ty: lowered.ty,
                span: param.span,
            })
            .collect();
    }

    fn lower_field_default(
        &mut self,
        provider: DefinitionID,
        args: GenericArguments<'ctx>,
        ty: Ty<'ctx>,
        span: crate::span::Span,
    ) -> ExprId {
        let signature =
            instantiate_signature_with_args(self.gcx, self.gcx.get_signature(provider), args);
        let callee = self.push_expr(
            ExprKind::Zst {
                id: provider,
                generic_args: Some(args),
            },
            Ty::from_labeled_signature(self.gcx, &signature),
            span,
        );
        self.push_expr(
            ExprKind::Call {
                callee,
                args: vec![],
                is_async: false,
                argument_evaluation_order: None,
            },
            ty,
            span,
        )
    }

    /// Source payload fields have flattened names but nested physical storage.
    /// Resolve that difference before MIR so ordinary field initialization,
    /// readonly checking and drop flags see the actual ownership tree.
    fn lower_source_field(
        &mut self,
        mut lhs: ExprId,
        index: usize,
        ty: Ty<'ctx>,
        span: crate::span::Span,
    ) -> ExprId {
        if let Some(class) = self.gcx.class_for_payload(self.func.exprs[lhs].ty) {
            for index in self
                .gcx
                .class_field_payload_path(class, index)
                .expect("payload field path")
            {
                let TyKind::Adt(def, args) = self.func.exprs[lhs].ty.kind() else {
                    unreachable!()
                };
                let field = self.gcx.get_struct_definition(def.id).fields[index as usize];
                let field_ty = instantiate_ty_with_args(self.gcx, field.ty, args);
                lhs = self.push_expr(
                    ExprKind::Field {
                        lhs,
                        index: FieldIndex::from_raw(index),
                    },
                    field_ty,
                    span,
                );
            }
            debug_assert_eq!(self.func.exprs[lhs].ty, ty);
            return lhs;
        }
        self.push_expr(
            ExprKind::Field {
                lhs,
                index: FieldIndex::from_usize(index),
            },
            ty,
            span,
        )
    }

    fn lower_self_initializer(
        &mut self,
        expr: &hir::Expression,
        receiver: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        propagate: bool,
    ) -> Expr<'ctx> {
        let (binding, context) = self.convenience.expect("self.init context");
        let source = self
            .results
            .overload_source(receiver.id)
            .or_else(|| self.results.overload_source(expr.id))
            .or_else(|| {
                self.results
                    .value_resolution(receiver.id)
                    .and_then(|resolution| resolution.definition_id())
            })
            .expect("resolved same-class initializer");
        let source_class = self.gcx.initializer_target(source);
        let entry = self
            .gcx
            .class_initializer(source_class, source)
            .expect("initializer entry");
        let helper = if entry.is_convenience {
            self.gcx
                .class_convenience_initializer(source)
                .expect("convenience helper")
        } else {
            self.gcx
                .class_initializer_dispatch(source)
                .expect("constructor dispatch helper")
        };
        let generic_args = self
            .results
            .instantiation(receiver.id)
            .or_else(|| self.results.instantiation(expr.id));
        let context_ty = self.gcx.get_signature(helper).inputs[0].ty;
        let context = self.push_expr(ExprKind::Local(context), context_ty, expr.span);
        let (mut args, evaluation) = self
            .lower_call_args_with_defaults(
                self.gcx.get_signature(source),
                receiver.id,
                arguments,
                &[],
                expr.span,
            )
            .expect("convenience delegation arguments");
        args.insert(0, context);
        let evaluation = evaluation.map(|order| {
            std::iter::once(0)
                .chain(order.into_iter().map(|index| index + 1))
                .collect()
        });
        let callee = self.push_expr(
            ExprKind::Zst {
                id: helper,
                generic_args,
            },
            self.gcx.get_type(helper),
            expr.span,
        );
        let result_ty = instantiate_ty_with_args(
            self.gcx,
            self.gcx.get_signature(helper).output,
            generic_args.unwrap_or(GenericArguments::empty()),
        );
        let value = self.push_expr(
            ExprKind::Call {
                callee,
                args,
                is_async: false,
                argument_evaluation_order: evaluation,
            },
            result_ty,
            expr.span,
        );
        let value = if propagate {
            self.propagate_initializer(value, expr.span)
        } else {
            value
        };
        let output = if propagate {
            self.gcx.types.void
        } else {
            self.results.node_type(expr.id)
        };
        let mapped = self.map_initializer_success(value, output, expr.span, |this, value| {
            let target = this.push_expr(
                ExprKind::Local(binding),
                this.gcx.initializer_target(this.func.id),
                expr.span,
            );
            this.push_expr(
                ExprKind::Assign { target, value },
                this.gcx.types.void,
                expr.span,
            )
        });
        self.func.exprs[mapped].clone()
    }

    fn lower_base_initializer(
        &mut self,
        expr: &hir::Expression,
        receiver: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
        propagate: bool,
    ) -> Expr<'ctx> {
        let source = self
            .results
            .overload_source(receiver.id)
            .or_else(|| self.results.overload_source(expr.id))
            .or_else(|| {
                self.results
                    .value_resolution(receiver.id)
                    .and_then(|resolution| resolution.definition_id())
            })
            .expect("resolved superclass initializer");
        let helper = self
            .gcx
            .class_payload_initializer(source)
            .expect("base payload initializer");
        let generic_args = self
            .results
            .instantiation(receiver.id)
            .or_else(|| self.results.instantiation(expr.id));
        let payload = instantiate_ty_with_args(
            self.gcx,
            self.gcx.get_signature(helper).output,
            generic_args.unwrap_or(GenericArguments::empty()),
        );
        let (args, argument_evaluation_order) = self
            .lower_call_args_with_defaults(
                self.gcx.get_signature(source),
                receiver.id,
                arguments,
                &[],
                expr.span,
            )
            .expect("base constructor arguments");
        let callee = self.push_expr(
            ExprKind::Zst {
                id: helper,
                generic_args,
            },
            self.gcx.get_type(helper),
            expr.span,
        );
        let value = self.push_expr(
            ExprKind::Call {
                callee,
                args,
                is_async: false,
                argument_evaluation_order,
            },
            payload,
            expr.span,
        );
        let value = if propagate {
            self.propagate_initializer(value, expr.span)
        } else {
            value
        };
        let output = if propagate {
            self.gcx.types.void
        } else {
            self.results.node_type(expr.id)
        };
        let mapped = self.map_initializer_success(value, output, expr.span, |this, value| {
            let payload = this.func.exprs[value].ty;
            let owner_ty = this.gcx.initializer_target(this.func.id);
            let owner = this.push_expr(
                ExprKind::Local(this.func.constructor_self.expect("construction storage")),
                owner_ty,
                expr.span,
            );
            let target = this.push_expr(
                ExprKind::Field {
                    lhs: owner,
                    index: FieldIndex::from_raw(0),
                },
                payload,
                expr.span,
            );
            let assignment = this.push_expr(
                ExprKind::Assign { target, value },
                this.gcx.types.void,
                expr.span,
            );
            let statement = this.push_stmt(Stmt {
                kind: StmtKind::Expr(assignment),
                span: expr.span,
            });
            let mut stmts = vec![statement];
            stmts.extend(this.constructor_default_statements());
            let block = this.func.blocks.push(Block {
                id: BlockId::from_usize(this.func.blocks.len()),
                stmts,
                expr: None,
            });
            this.push_expr(ExprKind::Block(block), this.gcx.types.void, expr.span)
        });
        self.func.exprs[mapped].clone()
    }

    fn lower_constructor_defaults(&mut self) {
        let defaults = self.constructor_default_statements();
        let body = self.func.body.expect("initializer body");
        self.func.blocks[body].stmts.splice(1..1, defaults);
    }

    fn constructor_default_statements(&mut self) -> Vec<StmtId> {
        self.constructor_default_parts(false).1
    }

    fn constructor_default_parts(&mut self, stage: bool) -> (Vec<StmtId>, Vec<StmtId>) {
        let Some(binding) = self.func.constructor_self else {
            return (vec![], vec![]);
        };
        let ty = self
            .gcx
            .constructor_value(self.gcx.get_signature(self.func.id).output);
        let TyKind::Adt(def, args) = ty.kind() else {
            return (vec![], vec![]);
        };
        let fields = self.gcx.get_struct_definition(def.id).fields;
        let mut early = vec![];
        let mut defaults = vec![];
        for (index, field) in fields.iter().enumerate() {
            let Some(provider) = field.default_provider else {
                continue;
            };
            let span = self.gcx.definition_ident(field.def_id).span;
            let field_ty = instantiate_ty_with_args(self.gcx, field.ty, args);
            let value = self.lower_field_default(provider, args, field_ty, span);
            let value = if stage {
                let id = self.fresh_synthetic_local();
                let declaration = self.push_stmt(Stmt {
                    kind: StmtKind::Let {
                        id,
                        pattern: thir::Pattern {
                            ty: field_ty,
                            span,
                            kind: thir::PatternKind::Binding {
                                name: self.gcx.intern_symbol("$decoded_default"),
                                local: id,
                                ty: field_ty,
                            },
                        },
                        expr: Some(value),
                        ty: field_ty,
                        mutable: false,
                    },
                    span,
                });
                early.push(declaration);
                self.push_expr(ExprKind::Local(id), field_ty, span)
            } else {
                value
            };
            let owner = self.push_expr(ExprKind::Local(binding), ty, span);
            let target = self.push_expr(
                ExprKind::Field {
                    lhs: owner,
                    index: FieldIndex::from_usize(index),
                },
                field_ty,
                span,
            );
            let assignment = self.push_expr(
                ExprKind::Assign { target, value },
                self.gcx.types.void,
                span,
            );
            defaults.push(self.push_stmt(Stmt {
                kind: StmtKind::Expr(assignment),
                span,
            }));
        }
        (early, defaults)
    }
    fn lower_body(&mut self, node: &hir::Function) {
        if let Some(block) = &node.block {
            let block_id = self.lower_block(block);
            self.func.body = Some(block_id);
        }
    }

    fn lower_block(&mut self, block: &hir::Block) -> BlockId {
        let id = BlockId::from_raw(self.func.blocks.len() as u32);
        self.func.blocks.push(Block {
            id,
            stmts: vec![],
            expr: None,
        });

        let stmts: Vec<_> = block
            .statements
            .iter()
            .filter_map(|stmt| self.lower_statement(stmt).map(|s| self.push_stmt(s)))
            .collect();
        let expr = block.tail.as_deref().map(|expr| self.lower_expr(expr));

        self.func.blocks[id].stmts = stmts;
        self.func.blocks[id].expr = expr;
        id
    }

    fn lower_statement(&mut self, stmt: &hir::Statement) -> Option<Stmt<'ctx>> {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => None,
            hir::StatementKind::Expression(expr) => {
                let expr_id = self.lower_expr(expr);
                Some(Stmt {
                    kind: StmtKind::Expr(expr_id),
                    span: stmt.span,
                })
            }
            hir::StatementKind::Variable(local) => Some(self.lower_local(local)),
            hir::StatementKind::Loop { block, .. } => {
                let block_id = self.lower_block(block);
                Some(Stmt {
                    kind: StmtKind::Loop { block: block_id },
                    span: stmt.span,
                })
            }
            hir::StatementKind::Defer(block) => {
                let block_id = self.lower_block(block);
                Some(Stmt {
                    kind: StmtKind::Defer(block_id),
                    span: stmt.span,
                })
            }
            hir::StatementKind::Guard {
                condition,
                else_block,
            } => {
                let cond = self.lower_expr(condition);
                let else_block_id = self.lower_block(else_block);

                Some(Stmt {
                    kind: StmtKind::Guard {
                        condition: cond,
                        else_block: else_block_id,
                    },
                    span: stmt.span,
                })
            }
        }
    }

    fn lower_local(&mut self, local: &hir::Local) -> Stmt<'ctx> {
        let ty = self.results.node_type(local.id);
        let pattern = pattern_from_hir(self.gcx, self.results.as_ref(), &local.pattern);
        let expr = local
            .initializer
            .as_deref()
            .map(|expr| self.lower_expr(expr));
        Stmt {
            kind: StmtKind::Let {
                id: local.id,
                pattern,
                expr,
                ty,
                mutable: local.mutability == hir::Mutability::Mutable,
            },
            span: local.pattern.span,
        }
    }

    pub fn lower_expr(&mut self, expr: &hir::Expression) -> ExprId {
        self.lower_expr_inner(expr)
    }

    fn lower_expr_inner(&mut self, expr: &hir::Expression) -> ExprId {
        let mut thir_expr = self.lower_expr_unadjusted(expr);
        // Apply adjustments if any
        if let Some(adjustments) = self
            .results
            .node_adjustments(expr.id)
            .map(|adj| adj.to_vec())
        {
            for adjustment in adjustments {
                thir_expr = self.apply_adjustment(expr.id, thir_expr, adjustment, expr.span);
            }
        }
        self.push_expr(thir_expr.kind, thir_expr.ty, thir_expr.span)
    }

    fn apply_adjustment(
        &mut self,
        _hir_id: hir::NodeID,
        expr: Expr<'ctx>,
        adjustment: Adjustment<'ctx>,
        span: crate::span::Span,
    ) -> Expr<'ctx> {
        let ty = expr.ty;
        match adjustment {
            Adjustment::Dereference => {
                let inner = match ty.kind() {
                    TyKind::Reference(inner) | TyKind::Pointer(inner, _) => inner,
                    // Logic error if we try to deref non-derefable type.
                    _ => return expr,
                };

                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Deref(inner_id),
                    ty: inner,
                    span,
                }
            }
            Adjustment::DerefCall {
                method,
                arguments,
                result,
            } => {
                let receiver = self.push_expr(expr.kind, expr.ty, expr.span);
                let callee = self.push_expr(
                    ExprKind::Zst {
                        id: method,
                        generic_args: Some(arguments),
                    },
                    self.gcx.get_type(method),
                    span,
                );
                Expr {
                    kind: ExprKind::Call {
                        callee,
                        args: vec![receiver],
                        argument_evaluation_order: None,
                        is_async: false,
                    },
                    ty: result,
                    span,
                }
            }
            Adjustment::ClassUpcast { to } => {
                let value = self.push_expr(expr.kind, expr.ty, expr.span);
                Expr {
                    kind: ExprKind::ClassUpcast { value },
                    ty: to,
                    span,
                }
            }
            Adjustment::PointerToConst => {
                let TyKind::Pointer(inner, _) = ty.kind() else {
                    panic!("raw pointer permission adjustment requires a pointer");
                };
                let value = self.push_expr(expr.kind, expr.ty, expr.span);
                Expr {
                    kind: ExprKind::Cast { value },
                    ty: Ty::new(TyKind::Pointer(inner, Mutability::Immutable), self.gcx),
                    span,
                }
            }
            Adjustment::NullPointer { to } => Expr {
                kind: ExprKind::Literal(Constant {
                    ty: to,
                    value: ConstantKind::Unit,
                }),
                ty: to,
                span,
            },
            Adjustment::Reference => {
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);
                Expr {
                    kind: ExprKind::Reference { expr: inner_id },
                    ty: Ty::new(TyKind::Reference(ty), self.gcx),
                    span,
                }
            }
            Adjustment::BoxExistential { .. } => {
                let Adjustment::BoxExistential { interfaces, .. } = adjustment else {
                    unreachable!()
                };
                let boxed_ty = Ty::new(TyKind::BoxedExistential { interfaces }, self.gcx);
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::BoxExistential {
                        value: inner_id,
                        interfaces,
                    },
                    ty: boxed_ty,
                    span,
                }
            }
            Adjustment::ExistentialUpcast { .. } => {
                let Adjustment::ExistentialUpcast { to, .. } = adjustment else {
                    unreachable!()
                };
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::ExistentialUpcast {
                        value: inner_id,
                        to,
                    },
                    ty: to,
                    span,
                }
            }
            Adjustment::OptionalWrap {
                is_some,
                generic_args,
            } => {
                let opt_id = self
                    .gcx
                    .std_item_def(hir::StdItem::Optional)
                    .expect("Optional type must exist");
                let enum_def = self.gcx.get_enum_definition(opt_id);
                let adt_def = enum_def.adt_def;

                let (variant_index, fields) = if is_some {
                    let some_idx = enum_def
                        .variants
                        .iter()
                        .position(|v| self.gcx.symbol_eq(v.name, "some"))
                        .expect("Optional.some variant");
                    let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);
                    (
                        some_idx,
                        vec![thir::FieldExpression {
                            index: FieldIndex::from_usize(0),
                            expression: inner_id,
                        }],
                    )
                } else {
                    let none_idx = enum_def
                        .variants
                        .iter()
                        .position(|v| self.gcx.symbol_eq(v.name, "none"))
                        .expect("Optional.none variant");
                    (none_idx, vec![])
                };

                let opt_ty = Ty::new(TyKind::Adt(adt_def, generic_args), self.gcx);
                Expr {
                    kind: ExprKind::Adt(thir::AdtExpression {
                        base: None,
                        definition: adt_def,
                        variant_index: Some(VariantIndex::from_usize(variant_index)),
                        generic_args,
                        fields,
                    }),
                    ty: opt_ty,
                    span,
                }
            }
            Adjustment::ResultOkWrap { generic_args } => {
                let result_id = self
                    .gcx
                    .std_item_def(hir::StdItem::Result)
                    .expect("Result type must exist");
                let definition = self.gcx.get_enum_definition(result_id);
                let variant_index = definition
                    .variants
                    .iter()
                    .position(|variant| self.gcx.symbol_eq(variant.name, "ok"))
                    .expect("Result.ok variant");
                let value = self.push_expr(expr.kind, expr.ty, expr.span);
                Expr {
                    kind: ExprKind::Adt(thir::AdtExpression {
                        base: None,
                        definition: definition.adt_def,
                        variant_index: Some(VariantIndex::from_usize(variant_index)),
                        generic_args,
                        fields: vec![thir::FieldExpression {
                            index: FieldIndex::from_usize(0),
                            expression: value,
                        }],
                    }),
                    ty: Ty::new(TyKind::Adt(definition.adt_def, generic_args), self.gcx),
                    span,
                }
            }
            Adjustment::Ignore(_) => expr,
            Adjustment::ClosureToFnPointer { closure_def_id } => {
                // Get the fn pointer type from the target type (set by type inference)
                // The closure expression is converted to a ClosureToFnPointer expression
                let closure_expr_id = self.push_expr(expr.kind, expr.ty, expr.span);

                // The result type should be the function pointer type.
                // Since this adjustment is only applied when coercing closure -> fn pointer,
                // the expected type from the coercion context provides the fn pointer type.
                // For now, we derive it from the closure's signature.
                let fn_ptr_ty = match expr.ty.kind() {
                    TyKind::Closure { inputs, output, .. } => Ty::new(
                        TyKind::FnPointer {
                            inputs,
                            output,
                            effects: Default::default(),
                        },
                        self.gcx,
                    ),
                    _ => expr.ty, // fallback, shouldn't happen
                };

                Expr {
                    kind: ExprKind::ClosureToFnPointer {
                        closure: closure_expr_id,
                        closure_def_id,
                    },
                    ty: fn_ptr_ty,
                    span,
                }
            }
        }
    }

    fn lower_expr_unadjusted(&mut self, expr: &hir::Expression) -> Expr<'ctx> {
        let ty = self.results.node_type(expr.id);
        let span = expr.span;
        if let Some((root, fields)) = self.capture_place(expr)
            && let Some(capture) = self.captures_map.as_ref().and_then(|captures| {
                captures.iter().find(|capture| {
                    capture.source_id == root
                        && capture.projection.len() == fields.len()
                        && capture
                            .projection
                            .iter()
                            .zip(&fields)
                            .all(|(projection, field)| projection.field == *field)
                })
            })
        {
            return Expr {
                kind: ExprKind::Upvar {
                    field_index: capture.field_index,
                    capture_kind: capture.capture_kind,
                },
                ty,
                span,
            };
        }
        if matches!(expr.kind, hir::ExpressionKind::Call { .. })
            && let Some(selected) = self.results.elaborated_method_calls.get(&expr.id).cloned()
        {
            return self.lower_expr_unadjusted(&selected);
        }
        let kind = match &expr.kind {
            hir::ExpressionKind::MemberBrackets { .. } => {
                let selected = self
                    .results
                    .selected_brackets
                    .get(&expr.id)
                    .cloned()
                    .expect("checked member bracket branch");
                return self.lower_expr_unadjusted(&selected);
            }
            hir::ExpressionKind::Index {
                target,
                index,
                nodes,
            } => {
                let info = self
                    .results
                    .native_indices
                    .get(&expr.id)
                    .copied()
                    .expect("checked native subscript");
                let receiver = self.lower_native_index_receiver(target, nodes.receiver);
                let mut args = vec![receiver];
                args.extend(
                    index
                        .iter()
                        .map(|argument| self.lower_expr(&argument.expression)),
                );
                let accessor = if info.use_address {
                    info.address.expect("validated address accessor")
                } else {
                    info.getter
                };
                let call = self.native_index_call(accessor, args, span);
                if info.use_address {
                    let reference = Ty::new(TyKind::Reference(ty), self.gcx);
                    let call = self.push_expr(call, reference, span);
                    ExprKind::Deref(call)
                } else {
                    call
                }
            }

            hir::ExpressionKind::Literal(lit) => {
                if let hir::Literal::Integer { value, .. } = lit
                    && *value < 0
                    && matches!(ty.kind(), TyKind::UInt(_))
                {
                    let operand = self.push_expr(
                        ExprKind::Literal(Constant {
                            ty,
                            value: ConstantKind::Integer((-*value) as u64),
                        }),
                        ty,
                        span,
                    );
                    return Expr {
                        kind: ExprKind::Unary {
                            op: mir::UnaryOperator::Negate,
                            operand,
                        },
                        ty,
                        span,
                    };
                }
                let value = self.lower_literal(lit);
                ExprKind::Literal(Constant { ty, value })
            }
            hir::ExpressionKind::Array(items) => {
                let elements: Vec<_> = items.iter().map(|e| self.lower_expr(e)).collect();
                let list_def_id = self.gcx.std_item_def(hir::StdItem::List);
                if let TyKind::Adt(def, args) = ty.kind()
                    && Some(def.id) == list_def_id
                {
                    let element_ty = match args.get(0) {
                        Some(GenericArgument::Type(elem)) => *elem,
                        _ => self.gcx.types.error,
                    };
                    ExprKind::ListLiteral {
                        elements,
                        element_ty,
                    }
                } else {
                    ExprKind::Array { elements }
                }
            }
            hir::ExpressionKind::Repeat { value, count: _ } => {
                let element = self.lower_expr(value);
                let count = match ty.kind() {
                    TyKind::Array { len, .. } => match len.kind {
                        ConstKind::Value(ConstValue::Integer(i)) => {
                            debug_assert!(
                                i >= 0,
                                "repeat count should be validated during typechecking"
                            );
                            usize::try_from(i).unwrap_or(0)
                        }
                        _ => {
                            debug_assert!(
                                false,
                                "repeat count should be a concrete integer const after typechecking"
                            );
                            0
                        }
                    },
                    _ => {
                        debug_assert!(
                            false,
                            "repeat expressions should typecheck to array types before THIR lowering"
                        );
                        0
                    }
                };
                ExprKind::Repeat { element, count }
            }
            hir::ExpressionKind::Path(path) => {
                let res = if let Some(def_id) = self.results.overload_source(expr.id) {
                    Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
                } else if let Some(resolution) = self.results.value_resolution(expr.id) {
                    resolution
                } else {
                    match path {
                        hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                        hir::ResolvedPath::Relative(..) => {
                            self.gcx.dcx().emit_error(
                                "unresolved relative path (typecheck should have resolved this)"
                                    .into(),
                                Some(expr.span),
                            );
                            Resolution::Error
                        }
                    }
                };
                self.lower_path_expression(expr, res)
            }
            hir::ExpressionKind::InferredMember { .. } => {
                let res = if let Some(def_id) = self.results.overload_source(expr.id) {
                    Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
                } else if let Some(resolution) = self.results.value_resolution(expr.id) {
                    resolution
                } else {
                    self.gcx.dcx().emit_error(
                        "unresolved inferred member (typecheck should have resolved this)".into(),
                        Some(expr.span),
                    );
                    Resolution::Error
                };
                self.lower_path_expression(expr, res)
            }
            hir::ExpressionKind::Call { callee, arguments } => {
                if self.results.dynamic_self_calls.contains(&expr.id) {
                    return self.lower_dynamic_self_call(expr, callee, arguments);
                }
                if let Some(ctor_id) = self.variant_ctor_callee(callee) {
                    let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                    let TyKind::Adt(_, generic_args) = ty.kind() else {
                        self.gcx
                            .dcx()
                            .emit_info(format!("Type is {}", ty.format(self.gcx)), Some(expr.span));
                        unreachable!()
                    };
                    // Labels select storage positions, but expressions must still
                    // evaluate in source order. Reordering the expression vector
                    // would reorder observable argument side effects.
                    let signature = self.gcx.get_signature(ctor_id);
                    let positions = match_arguments_to_parameters(
                        &signature.inputs,
                        false,
                        arguments.iter().map(|arg| {
                            (arg.label.map(|label| label.identifier), arg.expression.span)
                        }),
                        false,
                    )
                    .expect("typechecked enum constructor arguments");
                    let mut field_indices = vec![0; arguments.len()];
                    for (field_index, argument_indices) in positions.iter().enumerate() {
                        for &argument_index in argument_indices {
                            field_indices[argument_index] = field_index;
                        }
                    }
                    let fields = arguments
                        .iter()
                        .enumerate()
                        .map(|(argument_index, arg)| thir::FieldExpression {
                            index: FieldIndex::from_usize(field_indices[argument_index]),
                            expression: self.lower_expr(&arg.expression),
                        })
                        .collect();
                    return Expr {
                        kind: ExprKind::Adt(thir::AdtExpression {
                            base: None,
                            definition,
                            variant_index: Some(variant_index),
                            generic_args,
                            fields,
                        }),
                        ty,
                        span,
                    };
                }

                // Normal function call
                let thir_callee = self.lower_expr(callee);
                let (final_args, argument_evaluation_order) =
                    if let Some(def_id) = self.resolve_direct_callee_id(callee) {
                        let signature = self.gcx.get_signature(def_id);
                        self.lower_call_args_with_defaults(
                            signature,
                            callee.id,
                            arguments,
                            &[],
                            expr.span,
                        )
                        .unwrap_or_else(|| {
                            debug_assert!(
                                false,
                                "failed to match direct call arguments for default values"
                            );
                            (self.lower_call_args(arguments, &[]), None)
                        })
                    } else {
                        // Indirect call - just lower args as provided (no defaults).
                        (self.lower_call_args(arguments, &[]), None)
                    };

                self.lower_indirect_call(
                    thir_callee,
                    final_args,
                    argument_evaluation_order,
                    self.results.is_async_call(expr.id),
                    span,
                )
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                // Check if this is an operator method call
                if let Some(def_id) = self.results.overload_source(expr.id) {
                    // Lower as a method call
                    let lhs_expr = self.lower_expr(lhs);
                    let rhs_expr = self.lower_expr(rhs);
                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        argument_evaluation_order: None,
                        callee,
                        args: vec![lhs_expr, rhs_expr],
                        is_async: false,
                    }
                } else {
                    match op {
                        hir::BinaryOperator::IdentityEql | hir::BinaryOperator::IdentityNeq => {
                            ExprKind::ClassIdentity {
                                lhs: self.lower_expr(lhs),
                                rhs: self.lower_expr(rhs),
                                equal: *op == hir::BinaryOperator::IdentityEql,
                            }
                        }
                        hir::BinaryOperator::BoolAnd => ExprKind::Logical {
                            op: LogicalOperator::And,
                            lhs: self.lower_expr(lhs),
                            rhs: self.lower_expr(rhs),
                        },
                        hir::BinaryOperator::BoolOr => ExprKind::Logical {
                            op: LogicalOperator::Or,
                            lhs: self.lower_expr(lhs),
                            rhs: self.lower_expr(rhs),
                        },
                        _ => {
                            let lhs = self.lower_expr(lhs);
                            let rhs = self.lower_expr(rhs);
                            let op = bin_op(*op);
                            ExprKind::Binary { op, lhs, rhs }
                        }
                    }
                }
            }
            hir::ExpressionKind::Unary(unary_op, operand) => {
                // Check if this is an operator method call
                if let Some(def_id) = self.results.overload_source(expr.id) {
                    // Lower as a method call
                    let operand_expr = self.lower_expr(operand);
                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        argument_evaluation_order: None,
                        callee,
                        args: vec![operand_expr],
                        is_async: false,
                    }
                } else {
                    let operand = self.lower_expr(operand);
                    let op = match unary_op {
                        hir::UnaryOperator::LogicalNot => mir::UnaryOperator::LogicalNot,
                        hir::UnaryOperator::Negate => mir::UnaryOperator::Negate,
                        hir::UnaryOperator::BitwiseNot => mir::UnaryOperator::BitwiseNot,
                    };
                    ExprKind::Unary { op, operand }
                }
            }
            hir::ExpressionKind::CastAs(value, _) => {
                let value = self.lower_expr(value);
                ExprKind::Cast { value }
            }
            hir::ExpressionKind::CastAsTry(value, target) => {
                let value = self.lower_expr(value);
                let lowerer = DefTyLoweringCtx::new(self.func.id, self.gcx);
                let target = lowerer.lowerer().lower_type(target);
                ExprKind::ExistentialTryCast { value, target }
            }
            hir::ExpressionKind::TypeIs(value, target) => {
                let value = self.lower_expr(value);
                let lowerer = DefTyLoweringCtx::new(self.func.id, self.gcx);
                let target = lowerer.lowerer().lower_type(target);
                ExprKind::ExistentialTypeIs { value, target }
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                let results = self.results.clone();
                let lhs = results.selected_brackets.get(&lhs.id).unwrap_or(lhs);
                if let Some(entry) = self.native_index_info(lhs) {
                    self.lower_native_index_set(
                        lhs,
                        rhs,
                        entry.setter.expect("validated set accessor"),
                    )
                } else {
                    let target = self.lower_expr(lhs);
                    let value = self.lower_expr(rhs);
                    ExprKind::Assign { target, value }
                }
            }
            hir::ExpressionKind::AssignOp(op, lhs, rhs) => {
                let results = self.results.clone();
                let lhs = results.selected_brackets.get(&lhs.id).unwrap_or(lhs);
                if self.results.overload_source(expr.id).is_none()
                    && let Some(entry) = self.native_index_info(lhs)
                    && entry.address.is_none()
                {
                    self.lower_native_index_compound(
                        expr,
                        *op,
                        lhs,
                        rhs,
                        entry.getter,
                        entry.setter.expect("validated set accessor"),
                    )
                } else if let Some(def_id) = self.results.overload_source(expr.id) {
                    // Lower as a method call
                    let lhs_expr = self.lower_expr(lhs);
                    let rhs_expr = self.lower_expr(rhs);
                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        // Evaluate RHS before the receiver and pass each
                        // operand once with its declared value semantics.
                        argument_evaluation_order: Some(vec![1, 0]),
                        callee,
                        args: vec![lhs_expr, rhs_expr],
                        is_async: false,
                    }
                } else {
                    // Intrinsic compound assignment
                    let target = self.lower_expr(lhs);
                    let value = self.lower_expr(rhs);
                    let op = bin_op(*op);
                    ExprKind::AssignOp { op, target, value }
                }
            }
            hir::ExpressionKind::If(node) => {
                let cond = self.lower_expr(&node.condition);
                let then_expr = self.lower_expr(&node.then_block);
                let else_expr = node.else_block.as_deref().map(|expr| self.lower_expr(expr));
                ExprKind::If {
                    cond,
                    then_expr,
                    else_expr,
                }
            }
            hir::ExpressionKind::Match(node) => {
                let scrutinee = self.lower_expr(&node.value);
                let arms = node
                    .arms
                    .iter()
                    .map(|arm| self.lower_match_arm(arm))
                    .collect();
                ExprKind::Match {
                    scrutinee,
                    arms,
                    binding_condition: false,
                }
            }
            hir::ExpressionKind::Return { value } => {
                let value = value
                    .as_deref()
                    .map(|expr| self.lower_expr(expr))
                    .or_else(|| {
                        self.convenience.map(|(binding, _)| {
                            if self
                                .gcx
                                .result_parts(self.gcx.get_signature(self.func.id).output)
                                .is_some()
                            {
                                return self.initializer_ok(expr.span);
                            }
                            self.push_expr(
                                ExprKind::Local(binding),
                                self.gcx.initializer_target(self.func.id),
                                expr.span,
                            )
                        })
                    });
                let value = value.or_else(|| {
                    (self.func.constructor_self.is_some()
                        && self
                            .gcx
                            .result_parts(self.gcx.get_signature(self.func.id).output)
                            .is_some())
                    .then(|| self.initializer_ok(expr.span))
                });
                ExprKind::Return { value }
            }
            hir::ExpressionKind::Break { .. } => ExprKind::Break,
            hir::ExpressionKind::Continue { .. } => ExprKind::Continue,
            hir::ExpressionKind::Block(block) => {
                let block_id = self.lower_block(block);
                ExprKind::Block(block_id)
            }
            hir::ExpressionKind::UnsafeBlock(block) => {
                let block_id = self.lower_block(block);
                ExprKind::Block(block_id)
            }
            hir::ExpressionKind::Propagate(inner) => {
                return self.lower_propagate_expr(expr, inner);
            }
            hir::ExpressionKind::Dereference(inner) => {
                let operand = self.lower_expr(inner);
                ExprKind::Deref(operand)
            }
            hir::ExpressionKind::Reference(inner) => {
                let operand = self.lower_expr(inner);
                ExprKind::Reference { expr: operand }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                name: _,
                arguments,
            } => {
                if self.results.self_initializer_calls.contains(&expr.id) {
                    return self.lower_self_initializer(expr, receiver, arguments, false);
                }
                if self.results.base_initializer_calls.contains(&expr.id) {
                    return self.lower_base_initializer(expr, receiver, arguments, false);
                }
                if let Some(def_id) = self.results.overload_source(expr.id) {
                    let recv = self.lower_expr(receiver);
                    let receiver_args = [recv];
                    let signature = self.gcx.get_signature(def_id);
                    let (final_args, argument_evaluation_order) = self
                        .lower_call_args_with_defaults(
                            signature,
                            expr.id,
                            arguments,
                            &receiver_args,
                            expr.span,
                        )
                        .unwrap_or_else(|| {
                            debug_assert!(
                                false,
                                "failed to match method call arguments for default values"
                            );
                            (self.lower_call_args(arguments, &receiver_args), None)
                        });

                    let callee_ty = self.gcx.get_type(def_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: def_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        argument_evaluation_order,
                        callee,
                        args: final_args,
                        is_async: self.results.is_async_call(expr.id),
                    }
                } else if let Some(field_index) = self.results.field_index(expr.id) {
                    // Callable-field fallback from method resolution:
                    // lower `receiver.f(args)` as `(receiver.f)(args)`.
                    let recv = self.lower_expr(receiver);
                    let recv_ty = self.func.exprs[recv].ty;

                    let callee_ty = match recv_ty.kind() {
                        TyKind::Adt(..) => {
                            let struct_def = self
                                .gcx
                                .source_struct_definition(recv_ty)
                                .expect("callable source field");
                            struct_def
                                .fields
                                .get(field_index)
                                .map(|field| field.ty)
                                .unwrap_or(self.gcx.types.error)
                        }
                        _ => self.gcx.types.error,
                    };

                    let callee = self.lower_source_field(recv, field_index, callee_ty, expr.span);

                    let final_args = self.lower_call_args(arguments, &[]);
                    self.lower_indirect_call(
                        callee,
                        final_args,
                        None,
                        self.results.is_async_call(expr.id),
                        span,
                    )
                } else {
                    self.gcx.dcx().emit_error(
                        "failed to lower method call (no resolved target)".into(),
                        Some(expr.span),
                    );
                    return Expr {
                        kind: ExprKind::Literal(Constant {
                            ty: self.gcx.types.error,
                            value: ConstantKind::Unit,
                        }),
                        ty: self.gcx.types.error,
                        span: expr.span,
                    };
                }
            }

            hir::ExpressionKind::StructLiteral(literal) => {
                let TyKind::Adt(definition, generic_args) = ty.kind() else {
                    unreachable!()
                };

                let constructor = self
                    .results
                    .value_resolution(expr.id)
                    .and_then(|resolution| match resolution {
                        hir::Resolution::Definition(
                            id,
                            crate::sema::resolve::models::DefinitionKind::VariantConstructor(..),
                        ) => Some(id),
                        _ => None,
                    });

                // Resolve each entry's slot by field name against the struct
                // definition. The tycheck `field_index` table is keyed by the
                // value expression's NodeID, which collides with the member
                // access index when the value is itself a field read (e.g.
                // `Pair { a: input.b }` would resolve to slot `b`).
                let declared = crate::sema::tycheck::utils::named_fields::named_fields(
                    self.gcx,
                    ty,
                    constructor,
                )
                .expect("checked named literal fields");
                let mut node = thir::AdtExpression {
                    base: literal.base.as_ref().map(|base| self.lower_expr(base)),
                    definition,
                    variant_index: declared.variant_index.map(VariantIndex::from_usize),
                    generic_args,
                    fields: literal
                        .fields
                        .iter()
                        .map(|f| {
                            let name = match &f.label {
                                Some(label) => label.identifier.symbol,
                                None => match &f.expression.kind {
                                    hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(
                                        path,
                                    )) => {
                                        path.segments
                                            .last()
                                            .expect("path must have segments")
                                            .identifier
                                            .symbol
                                    }
                                    _ => unreachable!(),
                                },
                            };
                            let index = declared
                                .fields
                                .iter()
                                .position(|field| field.name == name)
                                .expect("struct literal field must match a declared field");
                            let expression = self.lower_expr(&f.expression);
                            thir::FieldExpression {
                                expression,
                                index: FieldIndex::from_usize(index),
                            }
                        })
                        .collect(),
                };

                for (index, field) in declared.fields.iter().enumerate() {
                    if node.base.is_none()
                        && let Some(provider) = field.default_provider
                        && !node
                            .fields
                            .iter()
                            .any(|provided| provided.index.index() == index)
                    {
                        let field_ty = field.ty;
                        let expression =
                            self.lower_field_default(provider, generic_args, field_ty, span);
                        node.fields.push(thir::FieldExpression {
                            index: FieldIndex::from_usize(index),
                            expression,
                        });
                    }
                }
                ExprKind::Adt(node)
            }
            hir::ExpressionKind::Member { target, .. } => {
                if let Some(method) = self.results.bound_method(expr.id).cloned() {
                    let info = self
                        .gcx
                        .get_closure_captures(method.closure.def_id)
                        .expect("bound receiver capture");
                    assert_eq!(
                        info.captures.len(),
                        1,
                        "method values capture only their receiver"
                    );
                    let capture = info.captures[0];
                    let capture_expr = self.lower_expr(&method.receiver);
                    let function = self.lower_closure_body(&method.closure);
                    self.nested_closures.push(function);
                    ExprKind::Closure {
                        def_id: method.closure.def_id,
                        kind: info.kind,
                        captures: vec![ClosureCapture {
                            source_id: capture.source_id,
                            capture_expr,
                            capture_kind: capture.capture_kind,
                            field_index: capture.field_index,
                        }],
                    }
                } else if let Some(property) = self.results.property_read(expr.id) {
                    let receiver = self.lower_expr(target);
                    let callee_ty = self.gcx.get_type(property.getter_id);
                    let generic_args = self.results.instantiation(expr.id);
                    let callee = self.push_expr(
                        ExprKind::Zst {
                            id: property.getter_id,
                            generic_args,
                        },
                        callee_ty,
                        expr.span,
                    );
                    ExprKind::Call {
                        argument_evaluation_order: None,
                        callee,
                        args: vec![receiver],
                        is_async: self.results.is_async_call(expr.id),
                    }
                } else {
                    let lhs = self.lower_expr(target);
                    let field = self.lower_source_field(
                        lhs,
                        self.results.field_index(expr.id).expect("Field Index"),
                        ty,
                        span,
                    );
                    return self.func.exprs[field].clone();
                }
            }
            hir::ExpressionKind::Tuple(elems) => {
                let fields = elems.iter().map(|e| self.lower_expr(&e)).collect();
                ExprKind::Tuple { fields }
            }
            hir::ExpressionKind::TupleAccess(target, ..) => {
                let lhs = self.lower_expr(target);
                ExprKind::Field {
                    lhs,
                    index: FieldIndex::from_usize(
                        self.results.field_index(expr.id).expect("Field Index"),
                    ),
                }
            }
            hir::ExpressionKind::PatternBinding(condition) => {
                // Lower `case pattern = expr` to a match that returns true if the pattern matches.
                // match expr { case pattern => true, case _ => false }
                let scrutinee = self.lower_expr(&condition.expression);
                let pattern = pattern_from_hir(self.gcx, self.results.as_ref(), &condition.pattern);

                // Create the "true" arm for when the pattern matches
                let true_lit = self.push_expr(
                    ExprKind::Literal(Constant {
                        ty: self.gcx.types.bool,
                        value: ConstantKind::Bool(true),
                    }),
                    self.gcx.types.bool,
                    condition.span,
                );
                let true_arm_id = {
                    let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
                    self.func.arms.push(thir::Arm {
                        pattern: Box::new(pattern),
                        guard: None,
                        body: true_lit,
                        span: condition.span,
                    });
                    id
                };

                // Create the "false" arm (wildcard) for when the pattern doesn't match
                let false_lit = self.push_expr(
                    ExprKind::Literal(Constant {
                        ty: self.gcx.types.bool,
                        value: ConstantKind::Bool(false),
                    }),
                    self.gcx.types.bool,
                    condition.span,
                );
                let wild_pattern = thir::Pattern {
                    ty: self.results.node_type(condition.expression.id),
                    span: condition.span,
                    kind: thir::PatternKind::Wild,
                };
                let false_arm_id = {
                    let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
                    self.func.arms.push(thir::Arm {
                        pattern: Box::new(wild_pattern),
                        guard: None,
                        body: false_lit,
                        span: condition.span,
                    });
                    id
                };

                ExprKind::Match {
                    scrutinee,
                    arms: vec![true_arm_id, false_arm_id],
                    binding_condition: true,
                }
            }
            hir::ExpressionKind::Closure(closure) => {
                // Get closure capture information from type checking phase
                let captures_info = self.gcx.get_closure_captures(closure.def_id);
                let kind = captures_info
                    .as_ref()
                    .map(|caps| caps.kind)
                    .unwrap_or(crate::sema::models::ClosureKind::Fn);

                // Build capture expressions for each captured variable
                let mut captures = vec![];
                if let Some(ref caps) = captures_info {
                    for cap in &caps.captures {
                        if closure.params.iter().any(|param| param.id == cap.source_id) {
                            continue;
                        }
                        // Check if this capture is itself an upvar in our current closure scope
                        // (needed for nested closures)
                        let mut capture_expr_id = self.lower_capture_source(*cap, span);

                        if matches!(cap.capture_kind, crate::sema::models::CaptureKind::ByRef) {
                            let ref_ty =
                                Ty::new(crate::sema::models::TyKind::Reference(cap.ty), self.gcx);
                            capture_expr_id = self.func.exprs.push(Expr {
                                kind: ExprKind::Reference {
                                    expr: capture_expr_id,
                                },
                                ty: ref_ty,
                                span,
                            });
                        }

                        captures.push(ClosureCapture {
                            source_id: cap.source_id,
                            capture_expr: capture_expr_id,
                            capture_kind: cap.capture_kind,
                            field_index: cap.field_index,
                        });
                    }
                }

                // Generate THIR function for the closure body
                let closure_func = self.lower_closure_body(closure);
                self.nested_closures.push(closure_func);

                ExprKind::Closure {
                    def_id: closure.def_id,
                    captures,
                    kind,
                }
            }
            hir::ExpressionKind::Await(inner) => {
                // The source marker authorizes suspension throughout the expression.
                // Actual async calls are awaited below, before value adjustments.
                let value = self.lower_expr(inner);
                return self.func.exprs[value].clone();
            }
            hir::ExpressionKind::Malformed => {
                unreachable!("malformed expression should not reach THIR lowering");
            }
        };

        if matches!(kind, ExprKind::Call { .. })
            && let Some(source) = self.results.overload_source(expr.id)
        {
            let raw = instantiate_ty_with_args(
                self.gcx,
                self.gcx.get_signature(source).output,
                self.results
                    .instantiation(expr.id)
                    .unwrap_or_else(GenericArguments::empty),
            );
            if raw != ty && self.is_refined_class_self_call(expr, raw, ty) {
                let is_async = matches!(kind, ExprKind::Call { is_async: true, .. });
                let mut value = self.push_expr(kind, raw, span);
                if is_async {
                    value = self.push_expr(ExprKind::Await { future: value }, raw, span);
                }
                return Expr {
                    kind: ExprKind::ClassSelfResult { value },
                    ty,
                    span,
                };
            }
        }
        if matches!(kind, ExprKind::Call { is_async: true, .. }) {
            let future = self.push_expr(kind, ty, span);
            return Expr {
                kind: ExprKind::Await { future },
                ty,
                span,
            };
        }
        Expr { kind, ty, span }
    }

    fn is_refined_class_self_call(
        &self,
        expr: &hir::Expression,
        raw: Ty<'ctx>,
        target: Ty<'ctx>,
    ) -> bool {
        self.gcx.is_class_subtype(target, raw)
            && self
                .results
                .overload_source(expr.id)
                .and_then(|method| self.gcx.class_method(raw, method))
                .is_some_and(|method| method.returns_self)
    }

    fn lower_literal(&self, lit: &hir::Literal) -> ConstantKind {
        match lit {
            hir::Literal::Bool(b) => ConstantKind::Bool(*b),
            hir::Literal::Rune(r) => ConstantKind::Rune(*r),
            hir::Literal::String(s) => ConstantKind::String(*s),
            hir::Literal::Integer { value, .. } => ConstantKind::Integer(*value as u64),
            hir::Literal::Float(f) => ConstantKind::Float(*f),
            hir::Literal::Nil => ConstantKind::Unit,
        }
    }

    fn capture_place(&self, expr: &hir::Expression) -> Option<(hir::NodeID, Vec<FieldIndex>)> {
        match &expr.kind {
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                let Resolution::LocalVariable(root) = path.resolution else {
                    return None;
                };
                Some((root, vec![]))
            }
            hir::ExpressionKind::Member { target, .. }
            | hir::ExpressionKind::TupleAccess(target, _) => {
                let field = FieldIndex::from_usize(self.results.field_index(expr.id)?);
                let (root, mut fields) = self.capture_place(target)?;
                if let Some(class) = self
                    .gcx
                    .class_for_payload(self.results.node_type(target.id))
                {
                    fields.extend(
                        self.gcx
                            .class_field_payload_path(class, field.index())?
                            .into_iter()
                            .map(FieldIndex::from_raw),
                    );
                } else {
                    fields.push(field);
                }
                Some((root, fields))
            }
            _ => None,
        }
    }

    /// Materialize the selected source field before copying/moving/borrowing
    /// it. An enclosing closure may store a parent of the requested place.
    fn lower_capture_source(
        &mut self,
        capture: crate::sema::models::CapturedVar<'ctx>,
        span: crate::span::Span,
    ) -> ExprId {
        let parent = self
            .captures_map
            .as_ref()
            .and_then(|captures| {
                captures.iter().find(|parent| {
                    parent.source_id == capture.source_id
                        && parent.projection.len() <= capture.projection.len()
                        && parent
                            .projection
                            .iter()
                            .zip(capture.projection)
                            .all(|(left, right)| left.field == right.field)
                })
            })
            .copied();
        let (kind, ty, start) = if let Some(parent) = parent {
            (
                ExprKind::Upvar {
                    field_index: parent.field_index,
                    capture_kind: parent.capture_kind,
                },
                parent.ty,
                parent.projection.len(),
            )
        } else {
            let root = self
                .local_remap
                .as_ref()
                .and_then(|remap| remap.get(&capture.source_id))
                .copied()
                .unwrap_or(capture.source_id);
            (ExprKind::Local(root), capture.root_ty, 0)
        };
        let mut source = self.push_expr(kind, ty, span);
        for field in &capture.projection[start..] {
            source = self.push_expr(
                ExprKind::Field {
                    lhs: source,
                    index: field.field,
                },
                field.ty,
                span,
            );
        }
        source
    }

    /// Lower a closure body into a separate THIR function
    fn lower_closure_body(&mut self, closure: &hir::ClosureExpr) -> ThirFunction<'ctx> {
        // Get captures for this closure
        let captures = self.gcx.get_closure_captures(closure.def_id);

        let captures_map = captures.as_ref().map(|caps| caps.captures.clone());

        // Generate a synthetic node ID for the self parameter
        // Use a high value based on the closure def_id's package to avoid collisions
        let self_param_id = crate::hir::NodeID::from_raw(
            closure
                .def_id
                .package()
                .raw()
                .wrapping_mul(0x10000)
                .wrapping_add(0xFFFF0000),
        );

        // Create a new FunctionLower for the closure body
        let mut closure_lower = FunctionLower {
            gcx: self.gcx,
            results: self.results.clone(),
            func: ThirFunction {
                id: closure.def_id,
                body: None,
                constructor_self: None,
                span: closure.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
                match_reports: FxHashMap::default(),
                is_async: self.gcx.definition_is_async(closure.def_id),
            },
            nested_closures: Vec::new(),
            captures_map,
            local_remap: None,
            next_synthetic_local_raw: u32::MAX,
            convenience: None,
        };

        // Get the full signature (self pointer + explicit params)
        let signature = self.gcx.get_signature(closure.def_id);

        // Add the self parameter (pointer to closure struct)
        // This is the first parameter in the signature - MIR will place it at _1
        if !signature.inputs.is_empty() {
            let self_sig_param = &signature.inputs[0];
            closure_lower.func.params.push(Param {
                id: self_param_id, // Synthetic ID, not referenced by body
                name: self_sig_param.name,
                ty: self_sig_param.ty,
                span: closure.span,
            });
        }

        // Add explicit closure parameters (after self in the signature).
        // Prefer the resolved local type recorded during type checking so THIR
        // does not depend on the cached closure signature preserving parameter
        // slots perfectly through later closure-signature updates.
        for (index, param) in closure.params.iter().enumerate() {
            let sig_param = signature.inputs.get(index + 1);
            let ty = self
                .results
                .try_node_type(param.id)
                .or_else(|| sig_param.map(|param| param.ty))
                .unwrap_or(self.gcx.types.error);
            let name =
                sig_param
                    .map(|param| param.name)
                    .unwrap_or_else(|| match &param.pattern.kind {
                        hir::PatternKind::Binding { name, .. } => name.symbol,
                        _ => self.gcx.intern_symbol("_"),
                    });
            closure_lower.func.params.push(Param {
                id: param.id,
                name,
                ty,
                span: param.span,
            });
        }

        // Lower the closure body expression
        let body_expr_id = closure_lower.lower_expr(&closure.body);

        // Create a block containing just the body expression
        let block_id = BlockId::from_raw(closure_lower.func.blocks.len() as u32);
        closure_lower.func.blocks.push(Block {
            id: block_id,
            stmts: vec![],
            expr: Some(body_expr_id),
        });
        closure_lower.func.body = Some(block_id);

        // Collect any nested closures from within this closure
        self.nested_closures.extend(closure_lower.nested_closures);

        closure_lower.func
    }

    fn lower_path_expression(
        &mut self,
        expr: &hir::Expression,
        resolution: Resolution,
    ) -> thir::ExprKind<'ctx> {
        if let Resolution::StdItem(item) = resolution {
            let Some(def_id) = self.gcx.std_item_def(item) else {
                self.gcx.dcx().emit_error(
                    "unresolvable std item used as value".into(),
                    Some(expr.span),
                );
                return ExprKind::Literal(Constant {
                    ty: self.gcx.types.error,
                    value: ConstantKind::Unit,
                });
            };
            let kind = self.gcx.definition_kind(def_id);
            return self.lower_path_expression(expr, Resolution::Definition(def_id, kind));
        }

        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
            ) => ExprKind::Zst {
                id,
                generic_args: self.results.instantiation(expr.id),
            },
            Resolution::Definition(id, DefinitionKind::ModuleVariable) => {
                let static_ty = self.gcx.get_type(id);
                let ptr_mutability = self
                    .gcx
                    .try_get_static_mutability(id)
                    .unwrap_or(Mutability::Immutable);
                let ptr_ty = Ty::new(TyKind::Pointer(static_ty, ptr_mutability), self.gcx);
                let zst = self.push_expr(
                    ExprKind::Zst {
                        id,
                        generic_args: None,
                    },
                    ptr_ty,
                    expr.span,
                );
                ExprKind::Deref(zst)
            }
            Resolution::Definition(
                id,
                DefinitionKind::Constant | DefinitionKind::AssociatedConstant,
            ) => {
                let Some(constant) = self.gcx.try_get_const(id) else {
                    self.gcx
                        .dcx()
                        .emit_error("constant value is not available".into(), Some(expr.span));
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                if let ConstKind::Value(ConstValue::EnumUnitVariant(ctor_id)) = constant.kind {
                    let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                    let TyKind::Adt(_, generic_args) = constant.ty.kind() else {
                        self.gcx.dcx().emit_error(
                            "constant enum unit variant has an invalid type".into(),
                            Some(expr.span),
                        );
                        return ExprKind::Literal(Constant {
                            ty: self.gcx.types.error,
                            value: ConstantKind::Unit,
                        });
                    };
                    return ExprKind::Adt(thir::AdtExpression {
                        base: None,
                        definition,
                        variant_index: Some(variant_index),
                        generic_args,
                        fields: Vec::new(),
                    });
                }
                let Some(value) = self.const_kind_to_thir(constant.kind) else {
                    self.gcx.dcx().emit_error(
                        "const parameter values are not supported here".into(),
                        Some(expr.span),
                    );
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                ExprKind::Literal(Constant {
                    ty: constant.ty,
                    value,
                })
            }
            Resolution::Definition(id, DefinitionKind::ConstParameter) => {
                let ty = self.results.node_type(expr.id);
                let Some(owner) = self.gcx.definition_parent(id) else {
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                let generics = self.gcx.generics_of(owner);
                let Some(def) = generics.parameters.iter().find(|p| p.id == id) else {
                    return ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    });
                };
                let param = crate::sema::models::GenericParameter {
                    index: def.index,
                    name: def.name,
                };
                ExprKind::Literal(Constant {
                    ty,
                    value: ConstantKind::ConstParam(param),
                })
            }
            Resolution::Definition(
                id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Function),
            ) => ExprKind::Zst {
                id,
                generic_args: self.results.instantiation(expr.id),
            },
            Resolution::Definition(
                ctor_id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
            ) => {
                let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                let ty = self.results.node_type(expr.id);
                let TyKind::Adt(_, generic_args) = ty.kind() else {
                    unreachable!()
                };
                ExprKind::Adt(thir::AdtExpression {
                    base: None,
                    definition,
                    variant_index: Some(variant_index),
                    generic_args,
                    fields: Vec::new(),
                })
            }
            Resolution::LocalVariable(id) => {
                // Check if this is a captured variable that needs to be accessed via upvar
                if let Some(captures_map) = &self.captures_map {
                    if let Some(capture) = captures_map
                        .iter()
                        .find(|capture| capture.source_id == id && capture.projection.is_empty())
                    {
                        // This is a captured variable - generate Upvar access
                        return ExprKind::Upvar {
                            field_index: capture.field_index,
                            capture_kind: capture.capture_kind,
                        };
                    }
                }
                if let Some(local_remap) = &self.local_remap {
                    if let Some(&remapped) = local_remap.get(&id) {
                        return ExprKind::Local(remapped);
                    }
                }
                // Not a capture - regular local variable
                ExprKind::Local(id)
            }
            _ => unreachable!(),
        }
    }

    fn const_kind_to_thir(&self, kind: ConstKind) -> Option<ConstantKind> {
        match kind {
            ConstKind::Value(value) => Some(match value {
                ConstValue::Bool(b) => ConstantKind::Bool(b),
                ConstValue::Rune(r) => ConstantKind::Rune(r),
                ConstValue::String(s) => ConstantKind::String(s),
                ConstValue::Integer(i) => ConstantKind::Integer(i as u64),
                ConstValue::Float(f) => ConstantKind::Float(f),
                ConstValue::Unit => ConstantKind::Unit,
                ConstValue::EnumUnitVariant(_) => return None,
            }),
            ConstKind::Param(p) => Some(ConstantKind::ConstParam(p)),
            ConstKind::Infer(_) => None,
        }
    }

    fn push_expr(&mut self, kind: ExprKind<'ctx>, ty: Ty<'ctx>, span: crate::span::Span) -> ExprId {
        let id = ExprId::from_raw(self.func.exprs.len() as u32);
        self.func.exprs.push(Expr { kind, ty, span });
        id
    }

    fn variant_ctor_callee(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        let resolution = if let Some(def_id) = self.results.overload_source(callee.id) {
            Some(Resolution::Definition(
                def_id,
                self.gcx.definition_kind(def_id),
            ))
        } else {
            match &callee.kind {
                hir::ExpressionKind::Path(path) => match path {
                    hir::ResolvedPath::Resolved(path) => Some(path.resolution.clone()),
                    hir::ResolvedPath::Relative(..) => self.results.value_resolution(callee.id),
                },
                hir::ExpressionKind::InferredMember { .. } => {
                    self.results.value_resolution(callee.id)
                }
                _ => None,
            }
        }?;

        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Function),
            ) => Some(id),
            _ => None,
        }
    }

    fn enum_variant_from_ctor(
        &self,
        ctor_id: DefinitionID,
    ) -> (crate::sema::models::AdtDef, VariantIndex) {
        let Some(parent_id) = self.gcx.definition_parent(ctor_id) else {
            unreachable!()
        };

        let enum_id = match self.gcx.definition_kind(parent_id) {
            DefinitionKind::Enum => parent_id,
            DefinitionKind::Variant => match self.gcx.definition_parent(parent_id) {
                Some(enum_id) => enum_id,
                None => {
                    unreachable!()
                }
            },
            _ => {
                unreachable!()
            }
        };

        let def = self.gcx.get_enum_definition(enum_id);
        let Some((index, _)) = def
            .variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.ctor_def_id == ctor_id)
        else {
            unreachable!()
        };

        (def.adt_def, VariantIndex::from_usize(index))
    }

    fn lower_match_arm(&mut self, arm: &hir::MatchArm) -> thir::ArmId {
        let guard = arm.guard.as_deref().map(|expr| self.lower_expr(expr));
        let body = self.lower_expr(&arm.body);
        let pattern = pattern_from_hir(self.gcx, self.results.as_ref(), &arm.pattern);
        let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
        self.func.arms.push(thir::Arm {
            pattern: Box::new(pattern),
            guard,
            body,
            span: arm.span,
        });
        id
    }

    fn lower_propagate_expr(
        &mut self,
        expr: &hir::Expression,
        inner: &hir::Expression,
    ) -> Expr<'ctx> {
        if let hir::ExpressionKind::MethodCall {
            receiver,
            arguments,
            ..
        } = &inner.kind
        {
            if self.results.base_initializer_calls.contains(&inner.id) {
                return self.lower_base_initializer(inner, receiver, arguments, true);
            }
            if self.results.self_initializer_calls.contains(&inner.id) {
                return self.lower_self_initializer(inner, receiver, arguments, true);
            }
        }
        let ty = self.results.node_type(expr.id);
        let span = expr.span;
        let scrutinee = self.lower_expr(inner);
        let scrutinee_ty = crate::sema::tycheck::utils::normalize_aliases(
            self.gcx,
            self.results.node_type(inner.id),
        );
        let return_ty = crate::sema::tycheck::utils::normalize_aliases(
            self.gcx,
            self.gcx.function_body_output(self.func.id),
        );
        let never_ty = Ty::new(TyKind::Never, self.gcx);

        let TyKind::Adt(scrutinee_def, scrutinee_args) = scrutinee_ty.kind() else {
            unreachable!("propagate operand must be Optional or Result");
        };
        let enum_def = self.gcx.get_enum_definition(scrutinee_def.id);

        let make_arm =
            |this: &mut Self, pattern: thir::Pattern<'ctx>, body: ExprId| -> thir::ArmId {
                let id = thir::ArmId::from_raw(this.func.arms.len() as u32);
                this.func.arms.push(thir::Arm {
                    pattern: Box::new(pattern),
                    guard: None,
                    body,
                    span,
                });
                id
            };

        if Some(scrutinee_def.id) == self.gcx.std_item_def(hir::StdItem::Optional) {
            let some_variant_def = self
                .gcx
                .std_item_def(hir::StdItem::OptionalSomeVariant)
                .expect("Optional.some variant");
            let none_variant_def = self
                .gcx
                .std_item_def(hir::StdItem::OptionalNoneVariant)
                .expect("Optional.none variant");

            let some_variant = enum_def
                .variants
                .iter()
                .find(|variant| variant.def_id == some_variant_def)
                .copied()
                .expect("Optional.some variant in enum definition");
            let none_variant = enum_def
                .variants
                .iter()
                .find(|variant| variant.def_id == none_variant_def)
                .copied()
                .expect("Optional.none variant in enum definition");

            let inner_ty = scrutinee_args
                .get(0)
                .copied()
                .and_then(GenericArgument::ty)
                .expect("Optional[T] inner type");
            let binding_local = self.fresh_synthetic_local();
            let binding_pattern = thir::Pattern {
                ty: inner_ty,
                span,
                kind: thir::PatternKind::Binding {
                    name: self.gcx.intern_symbol("__propagate_value"),
                    local: binding_local,
                    ty: inner_ty,
                },
            };
            let some_pattern = thir::Pattern {
                ty: scrutinee_ty,
                span,
                kind: thir::PatternKind::Variant {
                    definition: enum_def.adt_def,
                    variant: some_variant,
                    subpatterns: vec![thir::FieldPattern {
                        index: FieldIndex::from_usize(0),
                        pattern: binding_pattern,
                    }],
                },
            };
            let none_pattern = thir::Pattern {
                ty: scrutinee_ty,
                span,
                kind: thir::PatternKind::Variant {
                    definition: enum_def.adt_def,
                    variant: none_variant,
                    subpatterns: vec![],
                },
            };

            let some_body = self.push_expr(ExprKind::Local(binding_local), inner_ty, span);
            let none_value = self.push_expr(
                ExprKind::Adt(thir::AdtExpression {
                    base: None,
                    definition: scrutinee_def,
                    variant_index: Some(VariantIndex::from_usize(
                        enum_def
                            .variants
                            .iter()
                            .position(|variant| variant.def_id == none_variant.def_id)
                            .expect("Optional.none index"),
                    )),
                    generic_args: match return_ty.kind() {
                        TyKind::Adt(_, args) => args,
                        _ => unreachable!("Optional propagation return type must be Optional"),
                    },
                    fields: vec![],
                }),
                return_ty,
                span,
            );
            let none_body = self.push_expr(
                ExprKind::Return {
                    value: Some(none_value),
                },
                never_ty,
                span,
            );

            let some_arm = make_arm(self, some_pattern, some_body);
            let none_arm = make_arm(self, none_pattern, none_body);

            return Expr {
                kind: ExprKind::Match {
                    scrutinee,
                    arms: vec![some_arm, none_arm],
                    binding_condition: false,
                },
                ty,
                span,
            };
        }

        let ok_variant_def = self
            .gcx
            .std_item_def(hir::StdItem::ResultOkVariant)
            .expect("Result.ok variant");
        let err_variant_def = self
            .gcx
            .std_item_def(hir::StdItem::ResultErrVariant)
            .expect("Result.err variant");
        let ok_variant = enum_def
            .variants
            .iter()
            .find(|variant| variant.def_id == ok_variant_def)
            .copied()
            .expect("Result.ok variant in enum definition");
        let err_variant = enum_def
            .variants
            .iter()
            .find(|variant| variant.def_id == err_variant_def)
            .copied()
            .expect("Result.err variant in enum definition");

        let ok_ty = scrutinee_args
            .get(0)
            .copied()
            .and_then(GenericArgument::ty)
            .expect("Result[T, E] ok type");
        let err_ty = scrutinee_args
            .get(1)
            .copied()
            .and_then(GenericArgument::ty)
            .expect("Result[T, E] err type");
        let ok_local = self.fresh_synthetic_local();
        let err_local = self.fresh_synthetic_local();

        let ok_pattern = thir::Pattern {
            ty: scrutinee_ty,
            span,
            kind: thir::PatternKind::Variant {
                definition: enum_def.adt_def,
                variant: ok_variant,
                subpatterns: vec![thir::FieldPattern {
                    index: FieldIndex::from_usize(0),
                    pattern: thir::Pattern {
                        ty: ok_ty,
                        span,
                        kind: thir::PatternKind::Binding {
                            name: self.gcx.intern_symbol("__propagate_value"),
                            local: ok_local,
                            ty: ok_ty,
                        },
                    },
                }],
            },
        };
        let err_pattern = thir::Pattern {
            ty: scrutinee_ty,
            span,
            kind: thir::PatternKind::Variant {
                definition: enum_def.adt_def,
                variant: err_variant,
                subpatterns: vec![thir::FieldPattern {
                    index: FieldIndex::from_usize(0),
                    pattern: thir::Pattern {
                        ty: err_ty,
                        span,
                        kind: thir::PatternKind::Binding {
                            name: self.gcx.intern_symbol("__propagate_error"),
                            local: err_local,
                            ty: err_ty,
                        },
                    },
                }],
            },
        };

        let ok_body = self.push_expr(ExprKind::Local(ok_local), ok_ty, span);
        let return_args = match return_ty.kind() {
            TyKind::Adt(_, args) => args,
            _ => unreachable!("Result propagation return type must be Result"),
        };
        let err_value = self.push_expr(ExprKind::Local(err_local), err_ty, span);
        let err_value =
            if let Some(conversion) = self.results.result_propagation_conversion(expr.id) {
                let callee_ty = instantiate_ty_with_args(
                    self.gcx,
                    self.gcx.get_type(conversion.method_id),
                    conversion.generic_args,
                );
                let callee = self.push_expr(
                    ExprKind::Zst {
                        id: conversion.method_id,
                        generic_args: Some(conversion.generic_args),
                    },
                    callee_ty,
                    span,
                );
                self.push_expr(
                    ExprKind::Call {
                        argument_evaluation_order: None,
                        callee,
                        args: vec![err_value],
                        is_async: false,
                    },
                    conversion.target_ty,
                    span,
                )
            } else {
                err_value
            };
        let err_variant_index = enum_def
            .variants
            .iter()
            .position(|variant| variant.def_id == err_variant.def_id)
            .expect("Result.err index");
        let return_err_value = self.push_expr(
            ExprKind::Adt(thir::AdtExpression {
                base: None,
                definition: scrutinee_def,
                variant_index: Some(VariantIndex::from_usize(err_variant_index)),
                generic_args: return_args,
                fields: vec![thir::FieldExpression {
                    index: FieldIndex::from_usize(0),
                    expression: err_value,
                }],
            }),
            return_ty,
            span,
        );
        let err_body = self.push_expr(
            ExprKind::Return {
                value: Some(return_err_value),
            },
            never_ty,
            span,
        );

        let ok_arm = make_arm(self, ok_pattern, ok_body);
        let err_arm = make_arm(self, err_pattern, err_body);

        Expr {
            kind: ExprKind::Match {
                scrutinee,
                arms: vec![ok_arm, err_arm],
                binding_condition: false,
            },
            ty,
            span,
        }
    }

    fn push_stmt(&mut self, stmt: Stmt<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.func.stmts.len() as u32);
        self.func.stmts.push(stmt);
        id
    }

    fn fresh_synthetic_local(&mut self) -> hir::NodeID {
        let id = hir::NodeID::from_raw(self.next_synthetic_local_raw);
        self.next_synthetic_local_raw = self.next_synthetic_local_raw.saturating_sub(1);
        id
    }
}

fn bin_op(op: hir::BinaryOperator) -> mir::BinaryOperator {
    match op {
        hir::BinaryOperator::Add => mir::BinaryOperator::Add,
        hir::BinaryOperator::Sub => mir::BinaryOperator::Sub,
        hir::BinaryOperator::Mul => mir::BinaryOperator::Mul,
        hir::BinaryOperator::Div => mir::BinaryOperator::Div,
        hir::BinaryOperator::Rem => mir::BinaryOperator::Rem,
        hir::BinaryOperator::BitAnd => mir::BinaryOperator::BitAnd,
        hir::BinaryOperator::BitOr => mir::BinaryOperator::BitOr,
        hir::BinaryOperator::BitXor => mir::BinaryOperator::BitXor,
        hir::BinaryOperator::BitShl => mir::BinaryOperator::BitShl,
        hir::BinaryOperator::BitShr => mir::BinaryOperator::BitShr,
        hir::BinaryOperator::Eql => mir::BinaryOperator::Eql,
        hir::BinaryOperator::Lt => mir::BinaryOperator::Lt,
        hir::BinaryOperator::Gt => mir::BinaryOperator::Gt,
        hir::BinaryOperator::Leq => mir::BinaryOperator::Leq,
        hir::BinaryOperator::Geq => mir::BinaryOperator::Geq,
        hir::BinaryOperator::Neq => mir::BinaryOperator::Neq,
        _ => {
            unreachable!()
        }
    }
}
