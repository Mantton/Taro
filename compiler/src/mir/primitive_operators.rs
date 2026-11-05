//! Primitive operator witnesses are generated per concrete instance in the
//! consuming compilation unit. A precompiled standard-library arithmetic body
//! would otherwise bake its build profile's overflow behavior into callers.
use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::{DefinitionID, StdItem},
    mir::{
        BasicBlockData, BinaryOperator, Body, CallUnwindAction, Constant, ConstantKind, LocalDecl,
        LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, UnaryOperator,
    },
    sema::{
        models::{
            AssociatedTypeBinding, GenericArgument, GenericParameter, GenericParameterDefinition,
            GenericParameterDefinitionKind, Generics, InterfaceGoal, InterfaceReference,
            LabeledFunctionParameter, LabeledFunctionSignature, SyntheticDefinition,
            SyntheticDefinitionKind, Ty, TyKind,
        },
        tycheck::utils::normalize_post_monomorphization,
    },
    span::Span,
    specialize::Instance,
};
use index_vec::IndexVec;

pub(crate) const ITEMS: &[StdItem] = &[
    StdItem::Add,
    StdItem::Sub,
    StdItem::Mul,
    StdItem::Div,
    StdItem::Rem,
    StdItem::BitAnd,
    StdItem::BitOr,
    StdItem::BitXor,
    StdItem::Shl,
    StdItem::Shr,
    StdItem::AddAssign,
    StdItem::SubAssign,
    StdItem::MulAssign,
    StdItem::DivAssign,
    StdItem::RemAssign,
    StdItem::BitAndAssign,
    StdItem::BitOrAssign,
    StdItem::BitXorAssign,
    StdItem::ShlAssign,
    StdItem::ShrAssign,
    StdItem::Neg,
    StdItem::Not,
    StdItem::BitNot,
];

#[derive(Clone, Copy)]
enum Operation {
    Binary(BinaryOperator),
    Assign(BinaryOperator),
    Unary(UnaryOperator),
}
fn operation(item: StdItem) -> Option<Operation> {
    use BinaryOperator as B;
    use Operation::*;
    Some(match item {
        StdItem::Add => Binary(B::Add),
        StdItem::Sub => Binary(B::Sub),
        StdItem::Mul => Binary(B::Mul),
        StdItem::Div => Binary(B::Div),
        StdItem::Rem => Binary(B::Rem),
        StdItem::BitAnd => Binary(B::BitAnd),
        StdItem::BitOr => Binary(B::BitOr),
        StdItem::BitXor => Binary(B::BitXor),
        StdItem::Shl => Binary(B::BitShl),
        StdItem::Shr => Binary(B::BitShr),
        StdItem::AddAssign => Assign(B::Add),
        StdItem::SubAssign => Assign(B::Sub),
        StdItem::MulAssign => Assign(B::Mul),
        StdItem::DivAssign => Assign(B::Div),
        StdItem::RemAssign => Assign(B::Rem),
        StdItem::BitAndAssign => Assign(B::BitAnd),
        StdItem::BitOrAssign => Assign(B::BitOr),
        StdItem::BitXorAssign => Assign(B::BitXor),
        StdItem::ShlAssign => Assign(B::BitShl),
        StdItem::ShrAssign => Assign(B::BitShr),
        StdItem::Neg => Unary(UnaryOperator::Negate),
        StdItem::Not => Unary(UnaryOperator::LogicalNot),
        StdItem::BitNot => Unary(UnaryOperator::BitwiseNot),
        _ => return None,
    })
}

pub(crate) fn supports<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, item: StdItem) -> bool {
    let ty = crate::sema::tycheck::utils::normalize_aliases(gcx, ty);
    let ty = match (operation(item), ty.kind()) {
        (Some(Operation::Assign(_)), TyKind::Reference(inner)) => inner,
        _ => ty,
    };
    let integer = matches!(ty.kind(), TyKind::Int(_) | TyKind::UInt(_));
    let numeric = integer || matches!(ty.kind(), TyKind::Float(_));
    match item {
        StdItem::Add
        | StdItem::Sub
        | StdItem::Mul
        | StdItem::Div
        | StdItem::Rem
        | StdItem::AddAssign
        | StdItem::SubAssign
        | StdItem::MulAssign
        | StdItem::DivAssign
        | StdItem::RemAssign
        | StdItem::Neg => numeric,
        StdItem::BitAnd
        | StdItem::BitOr
        | StdItem::BitXor
        | StdItem::BitAndAssign
        | StdItem::BitOrAssign
        | StdItem::BitXorAssign => integer || matches!(ty.kind(), TyKind::Bool),
        StdItem::Shl | StdItem::Shr | StdItem::ShlAssign | StdItem::ShrAssign | StdItem::BitNot => {
            integer
        }
        StdItem::Not => matches!(ty.kind(), TyKind::Bool),
        _ => false,
    }
}

/// Materialize the exact builtin conformance for inference and runtime casts.
/// Assignment belongs to &T with Rhs=T, rather than advertising it on T or
/// treating the reference header itself as the RHS scalar.
pub(crate) fn interface_for_type<'ctx>(
    gcx: Gcx<'ctx>,
    self_ty: Ty<'ctx>,
    item: StdItem,
) -> Option<InterfaceReference<'ctx>> {
    let self_ty = crate::sema::tycheck::utils::normalize_aliases(gcx, self_ty);
    let op = operation(item)?;
    let operand = match (op, self_ty.kind()) {
        (Operation::Assign(_), TyKind::Reference(inner)) => inner,
        (Operation::Assign(_), _) => return None,
        _ => self_ty,
    };
    if !supports(gcx, operand, item) {
        return None;
    }
    let id = gcx.std_item_def(item)?;
    let mut args = vec![GenericArgument::Type(self_ty)];
    if !matches!(op, Operation::Unary(_)) {
        args.push(GenericArgument::Type(operand));
    }
    if gcx.generics_of(id).total_count() != args.len() {
        return None;
    }
    let bindings = if matches!(op, Operation::Assign(_)) {
        vec![]
    } else {
        let output = gcx
            .get_interface_requirements(id)?
            .types
            .iter()
            .find(|ty| gcx.symbol_eq(ty.name, "Output"))?;
        vec![AssociatedTypeBinding {
            name: output.name,
            ty: operand,
        }]
    };
    Some(InterfaceReference {
        id,
        arguments: gcx.store.interners.intern_generic_args(args),
        bindings: gcx.store.arenas.global.alloc_slice_copy(&bindings),
    })
}

pub(crate) fn item_for_goal<'ctx>(gcx: Gcx<'ctx>, goal: InterfaceGoal<'ctx>) -> Option<StdItem> {
    let item = ITEMS
        .iter()
        .copied()
        .find(|item| gcx.std_item_def(*item) == Some(goal.interface_id))?;
    let ty = crate::sema::tycheck::utils::normalize_aliases(gcx, goal.self_ty);
    let ty = match (operation(item)?, ty.kind()) {
        (Operation::Assign(_), TyKind::Reference(inner)) => inner,
        (Operation::Assign(_), _) => return None,
        _ => ty,
    };
    let op = operation(item)?;
    if !supports(gcx, ty, item)
        || goal.bindings.iter().any(|binding| {
            matches!(op, Operation::Assign(_))
                || !gcx.symbol_eq(binding.name, "Output")
                || crate::sema::tycheck::utils::normalize_aliases(gcx, binding.ty) != ty
        })
    {
        return None;
    }
    let arity = match op {
        Operation::Unary(_) => 0,
        _ => 1,
    };
    // Primitive operands and their associated Output are the same scalar type.
    // Bounds introduce neither reference forwarding nor numeric conversion.
    if goal.interface_args.len() > arity || goal.interface_args.iter().any(|arg| {
            !matches!(arg, GenericArgument::Type(actual) if crate::sema::tycheck::utils::normalize_aliases(gcx, *actual) == ty)
    }) {
        return None;
    }
    Some(item)
}

pub(crate) fn declaration(gcx: Gcx<'_>, item: StdItem, span: Span) -> DefinitionID {
    let kind = SyntheticDefinitionKind::PrimitiveOperator(item);
    if let Some(id) =
        gcx.store
            .synthetic_definitions
            .borrow()
            .iter()
            .find_map(|(id, definition)| {
                (id.package() == gcx.package_index() && definition.kind == kind).then_some(*id)
            })
    {
        return id;
    }
    let op = operation(item).expect("primitive operator item");
    let id = gcx.allocate_synthetic_id(gcx.package_index());
    let parameter_id = gcx.allocate_synthetic_id(gcx.package_index());
    let name = gcx.intern_symbol("T");
    let ty = Ty::new(TyKind::Parameter(GenericParameter { index: 0, name }), gcx);
    let generics = gcx.store.arenas.generics.alloc(Generics {
        parameters: vec![GenericParameterDefinition {
            name,
            id: parameter_id,
            index: 0,
            kind: GenericParameterDefinitionKind::Type { default: None },
        }],
        has_self: false,
        parent: None,
        parent_count: 0,
    });
    let input = |name: &str, ty| LabeledFunctionParameter {
        name: gcx.intern_symbol(name),
        label: None,
        default_provider: None,
        ty,
    };
    let receiver = match op {
        Operation::Unary(_) => ty,
        Operation::Assign(_) => Ty::new(TyKind::Reference(ty), gcx),
        Operation::Binary(_) => ty,
    };
    let mut inputs = vec![input("self", receiver)];
    if !matches!(op, Operation::Unary(_)) {
        inputs.push(input("rhs", ty));
    }
    let signature = gcx
        .store
        .arenas
        .function_signatures
        .alloc(LabeledFunctionSignature {
            inputs,
            output: if matches!(op, Operation::Assign(_)) {
                gcx.types.void
            } else {
                ty
            },
            is_variadic: false,
            abi: None,
        });
    gcx.register_synthetic_definition(
        id,
        SyntheticDefinition {
            kind,
            name: gcx.intern_symbol(&format!("${}primitive{item:?}", "")),
            generics,
            signature,
            span,
        },
    );
    gcx.cache_type(id, Ty::from_labeled_signature(gcx, signature));
    id
}

pub(crate) fn validate_declaration(
    gcx: Gcx<'_>,
    definition: &SyntheticDefinition<'_>,
) -> Result<(), &'static str> {
    let SyntheticDefinitionKind::PrimitiveOperator(item) = definition.kind else {
        return Ok(());
    };
    let op = operation(item).ok_or("invalid primitive operator metadata item")?;
    let generics = definition.generics;
    let [parameter] = generics.parameters.as_slice() else {
        return Err("primitive operator needs one type parameter");
    };
    if generics.has_self
        || generics.parent.is_some()
        || generics.parent_count != 0
        || parameter.index != 0
        || !matches!(
            parameter.kind,
            GenericParameterDefinitionKind::Type { default: None }
        )
    {
        return Err("invalid primitive operator generics");
    }
    let ty = Ty::new(
        TyKind::Parameter(GenericParameter {
            index: 0,
            name: parameter.name,
        }),
        gcx,
    );
    let receiver = match op {
        Operation::Unary(_) => ty,
        Operation::Assign(_) => Ty::new(TyKind::Reference(ty), gcx),
        Operation::Binary(_) => ty,
    };
    let signature = definition.signature;
    let count = if matches!(op, Operation::Unary(_)) {
        1
    } else {
        2
    };
    if signature.abi.is_some()
        || signature.is_variadic
        || signature.inputs.len() != count
        || signature.inputs[0].ty != receiver
        || (count == 2 && signature.inputs[1].ty != ty)
        || signature
            .inputs
            .iter()
            .any(|input| input.label.is_some() || input.default_provider.is_some())
        || signature.output
            != if matches!(op, Operation::Assign(_)) {
                gcx.types.void
            } else {
                ty
            }
    {
        return Err("invalid primitive operator signature");
    }
    Ok(())
}

pub(crate) fn build_body<'ctx>(
    gcx: Gcx<'ctx>,
    instance: Instance<'ctx>,
) -> CompileResult<Body<'ctx>> {
    let owner = instance.def_id();
    let definition = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&owner)
        .cloned()
        .ok_or(ReportedError)?;
    let span = definition.span;
    let error = |message: &str| {
        gcx.dcx().emit_error(message.into(), Some(span));
        ReportedError
    };
    validate_declaration(gcx, &definition).map_err(error)?;
    let SyntheticDefinitionKind::PrimitiveOperator(item) = definition.kind else {
        return Err(error("incorrect primitive operator definition kind"));
    };
    let [GenericArgument::Type(ty)] = &instance.args[..] else {
        return Err(error("primitive operator requires one concrete type"));
    };
    let ty = normalize_post_monomorphization(gcx, *ty);
    if !supports(gcx, ty, item) {
        return Err(error("unsupported primitive operator instance"));
    }
    let op = operation(item).expect("validated operator item");
    let output = if matches!(op, Operation::Assign(_)) {
        gcx.types.void
    } else {
        ty
    };
    let mut locals = IndexVec::new();
    let return_local = locals.push(LocalDecl {
        ty: output,
        kind: LocalKind::Return,
        mutable: true,
        name: None,
        span,
    });
    let receiver_ty = match op {
        Operation::Unary(_) => ty,
        Operation::Assign(_) => Ty::new(TyKind::Reference(ty), gcx),
        Operation::Binary(_) => ty,
    };
    let receiver = locals.push(LocalDecl {
        ty: receiver_ty,
        kind: LocalKind::Param,
        mutable: false,
        name: Some(gcx.intern_symbol("self")),
        span,
    });
    let mut receiver_place = Place::from_local(receiver);
    if matches!(op, Operation::Assign(_)) {
        receiver_place.projection.push(PlaceElem::Deref);
    }
    let value = if let Operation::Unary(op) = op {
        Rvalue::UnaryOp {
            op,
            operand: Operand::Copy(receiver_place.clone()),
        }
    } else {
        let rhs = locals.push(LocalDecl {
            ty,
            kind: LocalKind::Param,
            mutable: false,
            name: Some(gcx.intern_symbol("rhs")),
            span,
        });
        let rhs_place = Place::from_local(rhs);
        let (Operation::Binary(op) | Operation::Assign(op)) = op else {
            unreachable!()
        };
        Rvalue::BinaryOp {
            op,
            lhs: Operand::Copy(receiver_place.clone()),
            rhs: Operand::Copy(rhs_place),
        }
    };
    let destination = if matches!(op, Operation::Assign(_)) {
        receiver_place
    } else {
        Place::from_local(return_local)
    };
    let checked = if gcx.config.overflow_checks && gcx.std_package_index().is_some() {
        match (&value, ty.kind()) {
            (
                Rvalue::UnaryOp {
                    op: UnaryOperator::Negate,
                    ..
                },
                TyKind::Int(_),
            ) => Some("__intrinsic_checked_neg"),
            (Rvalue::BinaryOp { op, .. }, TyKind::Int(_) | TyKind::UInt(_)) => match op {
                BinaryOperator::Add => Some("__intrinsic_checked_add"),
                BinaryOperator::Sub => Some("__intrinsic_checked_sub"),
                BinaryOperator::Mul => Some("__intrinsic_checked_mul"),
                BinaryOperator::Div => Some("__intrinsic_checked_div"),
                BinaryOperator::Rem => Some("__intrinsic_checked_rem"),
                BinaryOperator::BitShl => Some("__intrinsic_checked_shl"),
                BinaryOperator::BitShr => Some("__intrinsic_checked_shr"),
                _ => None,
            },
            _ => None,
        }
    } else {
        None
    };
    let mut basic_blocks = IndexVec::new();
    let (value, pending_call) = if let Some(name) = checked {
        let id =
            crate::mir::optimize::async_transform::find_std_function(gcx, "intrinsic", name, span)?;
        let arguments = gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(ty)]);
        let function_ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            gcx,
            gcx.get_type(id),
            arguments,
        );
        let operands = match value {
            Rvalue::BinaryOp { lhs, rhs, .. } => vec![lhs, rhs],
            Rvalue::UnaryOp { operand, .. } => vec![operand],
            _ => unreachable!(),
        };
        let result = locals.push(LocalDecl {
            ty,
            kind: LocalKind::Temp,
            mutable: true,
            name: None,
            span,
        });
        (
            Rvalue::Use(Operand::Copy(Place::from_local(result))),
            Some((id, arguments, function_ty, operands, result)),
        )
    } else {
        (value, None)
    };
    let mut statements = vec![Statement {
        kind: StatementKind::Assign(destination, value),
        span,
    }];
    if matches!(op, Operation::Assign(_)) {
        statements.push(Statement {
            kind: StatementKind::Assign(
                Place::from_local(return_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: gcx.types.void,
                    value: ConstantKind::Unit,
                })),
            ),
            span,
        });
    }
    let finish = basic_blocks.push(BasicBlockData {
        note: Some("profile-local primitive operator".into()),
        statements,
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });
    let start_block = if let Some((id, args, function_ty, operands, result)) = pending_call {
        // Preserve caller cleanup when checked arithmetic panics. These
        // primitive arguments have no cleanup obligations of their own.
        let unwind = basic_blocks.push(BasicBlockData {
            note: Some("primitive operator unwind".into()),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::ResumeUnwind,
                span,
            }),
        });
        basic_blocks.push(BasicBlockData {
            note: Some("checked primitive operator".into()),
            statements: vec![],
            terminator: Some(Terminator {
                kind: TerminatorKind::Call {
                    func: Operand::Constant(Constant {
                        ty: function_ty,
                        value: ConstantKind::Function(id, args, function_ty),
                    }),
                    args: operands,
                    destination: Place::from_local(result),
                    target: finish,
                    unwind: CallUnwindAction::Cleanup(unwind),
                },
                span,
            }),
        })
    } else {
        finish
    };
    let body = Body {
        escape_locals: Vec::new(),

        owner,
        source_scopes: Body::initial_source_scopes(owner),
        locals,
        basic_blocks,
        start_block,
        return_local,
        phase: MirPhase::CfgClean,
        is_async: false,
    };
    Ok(body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::test_support::with_test_gcx;

    #[test]
    fn operator_eligibility_does_not_forward_references_or_resolve_abstract_types() {
        with_test_gcx(|gcx| {
            assert!(supports(gcx, gcx.types.bool, StdItem::BitAnd));
            assert!(supports(gcx, gcx.types.float64, StdItem::Rem));
            assert!(!supports(gcx, gcx.types.float64, StdItem::Shl));
            assert!(!supports(gcx, gcx.types.bool, StdItem::Add));
            let reference = Ty::new(TyKind::Reference(gcx.types.int32), gcx);
            assert!(!supports(gcx, reference, StdItem::Add));
            let abstract_ty = Ty::new(
                TyKind::Parameter(GenericParameter {
                    index: 0,
                    name: gcx.intern_symbol("T"),
                }),
                gcx,
            );
            assert!(!supports(gcx, abstract_ty, StdItem::Add));
        });
    }
}
