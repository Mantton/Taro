use crate::{
    compile::context::GlobalContext,
    hir::{self, DefinitionID},
    sema::models::{
        Const, ConstKind, GenericArgument, GenericArguments, GenericParameter,
        GenericParameterDefinition, GenericParameterDefinitionKind, Generics, Ty, TyKind,
    },
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    span::Span,
};
use std::marker::PhantomData;

pub fn generic_parameter_marker(param: &GenericParameterDefinition) -> GenericParameter {
    GenericParameter {
        index: param.index,
        name: param.name,
    }
}

pub fn expected_const_param_ty<'ctx>(
    gcx: GlobalContext<'ctx>,
    lowerer: &dyn TypeLowerer<'ctx>,
    param: &GenericParameterDefinition,
) -> Option<Ty<'ctx>> {
    let GenericParameterDefinitionKind::Const { ty, .. } = &param.kind else {
        return None;
    };

    Some(
        gcx.try_generic_const_param_ty(param.id)
            .unwrap_or_else(|| lowerer.lower_type(ty)),
    )
}

pub fn const_param_from_type_arg<'ctx>(
    gcx: GlobalContext<'ctx>,
    lowerer: &dyn TypeLowerer<'ctx>,
    ty: &hir::Type,
) -> Option<Const<'ctx>> {
    let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) = &ty.kind else {
        return None;
    };

    let hir::Resolution::Definition(param_id, hir::DefinitionKind::ConstParameter) =
        path.resolution
    else {
        return None;
    };

    let owner = gcx.definition_parent(param_id)?;
    let generics = gcx.generics_of(owner);
    let def = generics.parameters.iter().find(|p| p.id == param_id)?;
    let ty = expected_const_param_ty(gcx, lowerer, def)?;

    Some(Const {
        ty,
        kind: ConstKind::Param(generic_parameter_marker(def)),
    })
}

pub fn const_arg_ty_mismatches<'ctx>(
    gcx: GlobalContext<'ctx>,
    actual_ty: Ty<'ctx>,
    expected_ty: Ty<'ctx>,
) -> bool {
    actual_ty != expected_ty && actual_ty != gcx.types.error && expected_ty != gcx.types.error
}

pub fn emit_const_arg_type_mismatch<'ctx>(
    gcx: GlobalContext<'ctx>,
    expected_ty: Ty<'ctx>,
    span: Span,
) {
    let message = format!(
        "const argument does not match parameter type '{}'",
        expected_ty.format(gcx)
    );
    gcx.dcx().emit_error(message, Some(span));
}

pub fn error_generic_argument<'ctx>(
    gcx: GlobalContext<'ctx>,
    lowerer: &dyn TypeLowerer<'ctx>,
    param: &GenericParameterDefinition,
) -> GenericArgument<'ctx> {
    match &param.kind {
        GenericParameterDefinitionKind::Type { .. } => GenericArgument::Type(gcx.types.error),
        GenericParameterDefinitionKind::Const { .. } => {
            GenericArgument::Const(lowerer.error_const())
        }
    }
}

pub struct GenericsBuilder<'ctx> {
    _1: PhantomData<&'ctx ()>,
}

impl<'ctx> GenericsBuilder<'ctx> {
    pub fn identity_for_item(gcx: GlobalContext<'ctx>, id: DefinitionID) -> GenericArguments<'ctx> {
        let lower_ctx = DefTyLoweringCtx::new(id, gcx);
        Self::for_item(gcx, id, |param, _| match &param.kind {
            GenericParameterDefinitionKind::Type { .. } => {
                let ty = Ty::new(TyKind::Parameter(generic_parameter_marker(param)), gcx);
                GenericArgument::Type(ty)
            }
            GenericParameterDefinitionKind::Const { .. } => {
                let ty = expected_const_param_ty(gcx, lower_ctx.lowerer(), param)
                    .unwrap_or(gcx.types.error);
                GenericArgument::Const(Const {
                    ty,
                    kind: ConstKind::Param(generic_parameter_marker(param)),
                })
            }
        })
    }
    pub fn for_item<F>(
        gcx: GlobalContext<'ctx>,
        id: DefinitionID,
        mut mk_kind: F,
    ) -> GenericArguments<'ctx>
    where
        F: FnMut(&GenericParameterDefinition, &[GenericArgument<'ctx>]) -> GenericArgument<'ctx>,
    {
        let generics = gcx.generics_of(id);
        let mut arguments = vec![];
        Self::fill_item(&mut arguments, gcx, &generics, &mut mk_kind);
        let args = gcx.store.interners.intern_generic_args(arguments);
        args
    }

    pub fn fill_item<F>(
        arguments: &mut Vec<GenericArgument<'ctx>>,
        gcx: GlobalContext<'ctx>,
        defintion: &Generics,
        mk: &mut F,
    ) where
        F: FnMut(&GenericParameterDefinition, &[GenericArgument<'ctx>]) -> GenericArgument<'ctx>,
    {
        if let Some(id) = defintion.parent {
            let parent_def = gcx.generics_of(id);
            Self::fill_item(arguments, gcx, parent_def, mk);
        }

        Self::fill_single(arguments, defintion, mk)
    }
    pub fn fill_single<F>(
        arguments: &mut Vec<GenericArgument<'ctx>>,
        defintion: &Generics,
        mk: &mut F,
    ) where
        F: FnMut(&GenericParameterDefinition, &[GenericArgument<'ctx>]) -> GenericArgument<'ctx>,
    {
        for param in &defintion.parameters {
            let kind = mk(param, arguments);
            assert_eq!(
                param.index as usize,
                arguments.len(),
                "param | arg len mismtach"
            );
            arguments.push(kind);
        }
    }
}
