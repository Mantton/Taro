use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::models::{
        Const, ConstKind, GenericArgument, GenericArguments, GenericParameter,
        GenericParameterDefinition, GenericParameterDefinitionKind, Generics, Ty, TyKind,
    },
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};
use std::marker::PhantomData;

pub struct GenericsBuilder<'ctx> {
    _1: PhantomData<&'ctx ()>,
}

impl<'ctx> GenericsBuilder<'ctx> {
    pub fn identity_for_item(gcx: GlobalContext<'ctx>, id: DefinitionID) -> GenericArguments<'ctx> {
        let lower_ctx = DefTyLoweringCtx::new(id, gcx);
        Self::for_item(gcx, id, |param, _| match &param.kind {
            GenericParameterDefinitionKind::Type { .. } => {
                let p = GenericParameter {
                    index: param.index,
                    name: param.name.clone(),
                };
                let ty = Ty::new(TyKind::Parameter(p), gcx);
                GenericArgument::Type(ty)
            }
            GenericParameterDefinitionKind::Const { ty, .. } => {
                let p = GenericParameter {
                    index: param.index,
                    name: param.name.clone(),
                };
                let ty = lower_ctx.lowerer().lower_type(ty);
                GenericArgument::Const(Const {
                    ty,
                    kind: ConstKind::Param(p),
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
