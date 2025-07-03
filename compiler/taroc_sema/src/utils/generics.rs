use std::marker::PhantomData;
use taroc_hir::DefinitionID;

use crate::{
    GlobalContext,
    ty::{
        self, GenericArgument, GenericArguments, GenericParameter, GenericParameterDefinition,
        TyKind,
    },
};

pub struct GenericsBuilder<'ctx> {
    _1: PhantomData<&'ctx ()>,
}

impl<'ctx> GenericsBuilder<'ctx> {
    pub fn identity_for_item(gcx: GlobalContext<'ctx>, id: DefinitionID) -> GenericArguments<'ctx> {
        Self::for_item(gcx, id, |param, _| match param.kind {
            crate::ty::GenericParameterDefinitionKind::Type { .. } => {
                let p = GenericParameter {
                    index: param.index,
                    name: param.name,
                };
                let ty = gcx.mk_ty(TyKind::Parameter(p));

                GenericArgument::Type(ty)
            }
            crate::ty::GenericParameterDefinitionKind::Const { .. } => {
                GenericArgument::Const(0) // TODO!
            }
        })
    }
    pub fn for_item<F>(
        gcx: GlobalContext<'ctx>,
        id: DefinitionID,
        mut mk_kind: F,
    ) -> GenericArguments<'ctx>
    where
        F: FnMut(&GenericParameterDefinition, &[GenericArgument]) -> GenericArgument<'ctx>,
    {
        let generics = gcx.generics_of(id);
        let mut arguments = vec![];
        Self::fill_item(&mut arguments, gcx, &generics, &mut mk_kind);
        let args = gcx.store.interners.intern_generic_args(&arguments);
        args
    }

    pub fn fill_item<F>(
        arguments: &mut Vec<GenericArgument<'ctx>>,
        gcx: GlobalContext<'ctx>,
        defintion: &ty::Generics,
        mk: &mut F,
    ) where
        F: FnMut(&ty::GenericParameterDefinition, &[GenericArgument]) -> GenericArgument<'ctx>,
    {
        if let Some(id) = defintion.parent {
            let parent_def = gcx.generics_of(id);
            Self::fill_item(arguments, gcx, parent_def, mk);
        }

        Self::fill_single(arguments, defintion, mk)
    }
    pub fn fill_single<F>(
        arguments: &mut Vec<GenericArgument<'ctx>>,
        defintion: &ty::Generics,
        mk: &mut F,
    ) where
        F: FnMut(&ty::GenericParameterDefinition, &[GenericArgument]) -> GenericArgument<'ctx>,
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
