//! Prove generic defaults before source-only receiver distinctions disappear.
//! The facts constrain class adoption, not ordinary value-type conformances.
use crate::{
    compile::context::Gcx, error::CompileResult, mir::Body, sema::models::ClassDefaultContract,
};

pub(crate) fn collect<'ctx, 'a>(
    gcx: Gcx<'ctx>,
    bodies: impl IntoIterator<Item = &'a Body<'ctx>>,
) -> CompileResult<()>
where
    'ctx: 'a,
{
    for body in bodies {
        if super::analysis::class_self::conditional_receiver_owner(gcx, body.owner).is_some() {
            let preserves_dynamic_self =
                super::analysis::class_self::default_preserves_dynamic_self(gcx, body);
            gcx.with_session_type_database(|database| {
                database.def_to_class_default_contract.insert(
                    body.owner,
                    ClassDefaultContract {
                        preserves_dynamic_self,
                    },
                );
            });
        }
    }
    // Source type checking can provisionally select bodies before their proofs
    // exist. Never reuse that provisional answer after proof publication.
    gcx.with_session_type_database(|database| database.witness_cache.clear());
    crate::sema::impl_engine::validate_class_default_adoptions(gcx)
}
