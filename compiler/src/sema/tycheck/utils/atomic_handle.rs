//! Atomic class snapshots store one object address. Erased interface values
//! also carry witness metadata and cannot use this representation.
use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::StdItem,
    sema::{
        models::{Ty, TyKind},
        tycheck::{
            utils::{normalize_aliases, unresolved::storage_needs_substitution},
            visit::{TypeSuperVisitable, TypeVisitable, TypeVisitor},
        },
    },
    span::Span,
};

pub(crate) fn validate<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, span: Span) -> CompileResult<()> {
    struct Check<'ctx> {
        gcx: Gcx<'ctx>,
        invalid: bool,
    }
    impl<'ctx> TypeVisitor<'ctx> for Check<'ctx> {
        fn visit_ty(&mut self, ty: Ty<'ctx>) -> bool {
            let ty = normalize_aliases(self.gcx, ty);
            if let TyKind::Adt(def, args) = ty.kind()
                && self.gcx.std_item_def(StdItem::AtomicHandle) == Some(def.id)
                && let Some(class) = args.first().and_then(|arg| arg.ty())
            {
                let class = normalize_aliases(self.gcx, class);
                if !class.is_error()
                    && (matches!(class.kind(), TyKind::BoxedExistential { .. })
                        || (!storage_needs_substitution(self.gcx, class)
                            && !self.gcx.is_class_type(class)))
                {
                    self.invalid = true;
                    return true;
                }
            }
            ty.super_visit_with(self)
        }
    }
    let mut check = Check {
        gcx,
        invalid: false,
    };
    ty.visit_with(&mut check);
    if check.invalid {
        gcx.dcx().emit_error("atomic.Handle requires a concrete class type; erased interface values carry additional metadata".into(), Some(span));
        return Err(ReportedError);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn class_snapshot_slots_reject_erased_interface_types() {
        let source = r#"
interface AnyObject {}
interface Object: AnyObject {}
struct Slot[C: AnyObject] { value: *uint8 }
func inspect(_ slot: Slot[any Object]) {}
func main() {}
"#;
        let errors = crate::test_support::analyze_language_item_script(
            source,
            false,
            &[
                (crate::hir::StdItem::AnyObject, "AnyObject"),
                (crate::hir::StdItem::AtomicHandle, "Slot"),
            ],
        );
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("concrete class type")),
            "{errors:?}"
        );
    }
}

#[cfg(test)]
mod generic_erasure_tests {
    #[test]
    fn erased_generic_headers_are_rejected_before_instantiation() {
        let source = r#"
interface AnyObject {}
interface Object[T]: AnyObject {}
struct Slot[C: AnyObject] { value: *uint8 }
func inspect[T](_ slot: Slot[any Object[T]]) {}
func main() {}
"#;
        let errors = crate::test_support::analyze_language_item_script(
            source,
            false,
            &[
                (crate::hir::StdItem::AnyObject, "AnyObject"),
                (crate::hir::StdItem::AtomicHandle, "Slot"),
            ],
        );
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("concrete class type")),
            "{errors:?}"
        );
    }
}

#[cfg(test)]
mod inferred_erasure_tests {
    #[test]
    fn inferred_generic_result_rejects_erasure_during_type_checking() {
        let source = r#"
interface AnyObject {}
interface Object: AnyObject {}
struct Slot[C: AnyObject] { value: *uint8 }
func make[T: AnyObject]() -> Slot[T] { Slot[T] { value: nil } }
func main() { var slot = make[any Object]() }
"#;
        let errors = crate::test_support::analyze_language_item_script(
            source,
            false,
            &[
                (crate::hir::StdItem::AnyObject, "AnyObject"),
                (crate::hir::StdItem::AtomicHandle, "Slot"),
            ],
        );
        assert!(
            errors
                .iter()
                .any(|d| d.message.contains("concrete class type")),
            "{errors:?}"
        );
    }
}
