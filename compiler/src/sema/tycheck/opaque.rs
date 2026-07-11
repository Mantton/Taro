use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID},
    sema::{
        models::{AliasKind, GenericArgument, Ty, TyKind},
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            utils::{generics::GenericsBuilder, instantiate::instantiate_ty_with_args},
        },
    },
};
use rustc_hash::FxHashSet;

pub(crate) fn opaque_return_bounds(node: &hir::Function) -> Option<&[hir::PathNode]> {
    let output = node.signature.prototype.output.as_deref()?;
    let hir::TypeKind::ImplTrait { interfaces } = &output.kind else {
        return None;
    };
    Some(interfaces)
}

pub(crate) fn opaque_return_is_supported(
    node: &hir::Function,
    context: hir::FunctionContext,
) -> bool {
    node.block.is_some()
        && !matches!(
            context,
            hir::FunctionContext::Assoc(hir::AssocContext::Interface(_))
        )
}

pub(crate) fn opaque_return_ty<'ctx>(gcx: Gcx<'ctx>, owner: DefinitionID) -> Ty<'ctx> {
    let args = GenericsBuilder::identity_for_item(gcx, owner);
    Ty::new(
        TyKind::Alias {
            kind: AliasKind::Opaque,
            def_id: owner,
            args,
        },
        gcx,
    )
}

pub(crate) fn contains_opaque_owner_through_hidden<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    owner: DefinitionID,
) -> bool {
    fn visit<'ctx>(
        gcx: Gcx<'ctx>,
        ty: Ty<'ctx>,
        owner: DefinitionID,
        visiting: &mut FxHashSet<DefinitionID>,
    ) -> bool {
        let visit_arg = |arg: &GenericArgument<'ctx>, visiting: &mut FxHashSet<DefinitionID>| {
            let ty = match arg {
                GenericArgument::Type(ty) => *ty,
                GenericArgument::Const(c) => c.ty,
            };
            visit(gcx, ty, owner, visiting)
        };
        match ty.kind() {
            TyKind::Alias { kind, def_id, args } => {
                if kind == AliasKind::Opaque && def_id == owner {
                    return true;
                }
                if args.iter().any(|arg| visit_arg(arg, visiting)) {
                    return true;
                }
                if kind != AliasKind::Opaque || !visiting.insert(def_id) {
                    return false;
                }
                let result = gcx.try_get_alias_type(def_id).is_some_and(|hidden| {
                    let hidden = instantiate_ty_with_args(gcx, hidden, args);
                    visit(gcx, hidden, owner, visiting)
                });
                visiting.remove(&def_id);
                result
            }
            TyKind::Adt(_, args) => args.iter().any(|arg| visit_arg(arg, visiting)),
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                visit(gcx, inner, owner, visiting)
            }
            TyKind::Array { element, len } => {
                visit(gcx, element, owner, visiting) || visit(gcx, len.ty, owner, visiting)
            }
            TyKind::Tuple(items) => items.iter().any(|ty| visit(gcx, *ty, owner, visiting)),
            TyKind::FnPointer { inputs, output } => {
                inputs.iter().any(|ty| visit(gcx, *ty, owner, visiting))
                    || visit(gcx, output, owner, visiting)
            }
            TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|interface| {
                interface
                    .arguments
                    .iter()
                    .any(|arg| visit_arg(arg, visiting))
                    || interface
                        .bindings
                        .iter()
                        .any(|binding| visit(gcx, binding.ty, owner, visiting))
            }),
            TyKind::Closure {
                captured_generics,
                inputs,
                output,
                ..
            } => {
                captured_generics.iter().any(|arg| visit_arg(arg, visiting))
                    || inputs.iter().any(|ty| visit(gcx, *ty, owner, visiting))
                    || visit(gcx, output, owner, visiting)
            }
            _ => false,
        }
    }

    visit(gcx, ty, owner, &mut FxHashSet::default())
}

pub(crate) fn reveal_opaque_aliases<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
    struct RevealOpaqueFolder<'ctx> {
        gcx: Gcx<'ctx>,
        in_progress: FxHashSet<DefinitionID>,
    }

    impl<'ctx> TypeFolder<'ctx> for RevealOpaqueFolder<'ctx> {
        fn gcx(&self) -> Gcx<'ctx> {
            self.gcx
        }

        fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
            let TyKind::Alias {
                kind: AliasKind::Opaque,
                def_id,
                args,
            } = ty.kind()
            else {
                return ty.super_fold_with(self);
            };
            if !self.in_progress.insert(def_id) {
                return self.gcx.types.error;
            }
            let hidden = self
                .gcx
                .try_get_alias_type(def_id)
                .unwrap_or(self.gcx.types.error);
            let hidden = instantiate_ty_with_args(self.gcx, hidden, args).fold_with(self);
            self.in_progress.remove(&def_id);
            hidden
        }
    }

    ty.fold_with(&mut RevealOpaqueFolder {
        gcx,
        in_progress: FxHashSet::default(),
    })
}

#[cfg(test)]
mod tests {
    use crate::sema::tycheck::test_support::analyze_script_diagnostics;

    const PRELUDE: &str = r#"
interface Named {
    func name(&self) -> int32
}

struct First {}
impl Named for First {
    func name(&self) -> int32 { 1 }
}

struct Second {}
impl Named for Second {
    func name(&self) -> int32 { 2 }
}
"#;

    fn diagnostics_for(body: &str) -> Vec<crate::diagnostics::DiagnosticRecord> {
        analyze_script_diagnostics(&format!("{PRELUDE}\n{body}"))
    }

    #[test]
    fn opaque_returns_support_generics_and_same_identity_branches() {
        let diagnostics = diagnostics_for(
            r#"
func preserve[T: Named](_ value: T) -> some Named { value }

func chooseSame(_ flag: bool) -> some Named {
    if flag { return preserve(First {}) }
    preserve(First {})
}

func accept[T: Named](_ value: T) {}

func main() {
    accept(chooseSame(true))
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn opaque_return_paths_must_have_one_hidden_type() {
        let diagnostics = diagnostics_for(
            r#"
func choose(_ flag: bool) -> some Named {
    if flag { return First {} }
    Second {}
}

func main() {}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("opaque return type must resolve to one concrete type")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn opaque_identity_is_owned_by_the_defining_function() {
        let diagnostics = diagnostics_for(
            r#"
func first() -> some Named { First {} }
func second() -> some Named { First {} }

func choose(_ flag: bool) -> some Named {
    if flag { return first() }
    second()
}

func main() {}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("opaque return type must resolve to one concrete type")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn opaque_hidden_type_must_satisfy_every_bound() {
        let diagnostics = diagnostics_for(
            r#"
func invalid() -> some Named { 1 }
func main() {}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("does not conform to interface 'Named'")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn unconstrained_generic_cannot_be_an_opaque_hidden_type() {
        let diagnostics = diagnostics_for(
            r#"
func invalid[T](_ value: T) -> some Named { value }
func main() {}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("type 'T' does not conform to interface 'Named'")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn opaque_return_cannot_recursively_define_itself() {
        let diagnostics = diagnostics_for(
            r#"
func recursive() -> some Named { recursive() }
func main() {}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("opaque return type recursively refers to itself")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn mutually_recursive_opaque_returns_are_rejected() {
        let diagnostics = diagnostics_for(
            r#"
func first() -> some Named { second() }
func second() -> some Named { first() }
func main() {}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("opaque return type recursively refers to itself")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn callers_cannot_treat_opaque_return_as_hidden_type() {
        let diagnostics = diagnostics_for(
            r#"
func makeFirst() -> some Named { First {} }

func main() {
    let _: First = makeFirst()
}
"#,
        );
        assert!(
            diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("expected First, found some Named")),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn some_is_rejected_outside_concrete_return_positions() {
        for source in [
            "func consume(_ value: some Named) {}\nfunc main() {}",
            "type Hidden = some Named\nfunc main() {}",
            "interface Factory {\nfunc make() -> some Named\n}\nfunc main() {}",
            "struct Holder { value: some Named }\nfunc main() {}",
            "func main() { let value: some Named = First {} }",
            "func main() { let factory = || -> some Named { First {} } }",
            "func nested() -> (some Named, int32) { (First {}, 1) }\nfunc main() {}",
        ] {
            let diagnostics = diagnostics_for(source);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains("'some Interface'")),
                "source:\n{source}\n{diagnostics:#?}"
            );
        }
    }
}
