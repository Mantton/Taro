//! Advisory checks on source MIR, before optimization can erase accidental
//! copies. NoCopy does not alter typing, initialization, or runtime semantics.
use crate::{
    compile::context::Gcx,
    hir::KnownAttribute,
    mir::{
        Body, CastKind, ConstantKind, LocalKind, Operand, Place, PlaceElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    sema::{
        models::{AdtKind, EnumVariantKind, Ty, TyKind},
        tycheck::utils::{instantiate::instantiate_ty_with_args, normalize_aliases},
    },
    span::Span,
};
use rustc_hash::FxHashSet;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Finding {
    pub span: Span,
    pub message: String,
}

/// Inline aggregates propagate @NoCopy. Indirection copies a reference or
/// handle, not its target, so raw pointers, references and class handles stop.
pub(crate) fn type_contains_no_copy<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> bool {
    let mut seen = FxHashSet::default();
    contains_no_copy(gcx, ty, &mut seen)
}

fn contains_no_copy<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>, seen: &mut FxHashSet<Ty<'ctx>>) -> bool {
    let ty = normalize_aliases(gcx, ty);
    if !seen.insert(ty) {
        return false;
    }
    match ty.kind() {
        TyKind::Adt(definition, _)
            if gcx
                .attributes_of(definition.id)
                .iter()
                .any(|attribute| attribute.as_known(gcx) == Some(KnownAttribute::NoCopy)) =>
        {
            true
        }
        TyKind::Adt(..) if gcx.is_class_type(ty) => false,
        TyKind::Adt(definition, args) => match definition.kind {
            AdtKind::Struct => {
                gcx.get_struct_definition(definition.id)
                    .fields
                    .iter()
                    .any(|field| {
                        contains_no_copy(gcx, instantiate_ty_with_args(gcx, field.ty, args), seen)
                    })
            }
            AdtKind::Enum => {
                gcx.get_enum_definition(definition.id)
                    .variants
                    .iter()
                    .any(|variant| match variant.kind {
                        EnumVariantKind::Unit => false,
                        EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => {
                            fields.iter().any(|field| {
                                contains_no_copy(
                                    gcx,
                                    instantiate_ty_with_args(gcx, field.ty, args),
                                    seen,
                                )
                            })
                        }
                    })
            }
        },
        TyKind::Tuple(elements) => elements.iter().any(|ty| contains_no_copy(gcx, *ty, seen)),
        TyKind::Array { element, .. } => contains_no_copy(gcx, element, seen),
        _ => false,
    }
}

pub(crate) fn check_body<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> Vec<Finding> {
    // Address defaults are compiler-generated forwarding bodies. Diagnose
    // copies where users index or assign, not hidden getter/setter parameters.
    if gcx
        .native_subscript_for_accessor(body.owner)
        .is_some_and(|(_, entry)| {
            (entry.getter == Some(body.owner) && entry.getter_is_default)
                || (entry.setter == Some(body.owner) && entry.setter_is_default)
        })
    {
        return Vec::new();
    }
    let address_results: FxHashSet<_> = body
        .basic_blocks
        .iter()
        .filter_map(|block| {
            let TerminatorKind::Call {
                func: Operand::Constant(constant),
                destination,
                ..
            } = &block.terminator.as_ref()?.kind
            else {
                return None;
            };
            let ConstantKind::Function(definition, ..) = constant.value else {
                return None;
            };
            (destination.projection.is_empty()
                && gcx
                    .native_subscript_for_accessor(definition)
                    .is_some_and(|(_, entry)| entry.address == Some(definition)))
            .then_some(destination.local)
        })
        .collect();
    let mut findings = Vec::new();
    let marked = |ty| contains_no_copy(gcx, ty, &mut FxHashSet::default());
    for local in &body.locals {
        if local.kind == LocalKind::Param
            && marked(local.ty)
            && let Some(name) = local.name.filter(|name| !name.as_str().starts_with('$'))
        {
            findings.push(Finding {
                span: local.span,
                message: format!("@NoCopy parameter '{name}' is passed by value; use a reference"),
            });
        }
    }
    let copy = |place: &Place<'ctx>, span, findings: &mut Vec<Finding>| {
        let local = &body.locals[place.local];
        // Desugared loop storage is compiler-private; report the iteration
        // operation once instead of presenting its hidden bindings as user code.
        if local
            .name
            .is_some_and(|name| name.as_str().starts_with('$'))
        {
            return;
        }
        // Fresh call/aggregate results can initialize a value. A named value
        // or a value loaded through a named reference is an actual copy site.
        let dereferenced = place
            .projection
            .iter()
            .any(|projection| matches!(projection, PlaceElem::Deref));
        if !(matches!(local.kind, LocalKind::User | LocalKind::Param) || dereferenced)
            || !marked(body.place_ty(gcx, place))
        {
            return;
        }
        if dereferenced && address_results.contains(&place.local) {
            findings.push(Finding {
                span,
                message: "indexing copies a @NoCopy element; take its reference instead".into(),
            });
            return;
        }
        let captured_name = (local.kind == LocalKind::Param
            && local.name.is_some_and(|name| name.as_str() == "self"))
        .then(|| gcx.get_closure_captures(body.owner))
        .flatten()
        .and_then(|captures| {
            let field = place
                .projection
                .iter()
                .find_map(|projection| match projection {
                    PlaceElem::Field(index, _) => Some(*index),
                    _ => None,
                })?;
            captures
                .captures
                .iter()
                .find(|capture| capture.field_index == field)
                .map(|capture| capture.name)
        });
        let name = captured_name
            .as_ref()
            .or(local.name.as_ref())
            .map(|name| name.as_str())
            .unwrap_or("value");
        findings.push(Finding {
            span,
            message: format!("copy of @NoCopy value '{name}'; use a reference"),
        });
    };
    for block in &body.basic_blocks {
        for statement in &block.statements {
            let StatementKind::Assign(_, value) = &statement.kind else {
                continue;
            };
            match value {
                Rvalue::CopyValue { source } => copy(source, statement.span, &mut findings),
                Rvalue::Cast {
                    operand,
                    kind: CastKind::BoxExistential,
                    ..
                } if marked(body.operand_ty(gcx, operand)) => {
                    findings.push(Finding {
                        span: statement.span,
                        message:
                            "boxing a @NoCopy value hides its annotation; box a reference instead"
                                .into(),
                    });
                }
                Rvalue::Repeat { operand, count, .. }
                    if *count > 1 && marked(body.operand_ty(gcx, operand)) =>
                {
                    findings.push(Finding {
                        span: statement.span,
                        message:
                            "array repetition copies a @NoCopy value; store references instead"
                                .into(),
                    });
                }
                _ => value.for_each_operand(|operand| {
                    if let Some(place) = operand.place() {
                        copy(place, statement.span, &mut findings);
                    }
                }),
            }
        }
        let Some(terminator) = &block.terminator else {
            continue;
        };
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            for operand in args {
                if let Some(place) = operand.place() {
                    copy(place, terminator.span, &mut findings);
                }
            }
            if let Operand::Constant(constant) = func
                && let ConstantKind::Function(definition, ..) = constant.value
                && marked(body.place_ty(gcx, destination))
            {
                let native_get = gcx
                    .native_subscript_for_accessor(definition)
                    .is_some_and(|(_, entry)| entry.getter == Some(definition));
                let iteration = gcx.definition_ident(definition).symbol.as_str() == "next";
                if native_get || iteration {
                    findings.push(Finding {
                        span: terminator.span,
                        message: if iteration {
                            "iteration copies a @NoCopy element; iterate references instead".into()
                        } else {
                            "indexing copies a @NoCopy element; take its reference instead".into()
                        },
                    });
                }
            }
        }
    }
    findings.sort_by_key(|finding| {
        (
            finding.span.file,
            finding.span.start.line,
            finding.span.start.offset,
            finding.message.clone(),
        )
    });
    findings.dedup();
    findings
}

#[cfg(test)]
mod tests {
    fn findings(source: &str) -> Vec<String> {
        crate::test_support::analyze_script_built_mir(source, |bodies, gcx| {
            bodies
                .iter()
                .flat_map(|body| super::check_body(gcx, body))
                .map(|finding| finding.message)
                .collect()
        })
    }
    #[test]
    fn address_subscripts_report_an_index_copy_instead_of_a_hidden_value() {
        let messages = findings(&format!(
            r#"{TYPES}
struct Shelf {{ value: Lock }}
extend &Shelf {{
    subscript(index: int32) -> Lock {{ address {{ &self.value }} }}
}}
func main() {{
    var shelf = Shelf {{ value: Lock {{ value: 1 }} }}
    copied := shelf[0]
    var _ = &copied
}}
"#
        ));
        assert!(
            messages.iter().any(|m| m.contains("indexing copies")),
            "{messages:?}"
        );
        assert!(
            !messages.iter().any(|m| m.contains("value 'value'")),
            "{messages:?}"
        );
    }

    const TYPES: &str = r#"
@NoCopy
struct Lock { value: int32 }
struct Wrapper[T] { value: T }
"#;

    #[test]
    fn closure_capture_names_the_captured_local() {
        let messages = findings(&format!(
            r#"{TYPES}
func main() {{
    var m = Lock {{ value: 1 }}
    f := () => m
    var _ = f()
}}
"#
        ));
        assert!(
            messages.iter().any(|message| message.contains("'m'")),
            "{messages:?}"
        );
        let messages = findings(&format!(
            r#"{TYPES}
func main() {{
    var m = Lock {{ value: 1 }}
    f := () => {{
        var wrapped = Wrapper[Lock] {{ value: m }}
        copy := wrapped.value
        return copy
    }}
    var _ = f()
}}
"#
        ));
        assert!(
            messages.iter().any(|message| message.contains("'wrapped'")),
            "{messages:?}"
        );
        assert!(
            !messages.iter().any(|message| message.contains("'self'")),
            "{messages:?}"
        );
    }

    #[test]
    fn attribute_marks_named_value_and_reference_dereference_copies() {
        let messages = findings(&format!(
            r#"{TYPES}
func main() {{
    var lock = Lock {{ value: 1 }}
    copied := lock
    reference := &lock
    copiedThroughReference := *reference
    var _ = copied.value + copiedThroughReference.value
}}
"#
        ));
        assert!(
            messages.iter().any(|message| message.contains("'lock'")),
            "{messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains("'reference'")),
            "{messages:?}"
        );
    }

    #[test]
    fn attribute_propagates_through_generic_struct_tuple_array_and_enum() {
        let messages = findings(&format!(
            r#"{TYPES}
enum Choice {{ case value(Lock); case empty; }}
func structs(_ item: Wrapper[Lock]) {{}}
func tuples(_ item: (int32, Lock)) {{}}
func arrays(_ item: [Lock; 2]) {{}}
func enums(_ item: Choice) {{}}
func main() {{}}
"#
        ));
        assert_eq!(
            messages
                .iter()
                .filter(|message| message.contains("parameter"))
                .count(),
            4,
            "{messages:?}"
        );
    }

    #[test]
    fn references_pointers_and_unmarked_class_handles_remain_copyable() {
        let messages = findings(&format!(
            r#"{TYPES}
final class Holder {{ lock: Lock }}
func references(_ value: &Lock) {{ copy := value; copy.value = 2 }}
func pointers(_ value: *mut Lock) {{ copy := value; var _ = copy }}
func handles(_ value: Holder) {{ copy := value; var _ = copy }}
func main() {{}}
"#
        ));
        assert!(messages.is_empty(), "{messages:?}");
    }

    #[test]
    fn fresh_construction_and_call_results_can_initialize_values() {
        let messages = findings(&format!(
            r#"{TYPES}
func create() -> Lock {{ Lock {{ value: 1 }} }}
func main() {{
    var first = Lock {{ value: 1 }}
    var second = create()
    alias := &first
    copy := alias
    copy.value = second.value
}}
"#
        ));
        assert!(messages.is_empty(), "{messages:?}");
    }

    #[test]
    fn named_returns_arguments_and_value_receivers_are_diagnosed() {
        let messages = findings(&format!(
            r#"{TYPES}
func consume(_ value: Lock) {{}}
func copy(_ value: &Lock) -> Lock {{ *value }}
extend Lock {{
    func inspect() -> int32 {{ self.value }}
}}
func main() {{
    var lock = Lock {{ value: 1 }}
    consume(lock)
}}
"#
        ));
        assert!(
            messages
                .iter()
                .any(|message| message.contains("parameter 'value'")),
            "{messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains("parameter 'self'")),
            "{messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains("copy of @NoCopy value 'value'")),
            "{messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|message| message.contains("copy of @NoCopy value 'lock'")),
            "{messages:?}"
        );
    }

    #[test]
    fn array_repetition_diagnoses_fresh_values_too() {
        let messages = findings(&format!(
            r#"{TYPES}
func main() {{
    var repeated: [Lock; 2] = [Lock {{ value: 1 }}; 2]
    var _ = &repeated
}}
"#
        ));
        assert!(
            messages
                .iter()
                .any(|message| message.contains("array repetition")),
            "{messages:?}"
        );
    }

    #[test]
    fn fresh_erasure_cannot_hide_no_copy() {
        let messages = findings(&format!(
            r#"{TYPES}
interface Label {{ func label() -> int32; }}
conform Lock to Label {{
    func label() -> int32 {{ self.value }}
}}
func main() {{
    var erased: any Label = Lock {{ value: 1 }}
    var _ = &erased
}}
"#
        ));
        assert!(
            messages
                .iter()
                .any(|message| message.contains("boxing a @NoCopy value")),
            "{messages:?}"
        );
    }

    #[test]
    fn attribute_rejects_arguments_and_non_type_targets() {
        let errors = crate::test_support::analyze_script_diagnostics(
            r#"
@NoCopy
func copied() {}
@NoCopy("reason")
struct Lock {}
func main() {}
"#,
        );
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("structs, classes, and enums")),
            "{errors:?}"
        );
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("does not take arguments")),
            "{errors:?}"
        );
    }
}
