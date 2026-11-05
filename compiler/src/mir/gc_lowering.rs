//! Normalize GC value reads: user bindings remain readable, and whole-value
//! assignments copy erased payload storage when required.
use crate::mir::{Body, Operand, Rvalue, StatementKind};

pub fn lower_for_gc(body: &mut Body<'_>) {
    // Assignments of whole values duplicate erased payload storage. Codegen
    // emits nothing for values without erased payloads.
    for block in body.basic_blocks.iter_mut() {
        for statement in &mut block.statements {
            if let StatementKind::Assign(_, rvalue) = &mut statement.kind
                && let Rvalue::Use(Operand::Copy(place)) = rvalue
            {
                *rvalue = Rvalue::CopyValue {
                    source: place.clone(),
                };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::mir::{LocalKind, Operand, Rvalue, StatementKind};

    #[test]
    fn canonical_gc_assignments_materialize_value_copies() {
        let source = r#"
interface Label { func label() -> int32; }
struct Value { n: int32 }
conform Value to Label {
    func label() -> int32 { self.n }
}
struct Holder { inner: any Label; count: int32 }
func copyHolder(_ holder: Holder) -> Holder {
    first := holder
    second := holder
    var _ = first
    second
}
func identity[T](_ value: T) -> T {
    first := value
    var _ = first
    value
}
func relabel(_ holder: Holder) async -> int32 {
    copy := holder
    copy.inner.label() + holder.count
}
func main() {
    holder := Holder { inner: Value { n: 1 }, count: 2 }
    copied := copyHolder(holder)
    var _ = identity(copied)
    var _ = holder.inner.label()
}
"#;
        {
            crate::test_support::check_script(source, |_, gcx| {
                let packages = gcx.store.inline_mir_packages.borrow();
                let package = packages.get(&gcx.package_index()).unwrap();
                assert!(
                    package.functions.len() >= 5,
                    "fixture bodies were published"
                );
                for (definition, body) in &package.functions {
                    let name = gcx.definition_symbol_or_fallback(*definition);
                    for block in &body.basic_blocks {
                        for statement in &block.statements {
                            if let StatementKind::Assign(_, Rvalue::Use(Operand::Copy(place))) =
                                &statement.kind
                            {
                                assert!(
                                    !matches!(body.locals[place.local].kind, LocalKind::User),
                                    "{name}: binding assignments must use CopyValue"
                                );
                            }
                        }
                    }
                }
            })
        };
    }
}
