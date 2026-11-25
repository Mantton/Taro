use crate::{diagnostics::Diagnostic, hir::StdItem};

const INTERFACES: &str = "interface Add[Rhs=Self] { type Output = Self; func add(_ rhs: Rhs) -> Self::Output; }\ninterface AddAssign[Rhs=Self] { func addAssign(_ rhs: Rhs); }\n";
const COUNTER: &str = "struct Counter { value: int32 }\nconform Counter to Add { func add(_ rhs: Self) -> Self { Counter { value: self.value + rhs.value } }\n}\nconform &Counter to AddAssign[Counter] { func addAssign(_ rhs: Counter) { self.value += rhs.value }\n}\n";

fn diagnostics(body: &str) -> Vec<Diagnostic> {
    crate::test_support::analyze_language_item_script(
        &format!("{INTERFACES}{COUNTER}{body}"),
        true,
        &[(StdItem::Add, "Add"), (StdItem::AddAssign, "AddAssign")],
    )
}

#[test]
fn arithmetic_values_and_assignment_storage_dispatch_in_direct_and_generic_calls() {
    let diagnostics = diagnostics(
        "func combine[T: Add[T, Output = T]](_ first: &T, _ second: &T) -> T { *first + *second }\nfunc accumulate[Value, Storage: AddAssign[Value]](_ first: Storage, _ second: &Value) { first.addAssign(*second) }\nfunc main() { var first = Counter { value: 3 }; second := Counter { value: 5 }; result := first + second; generic := combine(&first, &second); first += second; accumulate(&first, &second); read := first.value + second.value + result.value + generic.value }",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn overloaded_compound_assignment_evaluates_rhs_before_receiver() {
    let diagnostics = diagnostics(
        "func destination(_ value: &Counter) -> &Counter { value.value = 1; value }\nfunc source(_ value: &Counter) -> Counter { value.value = 10; Counter { value: 2 } }\nfunc main() { var value = Counter { value: 0 }; *destination(&value) += source(&value) }",
    );
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn reference_assignment_uses_ordinary_receiver_storage() {
    let implementation = "struct Observer { value: int32 }\nconform &Observer to AddAssign[Observer] { func addAssign(_ rhs: Observer) {}\n}\n";
    let valid = diagnostics(&format!(
        "{implementation}func main() {{ var first = Observer {{ value: 1 }}; second := Observer {{ value: 2 }}; first += second; read := first.value + second.value }}"
    ));
    assert!(valid.is_empty(), "{valid:#?}");
    let readonly_slot = diagnostics(&format!(
        "{implementation}struct Holder {{ readonly first: Observer }}\nfunc main() {{ var holder = Holder {{ first: Observer {{ value: 1 }} }}; second := Observer {{ value: 2 }}; holder.first += second }}"
    ));
    assert!(readonly_slot.is_empty(), "{readonly_slot:#?}");
}
