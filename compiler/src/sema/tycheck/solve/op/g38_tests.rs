//! Operators select their language interface with ordinary receiver/value rules.
use crate::{diagnostics::Diagnostic, hir::StdItem};

const INTERFACES: &str = "interface Add[Rhs = Self] { type Output = Self; func add(_ rhs: Rhs) -> Self::Output; }\ninterface AddAssign[Rhs = Self] { func addAssign(_ rhs: Rhs); }\ninterface Neg { type Output = Self; func neg() -> Self::Output; }\n";
fn diagnostics(source: &str) -> Vec<Diagnostic> {
    crate::test_support::analyze_language_item_script(
        &format!("{INTERFACES}{source}"),
        false,
        &[
            (StdItem::Add, "Add"),
            (StdItem::AddAssign, "AddAssign"),
            (StdItem::Neg, "Neg"),
        ],
    )
}

#[test]
fn g38_binary_operators_use_value_rhs_and_associated_output() {
    let result = diagnostics(
        "struct Counter { value: int32 }\nconform Counter to Add[int32] { type Output = int32; func add(_ rhs: int32) -> int32 { self.value + rhs }; }\nconform int32 to Add[Counter] { type Output = int32; func add(_ rhs: Counter) -> int32 { self + rhs.value }; }\nfunc check(_ value: Counter) -> int32 { value + 2_i32 + (3_i32 + value) }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_assignment_can_mutate_original_reference_storage() {
    let result = diagnostics(
        "struct Counter { value: int32 }\nconform &Counter to AddAssign[int32] { func addAssign(_ rhs: int32) { self.value += rhs }; }\nfunc check(_ value: &Counter) { *value += 2_i32 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_class_assignment_does_not_write_back_the_handle_slot() {
    let result = diagnostics(
        "class Counter { value: int32 }\nconform Counter to AddAssign[int32] { func addAssign(_ rhs: int32) { self.value += rhs }; }\nstruct Holder { readonly counter: Counter }\nfunc check(_ value: Holder) { value.counter += 2_i32 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_value_assignment_can_mutate_shared_state_without_writing_its_receiver() {
    let result = diagnostics(
        "struct Counter { value: &int32 }\nconform Counter to AddAssign[int32] { func addAssign(_ rhs: int32) { *self.value += rhs }; }\nstruct Holder { readonly counter: Counter }\nfunc check(_ value: Holder) { value.counter += 2_i32 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_primitive_bound_proves_its_known_associated_result() {
    let result = diagnostics(
        "func negative[T: Neg[Output = int32]](_ value: T) -> int32 { -value }\nfunc main() { result := negative(1_i32) }",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_inherent_methods_and_add_do_not_enable_unrelated_operators() {
    for operation in ["value + value", "value += value"] {
        let result = diagnostics(&format!(
            "struct Counter {{ value: int32 }}\nextend Counter {{ func add(_ rhs: Counter) -> Counter {{ self }}; }}\nfunc check(_ value: Counter) {{ {operation} }}\nfunc main() {{}}"
        ));
        assert!(
            !result.is_empty(),
            "an inherent method supplied {operation}"
        );
    }
}

#[test]
fn g38_result_context_does_not_change_the_declared_rhs() {
    let result = diagnostics(
        "struct Counter { value: int32 }\nconform Counter to Add[int32] { type Output = int64; func add(_ rhs: int32) -> int64 { (self.value as int64) + (rhs as int64) }; }\nfunc check(_ value: Counter) -> int64 { value + 1 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_result_context_cannot_select_a_conformance() {
    let result = diagnostics(
        "struct Counter {}\nconform Counter to Add[int32] { type Output = int64; func add(_ rhs: int32) -> int64 { rhs as int64 }; }\nconform Counter to Add[int64] { type Output = bool; func add(_ rhs: int64) -> bool { true }; }\nfunc check(_ value: Counter) -> bool { value + 1 }\nfunc main() {}",
    );
    assert!(!result.is_empty(), "expected output selected Add[int64]");
}

#[test]
fn g38_rhs_can_itself_be_an_explicit_reference_value() {
    let result = diagnostics(
        "struct Counter { value: int32 }\nconform Counter to Add[&int32] { type Output = int32; func add(_ rhs: &int32) -> int32 { self.value + *rhs }; }\nfunc check(_ value: Counter, _ rhs: &int32) -> int32 { value + rhs }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_value_assignment_accepts_a_returned_class_receiver() {
    let result = diagnostics(
        "class Counter { value: int32 }\nconform Counter to AddAssign[int32] { func addAssign(_ rhs: int32) { self.value += rhs }; }\nfunc counter() -> Counter { loop {} }\nfunc main() { counter() += 2_i32 }",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_value_assignment_does_not_invent_a_property_writeback() {
    let result = diagnostics(
        "class Counter { value: int32 }\nconform Counter to AddAssign[int32] { func addAssign(_ rhs: int32) { self.value += rhs }; }\nstruct Holder { raw: Counter }\nextend Holder { var counter: Counter { get { self.raw } }; }\nfunc check(_ holder: Holder) { holder.counter += 2_i32 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_reference_assignment_follows_ordinary_method_semantics() {
    let result = diagnostics(
        "struct Counter { value: int32 }\nconform &Counter to AddAssign[int32] { func addAssign(_ rhs: int32) { self.value += rhs }; }\nstruct Holder { readonly counter: Counter }\nfunc check(_ holder: Holder) { holder.counter += 2_i32 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_intrinsic_assignment_still_requires_a_destination() {
    let result = diagnostics("func main() { 1_i32 += 2_i32 }");
    assert!(
        result
            .iter()
            .any(|diagnostic| diagnostic.message.contains("not assignable")),
        "{result:#?}"
    );
}

#[test]
fn g38_associated_default_is_not_a_generic_output_equality() {
    let result =
        diagnostics("func same[T: Add](_ value: T) -> T { value + value }\nfunc main() {}");
    assert!(
        !result.is_empty(),
        "an overridable Output default was assumed for every T"
    );
}

#[test]
fn g38_associated_output_can_remain_abstract_in_a_generic_function() {
    let result = diagnostics(
        "func sum[T: Add](_ left: T, _ right: T) -> T::Output { left + right }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_result_context_does_not_retype_an_explicit_factory_receiver() {
    let result = diagnostics(
        "struct Counter { value: int32 }\nconform Counter to Add[int32] { type Output = int64; func add(_ rhs: int32) -> int64 { rhs as int64 }; }\nfunc make[T]() -> T { loop {} }\nfunc sum() -> int64 { make[Counter]() + 1 }\nfunc main() {}",
    );
    assert!(result.is_empty(), "{result:#?}");
}

#[test]
fn g38_primitive_associated_output_infers_a_generic_result_parameter() {
    let result = diagnostics(
        "func negative[Output, T: Neg[Output = Output]](_ value: T) -> Output { -value }\nfunc main() { value := negative(1_i32); check := value == 0_i32 }",
    );
    assert!(result.is_empty(), "{result:#?}");
}
