//! Drop re-publications of GC roots that their slot already holds.
//!
//! Each collecting site publishes its live private values to their root slots
//! with volatile stores, so that LLVM keeps them for the collector. The collector
//! doesn't move objects, so a slot still holding the same value needs no new store,
//! but volatile stores are exactly what LLVM can't remove.
//!
//! A slot qualifies only if everything using it is understood here: stores to it,
//! loads and stack maps reading it, and intrinsics that clear it or end its life. An
//! alloca with any other use, such as a field address, is left entirely alone.
//!
//! A store is dropped when, on every path to it, the slot's last store wrote the same
//! SSA value and that value's definition hasn't run again since. That last condition
//! is what makes this correct in a loop, where one SSA value is many runtime values.
use inkwell::basic_block::BasicBlock;
use inkwell::module::Module;
use inkwell::values::{
    AnyValueEnum, AsValueRef, CallSiteValue, FunctionValue, InstructionOpcode, InstructionValue,
    Operand,
};
use llvm_sys::prelude::LLVMValueRef;
use rustc_hash::{FxHashMap, FxHashSet};

/// Beyond this much work in one function the savings can't justify the compile time.
const MAX_FUNCTION_OPERATIONS: usize = 200_000;

#[derive(Clone, Copy)]
enum Operation<'ctx> {
    Store {
        slot: LLVMValueRef,
        value: LLVMValueRef,
        instruction: InstructionValue<'ctx>,
    },
    ForgetSlot(LLVMValueRef),
    Redefine(LLVMValueRef),
}

type Contents = FxHashMap<LLVMValueRef, LLVMValueRef>;

fn instructions<'ctx>(block: BasicBlock<'ctx>) -> impl Iterator<Item = InstructionValue<'ctx>> {
    std::iter::successors(block.get_first_instruction(), |instruction| {
        instruction.get_next_instruction()
    })
}

fn called_name(instruction: InstructionValue<'_>) -> Option<String> {
    let call = CallSiteValue::try_from(instruction).ok()?;
    let function = call.get_called_fn_value()?;
    Some(function.get_name().to_string_lossy().into_owned())
}

fn operand_ref(instruction: InstructionValue<'_>, index: u32) -> Option<LLVMValueRef> {
    match instruction.get_operand(index)? {
        Operand::Value(value) => Some(value.as_value_ref()),
        Operand::Block(_) => None,
    }
}

/// An intrinsic that writes the slot in its first argument without capturing it.
fn clears_or_ends_slot(name: &str) -> bool {
    name.starts_with("llvm.memset") || name.starts_with("llvm.lifetime.")
}

fn is_understood_slot(alloca: InstructionValue<'_>) -> bool {
    let slot = alloca.as_value_ref();
    let mut next = alloca.get_first_use();
    while let Some(current) = next {
        next = current.get_next_use();
        let AnyValueEnum::InstructionValue(user) = current.get_user() else {
            return false;
        };
        let understood = match user.get_opcode() {
            InstructionOpcode::Load => true,
            // The slot being the stored value would let its address escape.
            InstructionOpcode::Store => {
                operand_ref(user, 0) != Some(slot) && operand_ref(user, 1) == Some(slot)
            }
            InstructionOpcode::Call => match called_name(user) {
                Some(name) if name.starts_with("llvm.experimental.stackmap") => true,
                Some(name) if clears_or_ends_slot(&name) => {
                    operand_ref(user, 0) == Some(slot)
                        && (1..user.get_num_operands())
                            .all(|index| operand_ref(user, index) != Some(slot))
                }
                _ => false,
            },
            _ => false,
        };
        if !understood {
            return false;
        }
    }
    true
}

fn successors<'ctx>(block: BasicBlock<'ctx>) -> Vec<BasicBlock<'ctx>> {
    let Some(terminator) = block.get_terminator() else {
        return Vec::new();
    };
    (0..terminator.get_num_operands())
        .filter_map(|index| match terminator.get_operand(index)? {
            Operand::Block(successor) => Some(successor),
            Operand::Value(_) => None,
        })
        .collect()
}

fn apply<'ctx>(
    operations: &[Operation<'ctx>],
    contents: &mut Contents,
    mut redundant: impl FnMut(InstructionValue<'ctx>),
) {
    for operation in operations {
        match *operation {
            Operation::Store {
                slot,
                value,
                instruction,
            } => {
                if contents.insert(slot, value) == Some(value) {
                    redundant(instruction);
                }
            }
            Operation::ForgetSlot(slot) => {
                contents.remove(&slot);
            }
            Operation::Redefine(value) => contents.retain(|_, held| *held != value),
        }
    }
}

fn elide_in_function(function: FunctionValue<'_>) -> usize {
    let blocks = function.get_basic_blocks();
    let Some(entry) = blocks.first().copied() else {
        return 0;
    };
    // Only an entry-block alloca is one slot for the whole call.
    let slots: FxHashSet<LLVMValueRef> = instructions(entry)
        .filter(|instruction| instruction.get_opcode() == InstructionOpcode::Alloca)
        .filter(|alloca| is_understood_slot(*alloca))
        .map(|alloca| alloca.as_value_ref())
        .collect();
    if slots.is_empty() {
        return 0;
    }
    let mut stored_values = FxHashSet::default();
    for block in &blocks {
        for instruction in instructions(*block) {
            if instruction.get_opcode() == InstructionOpcode::Store
                && operand_ref(instruction, 1).is_some_and(|pointer| slots.contains(&pointer))
                && let Some(value) = operand_ref(instruction, 0)
            {
                stored_values.insert(value);
            }
        }
    }
    let mut operations: Vec<Vec<Operation<'_>>> = Vec::with_capacity(blocks.len());
    let mut total = 0;
    for block in &blocks {
        let mut list = Vec::new();
        for instruction in instructions(*block) {
            let reference = instruction.as_value_ref();
            if stored_values.contains(&reference) {
                list.push(Operation::Redefine(reference));
            }
            match instruction.get_opcode() {
                InstructionOpcode::Store => {
                    if let (Some(value), Some(slot)) =
                        (operand_ref(instruction, 0), operand_ref(instruction, 1))
                        && slots.contains(&slot)
                    {
                        list.push(Operation::Store {
                            slot,
                            value,
                            instruction,
                        });
                    }
                }
                InstructionOpcode::Call => {
                    if let Some(slot) = operand_ref(instruction, 0)
                        && slots.contains(&slot)
                        && called_name(instruction).is_some_and(|name| clears_or_ends_slot(&name))
                    {
                        list.push(Operation::ForgetSlot(slot));
                    }
                }
                _ => {}
            }
        }
        total += list.len();
        operations.push(list);
    }
    if total > MAX_FUNCTION_OPERATIONS {
        return 0;
    }

    let index_of: FxHashMap<_, _> = blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (*block, index))
        .collect();
    let successor_lists: Vec<Vec<usize>> = blocks
        .iter()
        .map(|block| {
            successors(*block)
                .iter()
                .filter_map(|successor| index_of.get(successor).copied())
                .collect()
        })
        .collect();
    // A block's entry contents only ever shrink, from unknown to what every path
    // that reaches it agrees on. The entry block starts with nothing known.
    let mut entries: Vec<Option<Contents>> = vec![None; blocks.len()];
    entries[0] = Some(Contents::default());
    let mut pending = vec![0];
    while let Some(index) = pending.pop() {
        let mut contents = entries[index].clone().expect("a pending block was reached");
        apply(&operations[index], &mut contents, |_| {});
        for &successor in &successor_lists[index] {
            match &mut entries[successor] {
                slot @ None => {
                    *slot = Some(contents.clone());
                    pending.push(successor);
                }
                Some(existing) => {
                    let before = existing.len();
                    existing.retain(|slot, value| contents.get(slot) == Some(value));
                    if existing.len() != before {
                        pending.push(successor);
                    }
                }
            }
        }
    }

    let mut removable = Vec::new();
    for (index, entry) in entries.into_iter().enumerate() {
        if let Some(mut contents) = entry {
            apply(&operations[index], &mut contents, |instruction| {
                removable.push(instruction)
            });
        }
    }
    let removed = removable.len();
    for instruction in removable {
        instruction.erase_from_basic_block();
    }
    removed
}

/// Remove every redundant root publication in `module`, returning how many there were.
pub(crate) fn elide_redundant_root_stores(module: &Module<'_>) -> usize {
    module.get_functions().map(elide_in_function).sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use inkwell::context::Context;
    use inkwell::memory_buffer::MemoryBuffer;

    /// The volatile stores `ir` keeps once the pass has run.
    fn remaining_stores(ir: &str) -> usize {
        let context = Context::create();
        let buffer = MemoryBuffer::create_from_memory_range_copy(ir.as_bytes(), "test");
        let module = context.create_module_from_ir(buffer).unwrap();
        elide_redundant_root_stores(&module);
        module.verify().unwrap();
        module
            .get_functions()
            .flat_map(|function| function.get_basic_blocks())
            .flat_map(instructions)
            .filter(|instruction| {
                instruction.get_opcode() == InstructionOpcode::Store
                    && instruction.get_volatile().unwrap()
            })
            .count()
    }

    const PRELUDE: &str = "
        declare void @llvm.experimental.stackmap(i64, i32, ...)
        declare void @llvm.lifetime.start.p0(ptr)
        declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)
        declare void @collecting()
        declare ptr @produce()
        declare i1 @flag()
        declare void @escape(ptr)
        declare i32 @__gxx_personality_v0(...)
    ";

    fn with_prelude(body: &str) -> String {
        format!("{PRELUDE}\n{body}\0")
    }

    #[test]
    fn a_slot_already_holding_the_value_needs_no_second_store() {
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %root) {
                    %slot = alloca ptr
                    store volatile ptr %root, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    call void @collecting()
                    store volatile ptr %root, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 2, i32 0, ptr %slot)
                    call void @collecting()
                    ret void
                }"
            )),
            1
        );
    }

    #[test]
    fn a_different_value_is_always_stored() {
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %first, ptr %second) {
                    %slot = alloca ptr
                    store volatile ptr %first, ptr %slot
                    store volatile ptr %second, ptr %slot
                    store volatile ptr %first, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    ret void
                }"
            )),
            3
        );
    }

    #[test]
    fn one_ssa_value_in_a_loop_is_a_new_value_each_iteration() {
        // Without noticing %next being redefined, this would root a stale object.
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f() {
                entry:
                    %slot = alloca ptr
                    br label %loop
                loop:
                    %next = call ptr @produce()
                    store volatile ptr %next, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    call void @collecting()
                    %again = call i1 @flag()
                    br i1 %again, label %loop, label %done
                done:
                    ret void
                }"
            )),
            1
        );
        // The store has to run every iteration, not only the first.
        let context = Context::create();
        let buffer = MemoryBuffer::create_from_memory_range_copy(
            with_prelude(
                "define void @f(ptr %start, i1 %c) {
                entry:
                    %slot = alloca ptr
                    store volatile ptr %start, ptr %slot
                    br label %loop
                loop:
                    %current = phi ptr [ %start, %entry ], [ %next, %loop ]
                    store volatile ptr %current, ptr %slot
                    %next = call ptr @produce()
                    br i1 %c, label %loop, label %done
                done:
                    ret void
                }",
            )
            .as_bytes(),
            "test",
        );
        let module = context.create_module_from_ir(buffer).unwrap();
        assert_eq!(elide_redundant_root_stores(&module), 0);
    }

    #[test]
    fn a_value_unchanged_around_a_loop_stays_published() {
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %root) {
                entry:
                    %slot = alloca ptr
                    store volatile ptr %root, ptr %slot
                    br label %loop
                loop:
                    store volatile ptr %root, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    call void @collecting()
                    %again = call i1 @flag()
                    br i1 %again, label %loop, label %done
                done:
                    ret void
                }"
            )),
            1
        );
    }

    #[test]
    fn every_path_to_a_store_has_to_have_published_the_value() {
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %root, ptr %other, i1 %c) {
                entry:
                    %slot = alloca ptr
                    br i1 %c, label %left, label %right
                left:
                    store volatile ptr %root, ptr %slot
                    br label %join
                right:
                    store volatile ptr %other, ptr %slot
                    br label %join
                join:
                    store volatile ptr %root, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    ret void
                }"
            )),
            3
        );
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %root, i1 %c) {
                entry:
                    %slot = alloca ptr
                    br i1 %c, label %left, label %right
                left:
                    store volatile ptr %root, ptr %slot
                    br label %join
                right:
                    store volatile ptr %root, ptr %slot
                    br label %join
                join:
                    store volatile ptr %root, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    ret void
                }"
            )),
            2
        );
    }

    #[test]
    fn a_path_that_unwinds_counts_too() {
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %root, ptr %other) personality ptr @__gxx_personality_v0 {
                entry:
                    %slot = alloca ptr
                    store volatile ptr %root, ptr %slot
                    invoke void @collecting() to label %normal unwind label %cleanup
                normal:
                    store volatile ptr %other, ptr %slot
                    ret void
                cleanup:
                    %caught = landingpad { ptr, i32 } cleanup
                    store volatile ptr %root, ptr %slot
                    call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
                    resume { ptr, i32 } %caught
                }"
            )),
            2
        );
    }

    #[test]
    fn clearing_or_restarting_a_slot_forgets_what_it_held() {
        assert_eq!(
            remaining_stores(&with_prelude(
                "define void @f(ptr %root) {
                    %slot = alloca ptr
                    store volatile ptr %root, ptr %slot
                    call void @llvm.memset.p0.i64(ptr %slot, i8 0, i64 8, i1 true)
                    store volatile ptr %root, ptr %slot
                    call void @llvm.lifetime.start.p0(ptr %slot)
                    store volatile ptr %root, ptr %slot
                    ret void
                }"
            )),
            3
        );
    }

    #[test]
    fn any_other_use_of_the_slot_leaves_it_alone() {
        for other_use in [
            "call void @escape(ptr %slot)",
            "%field = getelementptr i8, ptr %slot, i64 8\n call void @escape(ptr %field)",
            "%holder = alloca ptr\n store ptr %slot, ptr %holder",
        ] {
            assert_eq!(
                remaining_stores(&with_prelude(&format!(
                    "define void @f(ptr %root) {{
                        %slot = alloca [2 x ptr]
                        store volatile ptr %root, ptr %slot
                        {other_use}
                        store volatile ptr %root, ptr %slot
                        ret void
                    }}"
                ))),
                2,
                "{other_use}"
            );
        }
    }
}
