//! Concrete generic specializations reached by opening an erased value.
//!
//! Unlike class dispatch, the first key is the *stored concrete value type*:
//! erasing a Base handle never turns it into the object's dynamic Derived type.
//! All keys/targets are immutable, compiler-owned linker identities. A resolved
//! target is invoked after releasing the registry lock; lookup calls no Taro code.
use std::{
    collections::HashMap,
    sync::{OnceLock, RwLock},
};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct ErasedOpening {
    pub concrete: *const u8,
    pub family: *const u8,
    pub arguments: *const u8,
    pub target: *const u8,
}

type Key = (usize, usize, usize);
fn registry() -> &'static RwLock<HashMap<Key, usize>> {
    static ENTRIES: OnceLock<RwLock<HashMap<Key, usize>>> = OnceLock::new();
    ENTRIES.get_or_init(|| RwLock::new(HashMap::new()))
}
fn invalid(message: &str) -> ! {
    eprintln!("fatal: invalid erased generic dispatch: {message}");
    std::process::abort()
}

/// # Safety
/// Every key has process lifetime and is a canonical, nonnull compiler identity.
/// The target implements the family's exact erased bridge ABI. Registration does not grant interface conformance to source types.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__erased_register_openings(
    entries: *const ErasedOpening,
    count: usize,
) {
    if count == 0 {
        return;
    }
    if entries.is_null() {
        invalid("null registration table");
    }
    let entries = unsafe { std::slice::from_raw_parts(entries, count) };
    let mut registry = registry()
        .write()
        .unwrap_or_else(|_| invalid("poisoned registry"));
    for entry in entries {
        if entry.concrete.is_null()
            || entry.family.is_null()
            || entry.arguments.is_null()
            || entry.target.is_null()
        {
            invalid("incomplete or unchecked registration");
        }
        let key = (
            entry.concrete as usize,
            entry.family as usize,
            entry.arguments as usize,
        );
        if let Some(previous) = registry.insert(key, entry.target as usize)
            && previous != entry.target as usize
        {
            invalid("conflicting concrete specializations");
        }
    }
}

/// # Safety
/// The caller holds an owned value or a live borrow of its container, proves
/// its static interface requirements, and uses the family's exact bridge ABI.
/// This operation neither moves the payload nor changes the borrow's mode.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__erased_resolve_opening(
    concrete: *const u8,
    family: *const u8,
    arguments: *const u8,
) -> *const u8 {
    if concrete.is_null() || family.is_null() || arguments.is_null() {
        invalid("null concrete type, family or argument key");
    }
    registry()
        .read()
        .unwrap_or_else(|_| invalid("poisoned registry"))
        .get(&(concrete as usize, family as usize, arguments as usize))
        .copied()
        .map(|target| target as *const u8)
        .unwrap_or_else(|| invalid("missing concrete generic specialization"))
}

#[cfg(test)]
mod tests {
    use super::*;
    static VALUE: u8 = 1;
    static OTHER: u8 = 2;
    static FAMILY: u8 = 3;
    static ARGS: u8 = 4;
    static OTHER_ARGS: u8 = 5;
    extern "C" fn first() {}
    extern "C" fn second() {}
    extern "C" fn third() {}

    #[test]
    fn concrete_type_and_other_arguments_select_independent_native_bridges() {
        let entries = [
            ErasedOpening {
                concrete: &VALUE,
                family: &FAMILY,
                arguments: &ARGS,
                target: first as *const u8,
            },
            ErasedOpening {
                concrete: &OTHER,
                family: &FAMILY,
                arguments: &ARGS,
                target: second as *const u8,
            },
            ErasedOpening {
                concrete: &VALUE,
                family: &FAMILY,
                arguments: &OTHER_ARGS,
                target: third as *const u8,
            },
        ];
        unsafe {
            __rt__erased_register_openings(entries.as_ptr(), entries.len());
            // ODR-merged registrations can safely repeat an identical target.
            __rt__erased_register_openings(entries.as_ptr(), entries.len());
            for entry in entries {
                assert_eq!(
                    __rt__erased_resolve_opening(entry.concrete, entry.family, entry.arguments),
                    entry.target
                );
            }
        }
    }
}
