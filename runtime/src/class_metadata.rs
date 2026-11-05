//! Immutable class metadata and monomorphized generic virtual entry points.
//!
//! Keys are canonical linker identities, not hashes used as type proofs. The
//! final executable registers generic specializations before language execution.
//! Registration and lookup never invoke user code while holding the map lock.
use std::{
    collections::HashMap,
    sync::{OnceLock, RwLock},
};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct ClassMethod {
    pub family: *const u8,
    pub target: *const u8,
}

/// Compiler-owned, process-long metadata. The base payload is a physical prefix;
/// ordinary method entries may override a family inherited from that base.
#[repr(C)]
pub struct ClassDescriptor {
    pub identity: *const u8,
    pub base: *const ClassDescriptor,
    pub methods: *const ClassMethod,
    pub method_count: usize,
}
// Metadata only contains immutable addresses. This grants no Sendable property
// to an object's payload or to a method's arguments.
unsafe impl Sync for ClassDescriptor {}
unsafe impl Sync for ClassMethod {}

impl ClassDescriptor {
    /// # Safety
    /// Every descriptor/table in this acyclic chain must be readable for the
    /// process lifetime, with canonical nonnull identities and verified targets.
    pub unsafe fn is_a(&self, target: *const u8) -> bool {
        let mut current = Some(self);
        while let Some(class) = current {
            if class.identity == target {
                return true;
            }
            current = unsafe { class.base.as_ref() };
        }
        false
    }

    pub(crate) unsafe fn own_method(&self, family: *const u8) -> Option<*const u8> {
        let methods = if self.method_count == 0 {
            &[][..]
        } else {
            if self.methods.is_null() {
                invalid("null class method table");
            }
            unsafe { std::slice::from_raw_parts(self.methods, self.method_count) }
        };
        if let Some(method) = methods.iter().find(|method| method.family == family) {
            if method.target.is_null() {
                invalid("class method target is null");
            }
            return Some(method.target);
        }
        None
    }

    pub(crate) unsafe fn method(&self, family: *const u8) -> Option<*const u8> {
        unsafe { self.own_method(family) }.or_else(|| {
            unsafe { self.base.as_ref() }.and_then(|base| unsafe { base.method(family) })
        })
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct GenericClassMethod {
    pub class: *const u8,
    pub family: *const u8,
    pub arguments: *const u8,
    pub target: *const u8,
}

pub(crate) fn invalid(message: &str) -> ! {
    eprintln!("fatal: invalid class dispatch: {message}");
    std::process::abort()
}

type Key = (usize, usize, usize);
fn generic_methods() -> &'static RwLock<HashMap<Key, usize>> {
    static METHODS: OnceLock<RwLock<HashMap<Key, usize>>> = OnceLock::new();
    METHODS.get_or_init(|| RwLock::new(HashMap::new()))
}

/// # Safety
/// Entries describe actual native functions with the family's exact concrete
/// ABI, and canonical process-long class/family/type-argument identities. This
/// is compiler metadata, never an API for granting conformance to raw pointers.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__class_register_generic_methods(
    entries: *const GenericClassMethod,
    count: usize,
) {
    if count == 0 {
        return;
    }
    if entries.is_null() {
        invalid("null generic method registrations");
    }
    let entries = unsafe { std::slice::from_raw_parts(entries, count) };
    let mut methods = generic_methods()
        .write()
        .unwrap_or_else(|_| invalid("poisoned generic method registry"));
    for entry in entries {
        if entry.class.is_null()
            || entry.family.is_null()
            || entry.arguments.is_null()
            || entry.target.is_null()
        {
            invalid("incomplete generic method registration");
        }
        let key = (
            entry.class as usize,
            entry.family as usize,
            entry.arguments as usize,
        );
        if let Some(previous) = methods.insert(key, entry.target as usize)
            && previous != entry.target as usize
        {
            invalid("conflicting generic method specializations");
        }
    }
}

/// Resolve a fully constructing entry point for the requested concrete class.
/// Unlike ordinary methods, a missing constructor must never fall back to a
/// base entry: that would produce a base allocation in place of a subclass.
/// # Safety
/// descriptor and identities are trusted process-long compiler metadata. The
/// caller uses the designated family's exact native parameter/result ABI.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__class_resolve_initializer(
    descriptor: *const ClassDescriptor,
    family: *const u8,
    arguments: *const u8,
) -> *const u8 {
    if descriptor.is_null() || family.is_null() {
        invalid("null class initializer context/family");
    }
    let class = unsafe { &*descriptor };
    if class.identity.is_null() {
        invalid("null class identity");
    }
    if arguments.is_null() {
        unsafe { class.own_method(family) }
            .unwrap_or_else(|| invalid("missing concrete class initializer"))
    } else {
        generic_methods()
            .read()
            .unwrap_or_else(|_| invalid("poisoned generic method registry"))
            .get(&(class.identity as usize, family as usize, arguments as usize))
            .copied()
            .map(|target| target as *const u8)
            .unwrap_or_else(|| invalid("missing concrete generic class initializer"))
    }
}

/// Resolve a method against the actual dynamic class. Both object backends use
/// the same immutable tables and generic-specialization registry.
/// # Safety
/// Metadata and keys are process-long compiler publications with exact ABIs.
pub(crate) unsafe fn resolve_method(
    class: &ClassDescriptor,
    family: *const u8,
    arguments: *const u8,
) -> *const u8 {
    if family.is_null() {
        invalid("null virtual method family");
    }
    if arguments.is_null() {
        unsafe { class.method(family) }.unwrap_or_else(|| invalid("missing virtual method family"))
    } else {
        generic_methods()
            .read()
            .unwrap_or_else(|_| invalid("poisoned generic method registry"))
            .get(&(class.identity as usize, family as usize, arguments as usize))
            .copied()
            .map(|target| target as *const u8)
            .unwrap_or_else(|| invalid("missing generic virtual specialization"))
    }
}
