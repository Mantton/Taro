//! Candidate class handles point directly to a non-moving object whose first
//! word is immutable dynamic metadata. Its remaining fields are traced using
//! the allocation's typed descriptor; metadata and code addresses are not GC
//! edges. Stack placement uses this identical header and object layout.
use crate::class_metadata::{ClassDescriptor, invalid};

/// Publish the actual class once, before any initialized class handle escapes.
/// # Safety
/// `object` is aligned fresh object storage with a zero header, and `class`
/// describes that exact complete allocation. All metadata is process-long.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __gc__class_initialize(object: *mut u8, class: *const ClassDescriptor) {
    if object.is_null() || class.is_null() || unsafe { (*class).identity.is_null() } {
        invalid("null GC class publication metadata");
    }
    let slot = object.cast::<*const ClassDescriptor>();
    if !unsafe { slot.read() }.is_null() {
        invalid("GC class header was already published");
    }
    unsafe { slot.write(class) };
}

/// # Safety
/// The nonnull, initialized object remains live for this operation. Safe class
/// handles satisfy this through GC roots; raw native callers must keep a root.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __gc__class_descriptor(object: *const u8) -> *const ClassDescriptor {
    if object.is_null() {
        invalid("null GC class receiver");
    }
    let class = unsafe { object.cast::<*const ClassDescriptor>().read() };
    if class.is_null() {
        invalid("uninitialized GC class receiver");
    }
    class
}

/// # Safety
/// `object` is a live initialized class and `identity` is a canonical compiler
/// identity. Upcasts preserve the object's actual dynamic descriptor.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __gc__class_is_a(object: *const u8, identity: *const u8) -> bool {
    if identity.is_null() {
        return false;
    }
    let class = unsafe { &*__gc__class_descriptor(object) };
    unsafe { class.is_a(identity) }
}

/// # Safety
/// Receiver and immutable keys remain valid, and the caller uses the selected
/// family's exact concrete ABI. Resolving a method neither copies its receiver
/// nor changes a handle slot.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __gc__class_resolve_method(
    object: *const u8,
    family: *const u8,
    arguments: *const u8,
) -> *const u8 {
    let class = unsafe { &*__gc__class_descriptor(object) };
    unsafe { crate::class_metadata::resolve_method(class, family, arguments) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::class_metadata::ClassMethod;
    static BASE: u8 = 1;
    static CHILD: u8 = 2;
    static OTHER: u8 = 3;
    static FAMILY: u8 = 4;
    unsafe extern "C" fn base(_: *const u8) -> u32 {
        11
    }
    unsafe extern "C" fn child(_: *const u8) -> u32 {
        22
    }

    #[test]
    fn aliases_and_upcasts_preserve_the_dynamic_class_and_override() {
        static BASE_METHODS: [ClassMethod; 1] = [ClassMethod {
            family: &FAMILY,
            target: base as *const u8,
        }];
        static BASE_CLASS: ClassDescriptor = ClassDescriptor {
            identity: &BASE,
            base: std::ptr::null(),
            methods: BASE_METHODS.as_ptr(),
            method_count: 1,
        };
        static CHILD_METHODS: [ClassMethod; 1] = [ClassMethod {
            family: &FAMILY,
            target: child as *const u8,
        }];
        static CHILD_CLASS: ClassDescriptor = ClassDescriptor {
            identity: &CHILD,
            base: &BASE_CLASS,
            methods: CHILD_METHODS.as_ptr(),
            method_count: 1,
        };
        // Stack-promoted objects use the same metadata ABI. The fixture owns
        // its header for the operation; the metadata is process-long.
        let mut header: *const ClassDescriptor = std::ptr::null();
        let object = (&mut header as *mut *const ClassDescriptor).cast::<u8>();
        unsafe {
            __gc__class_initialize(object, &CHILD_CLASS);
            let alias = object;
            assert!(__gc__class_is_a(alias, &BASE));
            assert!(__gc__class_is_a(alias, &CHILD));
            assert!(!__gc__class_is_a(alias, &OTHER));
            assert_eq!(
                __gc__class_descriptor(alias),
                &CHILD_CLASS as *const ClassDescriptor
            );
            let method: unsafe extern "C" fn(*const u8) -> u32 =
                std::mem::transmute(__gc__class_resolve_method(alias, &FAMILY, std::ptr::null()));
            assert_eq!(method(alias), 22);
            let super_method: unsafe extern "C" fn(*const u8) -> u32 =
                std::mem::transmute(BASE_CLASS.method(&FAMILY).unwrap());
            assert_eq!(super_method(alias), 11);
        }
    }
}
