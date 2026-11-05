//! Immutable type identities and conformance tables used by GC dispatch.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct ConformanceEntry {
    pub iface_desc: *const u8,
    pub witness_table: *const u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TypeMetadata {
    pub entries: *const ConformanceEntry,
    pub len: usize,
    /// Canonical, address-significant type token. Dispatch metadata may vary
    /// with overflow mode without changing the concrete value's identity.
    pub identity: *const u8,
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__existential_lookup_conformance(
    meta: *const TypeMetadata,
    iface_desc: *const u8,
) -> *const u8 {
    if meta.is_null() || iface_desc.is_null() {
        return std::ptr::null();
    }

    let meta = unsafe { &*meta };
    if meta.entries.is_null() || meta.len == 0 {
        return std::ptr::null();
    }

    for i in 0..meta.len {
        let entry = unsafe { &*meta.entries.add(i) };
        if entry.iface_desc == iface_desc {
            return entry.witness_table;
        }
    }

    std::ptr::null()
}
