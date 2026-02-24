#[repr(C)]
#[derive(Clone, Copy)]
pub struct RtConformanceEntry {
    pub iface_desc: *const u8,
    pub witness_table: *const u8,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct RtTypeMetadata {
    pub entries: *const RtConformanceEntry,
    pub len: usize,
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__existential_lookup_conformance(
    meta: *const RtTypeMetadata,
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
