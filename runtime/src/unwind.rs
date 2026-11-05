//! Platform unwinder declarations used by the GC stack walker.
use std::ffi::c_void;

/// Select the instruction belonging to an unwind frame. Normal unwind IPs
/// are return addresses and may equal the start of an adjacent function;
/// signal/exact IPs already identify the instruction and must stay unchanged.
pub(crate) fn instruction_pc(ip: usize, before_instruction: bool) -> Option<usize> {
    if ip == 0 {
        None
    } else {
        Some(if before_instruction { ip } else { ip - 1 })
    }
}

#[cfg(unix)]
#[repr(C)]
pub(crate) struct UnwindContext {
    _private: [u8; 0],
}

#[cfg(unix)]
type UnwindReasonCode = i32;

#[cfg(unix)]
unsafe extern "C" {
    pub(crate) fn _Unwind_Backtrace(
        trace: unsafe extern "C" fn(*mut UnwindContext, *mut c_void) -> UnwindReasonCode,
        argument: *mut c_void,
    ) -> UnwindReasonCode;
    pub(crate) fn _Unwind_GetIPInfo(
        context: *mut UnwindContext,
        before_instruction: *mut i32,
    ) -> usize;
    pub(crate) fn _Unwind_GetCFA(context: *mut UnwindContext) -> usize;
    pub(crate) fn _Unwind_GetGR(context: *mut UnwindContext, index: i32) -> usize;
}

#[cfg(test)]
mod tests {
    #[test]
    fn unwind_ip_normalization_preserves_exact_and_call_boundaries() {
        assert_eq!(super::instruction_pc(0, false), None);
        assert_eq!(super::instruction_pc(100, false), Some(99));
        assert_eq!(super::instruction_pc(100, true), Some(100));
    }
}
