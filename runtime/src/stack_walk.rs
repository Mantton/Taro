//! Cooperative native stack walking for GC roots and compact Taro frames.

use std::ffi::c_void;

use crate::gc_layout::{TraceMode, trace_layout};
use crate::pc_metadata::{self, LogicalFrame, PcFunction, PcRecord, RootLocation};

const MAX_WALKED_FRAMES: usize = 4096;
const MAX_CAPTURED_ROOTS: usize = 1 << 20;
const MAX_LOGICAL_FRAMES: usize = 4096;

#[cfg(unix)]
#[repr(C)]
struct UnwindContext {
    _private: [u8; 0],
}

#[cfg(unix)]
type UnwindReasonCode = i32;

#[cfg(unix)]
const URC_NO_REASON: UnwindReasonCode = 0;
#[cfg(unix)]
const URC_END_OF_STACK: UnwindReasonCode = 5;

#[cfg(unix)]
unsafe extern "C" {
    fn _Unwind_Backtrace(
        trace: unsafe extern "C" fn(*mut UnwindContext, *mut c_void) -> UnwindReasonCode,
        argument: *mut c_void,
    ) -> UnwindReasonCode;
    fn _Unwind_GetIP(context: *mut UnwindContext) -> usize;
    fn _Unwind_GetCFA(context: *mut UnwindContext) -> usize;
    fn _Unwind_GetGR(context: *mut UnwindContext, index: i32) -> usize;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CapturedLogicalFrame {
    pub(crate) function: String,
    pub(crate) file: String,
    pub(crate) line: u32,
    pub(crate) column: u32,
}

#[derive(Default)]
struct WalkOutput {
    roots: Vec<*const u8>,
    frames: Vec<CapturedLogicalFrame>,
    walked_frames: usize,
    capture_roots: bool,
    capture_frames: bool,
}

fn add_signed(base: usize, offset: i32) -> Option<usize> {
    if offset >= 0 {
        base.checked_add(offset as usize)
    } else {
        base.checked_sub(offset.unsigned_abs() as usize)
    }
}

#[cfg(target_arch = "x86_64")]
const STACK_POINTER_DWARF_REGISTER: u16 = 7;
#[cfg(target_arch = "x86_64")]
const FRAME_POINTER_DWARF_REGISTER: u16 = 6;
#[cfg(target_arch = "x86_64")]
const CALL_FRAME_BYTES: usize = std::mem::size_of::<usize>();

#[cfg(target_arch = "aarch64")]
const STACK_POINTER_DWARF_REGISTER: u16 = 31;
#[cfg(target_arch = "aarch64")]
const FRAME_POINTER_DWARF_REGISTER: u16 = 29;
#[cfg(target_arch = "aarch64")]
const CALL_FRAME_BYTES: usize = 0;

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const STACK_POINTER_DWARF_REGISTER: u16 = u16::MAX;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const FRAME_POINTER_DWARF_REGISTER: u16 = u16::MAX - 1;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
const CALL_FRAME_BYTES: usize = 0;

#[cfg(unix)]
unsafe fn location_base(
    context: *mut UnwindContext,
    function: &PcFunction,
    location: &RootLocation,
) -> Option<usize> {
    if location.dwarf_register == STACK_POINTER_DWARF_REGISTER {
        let cfa = unsafe { _Unwind_GetCFA(context) };
        let stack_size = usize::try_from(function.stack_size).ok()?;
        cfa.checked_sub(CALL_FRAME_BYTES)?.checked_sub(stack_size)
    } else if location.dwarf_register == FRAME_POINTER_DWARF_REGISTER {
        Some(unsafe { _Unwind_GetGR(context, i32::from(location.dwarf_register)) })
    } else {
        None
    }
}

unsafe fn load_pointer(address: usize) -> Option<usize> {
    if address == 0 || address % std::mem::align_of::<usize>() != 0 {
        return None;
    }
    Some(unsafe { std::ptr::read_unaligned(address as *const usize) })
}

unsafe fn evaluate_root_location(
    mut storage: usize,
    location: &RootLocation,
    output: &mut Vec<*const u8>,
) {
    for _ in 0..location.storage_deref_depth {
        let Some(next) = (unsafe { load_pointer(storage) }) else {
            return;
        };
        if next == 0 {
            return;
        }
        storage = next;
    }

    let result = unsafe {
        trace_layout(
            storage as *const u8,
            &location.nodes,
            usize::MAX,
            TraceMode::Stack,
            |value| {
                if output.len() < MAX_CAPTURED_ROOTS {
                    output.push(value);
                }
            },
        )
    };
    if let Err(error) = result {
        eprintln!("fatal: invalid live stack GC value at {storage:#x}: {error}");
        std::process::abort();
    }
}

fn append_frames(frames: &[LogicalFrame], output: &mut Vec<CapturedLogicalFrame>) {
    for frame in frames {
        if output.len() >= MAX_LOGICAL_FRAMES {
            return;
        }
        output.push(CapturedLogicalFrame {
            function: frame.function.clone(),
            file: frame.file.clone(),
            line: frame.line,
            column: frame.column,
        });
    }
}

#[cfg(unix)]
unsafe extern "C" fn trace_frame(
    context: *mut UnwindContext,
    argument: *mut c_void,
) -> UnwindReasonCode {
    let output = unsafe { &mut *(argument as *mut WalkOutput) };
    output.walked_frames += 1;
    if output.walked_frames > MAX_WALKED_FRAMES {
        return URC_END_OF_STACK;
    }
    let pc = unsafe { _Unwind_GetIP(context) };
    if pc == 0 {
        return URC_NO_REASON;
    }
    pc_metadata::with_record_at_pc(
        pc,
        output.capture_roots,
        output.capture_frames,
        |function, record| {
            if output.capture_roots {
                append_roots(context, function, record, &mut output.roots);
            }
            if output.capture_frames {
                append_frames(record.logical_frames.as_ref(), &mut output.frames);
            }
        },
    );
    URC_NO_REASON
}

#[cfg(unix)]
fn append_roots(
    context: *mut UnwindContext,
    function: &PcFunction,
    record: &PcRecord,
    output: &mut Vec<*const u8>,
) {
    for location in record.roots.iter() {
        if output.len() >= MAX_CAPTURED_ROOTS {
            return;
        }
        let Some(base) = (unsafe { location_base(context, function, location) }) else {
            continue;
        };
        let Some(storage) = add_signed(base, location.frame_offset) else {
            continue;
        };
        unsafe { evaluate_root_location(storage, location, output) };
    }
}

fn walk(capture_roots: bool, capture_frames: bool) -> WalkOutput {
    let mut output = WalkOutput {
        capture_roots,
        capture_frames,
        ..WalkOutput::default()
    };
    #[cfg(unix)]
    unsafe {
        _Unwind_Backtrace(trace_frame, (&mut output as *mut WalkOutput).cast());
    }
    if capture_roots {
        output
            .roots
            .sort_unstable_by_key(|pointer| *pointer as usize);
        output.roots.dedup();
    }
    output
}

pub(crate) fn capture_current_roots() -> Vec<*const u8> {
    walk(true, false).roots
}

pub(crate) fn capture_logical_frames() -> Vec<CapturedLogicalFrame> {
    walk(false, true).frames
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gc_layout::{GC_LAYOUT_POINTER, GC_LAYOUT_REFERENCE, GcLayoutNode};

    #[test]
    fn root_layout_follows_storage_and_reference_indirection() {
        let managed = Box::new(17_u64);
        let managed_pointer = (&*managed as *const u64).cast::<u8>();
        let aggregate = Box::new(managed_pointer as usize);
        let reference = Box::new((&*aggregate as *const usize) as usize);
        let wrapper = Box::new((&*reference as *const usize) as usize);
        let location = RootLocation {
            dwarf_register: FRAME_POINTER_DWARF_REGISTER,
            frame_offset: 0,
            storage_deref_depth: 1,
            nodes: vec![
                GcLayoutNode {
                    offset: 0,
                    stride: 0,
                    first_child: 1,
                    child_count: 1,
                    kind: GC_LAYOUT_REFERENCE,
                    width: 0,
                    reserved: [0; 6],
                },
                GcLayoutNode {
                    offset: 0,
                    stride: 0,
                    first_child: 0,
                    child_count: 0,
                    kind: GC_LAYOUT_POINTER,
                    width: 0,
                    reserved: [0; 6],
                },
            ],
        };
        let mut roots = Vec::new();
        unsafe {
            evaluate_root_location((&*wrapper as *const usize) as usize, &location, &mut roots)
        };
        assert_eq!(
            roots,
            vec![(&*aggregate as *const usize).cast::<u8>(), managed_pointer,]
        );
    }

    #[test]
    fn null_reference_stops_deeper_layout_traversal() {
        let storage = Box::new(0_usize);
        let location = RootLocation {
            dwarf_register: FRAME_POINTER_DWARF_REGISTER,
            frame_offset: 0,
            storage_deref_depth: 0,
            nodes: vec![
                GcLayoutNode {
                    offset: 0,
                    stride: 0,
                    first_child: 1,
                    child_count: 1,
                    kind: GC_LAYOUT_REFERENCE,
                    width: 0,
                    reserved: [0; 6],
                },
                GcLayoutNode {
                    offset: 0,
                    stride: 0,
                    first_child: 0,
                    child_count: 0,
                    kind: GC_LAYOUT_POINTER,
                    width: 0,
                    reserved: [0; 6],
                },
            ],
        };
        let mut roots = Vec::new();
        unsafe {
            evaluate_root_location((&*storage as *const usize) as usize, &location, &mut roots)
        };
        assert!(roots.is_empty());
    }
}
