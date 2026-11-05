//! Diagnostic allocation attribution, compiled only with `--features alloc-profile`.
//!
//! Records every managed allocation and every Rust global-allocator request by
//! exact unwound call stack, then writes JSON lines to `TARO_ALLOC_PROFILE` at
//! normal process exit. Unwinding makes this far too slow for timing: use the
//! counts, never the throughput. It observes allocations and changes no policy.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::ffi::c_void;
use std::fmt::Write as _;
use std::sync::{Mutex, Once};

use rustc_hash::FxHashMap;

use super::{GcDesc, desc_has_pointers};
use crate::unwind::{_Unwind_Backtrace, _Unwind_GetIPInfo, UnwindContext};

const MAX_FRAMES: usize = 48;
const URC_NO_REASON: i32 = 0;
const URC_END_OF_STACK: i32 = 5;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Site {
    /// Null for native allocator requests.
    desc: usize,
    size: usize,
    frames: [usize; MAX_FRAMES],
}

static SITES: Mutex<Option<FxHashMap<Site, u64>>> = Mutex::new(None);
static REGISTER_EXIT_HOOK: Once = Once::new();

thread_local! {
    /// Unwinding and the histogram allocate; those requests are not the program's.
    static RECORDING: Cell<bool> = const { Cell::new(false) };
}

unsafe extern "C" {
    fn _dyld_get_image_vmaddr_slide(image_index: u32) -> isize;
}

struct Capture {
    frames: [usize; MAX_FRAMES],
    count: usize,
}

unsafe extern "C" fn capture_frame(context: *mut UnwindContext, argument: *mut c_void) -> i32 {
    let capture = unsafe { &mut *(argument as *mut Capture) };
    let mut before_instruction = 0;
    let ip = unsafe { _Unwind_GetIPInfo(context, &mut before_instruction) };
    if let Some(pc) = crate::unwind::instruction_pc(ip, before_instruction != 0) {
        capture.frames[capture.count] = pc;
        capture.count += 1;
    }
    if capture.count == MAX_FRAMES {
        URC_END_OF_STACK
    } else {
        URC_NO_REASON
    }
}

fn record(desc: usize, size: usize) {
    // A thread being torn down has no usable slot; its request is simply not counted.
    let Ok(entered) = RECORDING.try_with(|recording| !recording.replace(true)) else {
        return;
    };
    if !entered {
        return;
    }
    let mut capture = Capture {
        frames: [0; MAX_FRAMES],
        count: 0,
    };
    unsafe {
        _Unwind_Backtrace(capture_frame, (&mut capture as *mut Capture).cast());
    }
    let site = Site {
        desc,
        size,
        frames: capture.frames,
    };
    *SITES
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get_or_insert_with(FxHashMap::default)
        .entry(site)
        .or_insert(0) += 1;
    REGISTER_EXIT_HOOK.call_once(|| {
        unsafe { libc::atexit(write_report) };
    });
    RECORDING.with(|recording| recording.set(false));
}

pub(super) fn record_managed(size: usize, desc: *const GcDesc) {
    record(desc as usize, size);
}

extern "C" fn write_report() {
    let Some(path) = std::env::var_os("TARO_ALLOC_PROFILE") else {
        return;
    };
    RECORDING.with(|recording| recording.set(true));
    let slide = unsafe { _dyld_get_image_vmaddr_slide(0) } as usize;
    let sites = SITES
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .take()
        .unwrap_or_default();
    let mut output = String::new();
    for (site, count) in sites {
        let addresses = site
            .frames
            .iter()
            .take_while(|pc| **pc != 0)
            .map(|pc| format!("\"{:#x}\"", pc.wrapping_sub(slide)))
            .collect::<Vec<_>>()
            .join(",");
        let (desc, desc_size, node_count, pointers) = if site.desc == 0 {
            (0, 0, 0, false)
        } else {
            let desc = site.desc as *const GcDesc;
            let (size, nodes) = unsafe { ((*desc).size, (*desc).node_count) };
            (
                site.desc.wrapping_sub(slide),
                size,
                nodes,
                desc_has_pointers(desc),
            )
        };
        let _ = writeln!(
            output,
            "{{\"count\":{count},\"size\":{},\"desc\":\"{desc:#x}\",\"desc_size\":{desc_size},\"desc_nodes\":{node_count},\"pointers\":{pointers},\"frames\":[{addresses}]}}",
            site.size,
        );
    }
    if let Err(error) = std::fs::write(&path, output) {
        eprintln!("alloc-profile: cannot write report: {error}");
    }
}

struct ProfilingAllocator;

unsafe impl GlobalAlloc for ProfilingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record(0, layout.size());
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record(0, layout.size());
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        record(0, new_size);
        unsafe { System.realloc(pointer, layout, new_size) }
    }
}

#[global_allocator]
static ALLOCATOR: ProfilingAllocator = ProfilingAllocator;
