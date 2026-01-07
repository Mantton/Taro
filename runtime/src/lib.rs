pub mod garbage_collector;
pub mod gc_pointer;
pub mod runtime;
pub mod slice;
pub mod string;

pub use garbage_collector::*;
pub use gc_pointer::*;
pub use runtime::*;
pub use string::*;

#[unsafe(no_mangle)]
pub extern "C" fn __rt__debug_print_ptr(ptr: *const u8) {
    eprintln!("PTR: {:p}", ptr);
}
