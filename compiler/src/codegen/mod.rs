pub mod abi;
pub mod artifact;
pub mod link;
pub mod llvm;
pub mod mangle;
pub mod target;

use std::{ffi::CString, ptr, sync::Once};

static CONFIGURE_OPTIMIZATION_REMARKS: Once = Once::new();

/// Enable LLVM's passed, missed, and analysis optimization remarks.
///
/// LLVM exposes remark filtering through process-global command-line state in
/// its C API. The CLI calls this at most once, before creating LLVM contexts;
/// compiler-library and language-server sessions never enable it implicitly.
pub fn configure_optimization_remarks(pass_filter: &str) -> Result<(), String> {
    let raw_arguments = [
        "taro".to_owned(),
        format!("--pass-remarks={pass_filter}"),
        format!("--pass-remarks-missed={pass_filter}"),
        format!("--pass-remarks-analysis={pass_filter}"),
    ];
    let arguments = raw_arguments
        .iter()
        .map(|argument| {
            CString::new(argument.as_str())
                .map_err(|_| "optimization remark filter cannot contain a NUL byte".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;

    CONFIGURE_OPTIMIZATION_REMARKS.call_once(|| {
        let argument_pointers = arguments
            .iter()
            .map(|argument| argument.as_ptr())
            .collect::<Vec<_>>();

        // SAFETY: every pointer references a live NUL-terminated CString for
        // the duration of the call, and LLVM copies/parses the arguments
        // synchronously. This function is serialized by `Once`.
        unsafe {
            inkwell::llvm_sys::support::LLVMParseCommandLineOptions(
                argument_pointers.len() as i32,
                argument_pointers.as_ptr(),
                ptr::null(),
            );
        }
    });
    Ok(())
}
