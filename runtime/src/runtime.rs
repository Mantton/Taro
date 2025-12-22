#[unsafe(no_mangle)]
pub extern "C" fn __rt__exit(code: i32) {
    std::process::exit(code);
}
