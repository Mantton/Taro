fn main() {
    println!("cargo:rerun-if-changed=native/unwind_probe.c");
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let family = std::env::var("CARGO_CFG_TARGET_FAMILY").unwrap();
    if family.split(',').any(|value| value == "unix")
        && matches!(arch.as_str(), "aarch64" | "x86_64")
    {
        cc::Build::new()
            .file("native/unwind_probe.c")
            .flag_if_supported("-fno-omit-frame-pointer")
            .flag_if_supported("-fno-optimize-sibling-calls")
            .compile("taro_unwind_probe");
    }
}
