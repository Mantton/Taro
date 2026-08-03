use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

fn command_output(program: &Path, arguments: &[&str]) -> Option<String> {
    let output = Command::new(program).args(arguments).output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn main() {
    println!("cargo:rerun-if-env-changed=DEP_LLVM_22_CONFIG_PATH");
    println!("cargo:rerun-if-changed=native/llvm_shims.cpp");

    let llvm_config = env::var_os("DEP_LLVM_22_CONFIG_PATH")
        .map(PathBuf::from)
        .expect("llvm-sys did not provide its selected llvm-config path");
    let include_dir = command_output(&llvm_config, &["--includedir"])
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            panic!(
                "{} did not report an include directory",
                llvm_config.display()
            )
        });

    let mut build = cc::Build::new();
    build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .include(include_dir)
        .define("__STDC_CONSTANT_MACROS", None)
        .define("__STDC_FORMAT_MACROS", None)
        .define("__STDC_LIMIT_MACROS", None)
        .file("native/llvm_shims.cpp");
    build.compile("taro_llvm_shims");
}
