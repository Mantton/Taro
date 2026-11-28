use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

mod build_identity;

fn command_output(program: &Path, arguments: &[&str]) -> Option<String> {
    let output = Command::new(program).args(arguments).output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn main() {
    #[cfg(feature = "llvm")]
    let llvm_version = build_llvm_shim();
    let rustc = env::var_os("RUSTC").map(PathBuf::from).expect("RUSTC");
    let mut settings = vec![
        (
            "rustc".into(),
            command_output(&rustc, &["--version", "--verbose"]).expect("rustc version"),
        ),
        ("target".into(), env::var("TARGET").expect("TARGET")),
    ];
    #[cfg(feature = "llvm")]
    settings.push(("llvm".into(), llvm_version));
    settings.extend(env::vars().filter(|(name, _)| name.starts_with("CARGO_FEATURE_")));
    let identity = build_identity::compute(
        Path::new(&env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR")),
        &settings,
    )
    .expect("cannot fingerprint compiler build inputs");
    for path in identity.watched_paths {
        println!("cargo:rerun-if-changed={}", path.display());
    }
    println!("cargo:rustc-env=TARO_COMPILER_ID={}", identity.stamp);
}

#[cfg(feature = "llvm")]
fn build_llvm_shim() -> String {
    println!("cargo:rerun-if-env-changed=DEP_LLVM_22_CONFIG_PATH");
    println!("cargo:rerun-if-changed=native/llvm_shims.cpp");

    let llvm_config = env::var_os("DEP_LLVM_22_CONFIG_PATH")
        .map(PathBuf::from)
        .expect("llvm-sys did not provide its selected llvm-config path");
    let llvm_version = command_output(&llvm_config, &["--version"]).expect("LLVM version");
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
    link_ffi_if_llvm_uses_it(&llvm_config);
    llvm_version
}

/// LLVM's interpreter calls libffi when LLVM was configured with
/// `LLVM_ENABLE_FFI`, which `llvm-config --system-libs` does not report.
/// Homebrew's LLVM enables it; the SDK's LLVM does not, and must not link
/// libffi, whose soname differs between Linux distributions. inkwell's own
/// unconditional libffi link is disabled (`no-libffi-linking`).
#[cfg(feature = "llvm")]
fn link_ffi_if_llvm_uses_it(llvm_config: &Path) {
    let config = command_output(llvm_config, &["--cmakedir"])
        .map(|dir| PathBuf::from(dir).join("LLVMConfig.cmake"));
    let enabled = match config.as_deref().map(std::fs::read_to_string) {
        Some(Ok(text)) => {
            println!("cargo:rerun-if-changed={}", config.as_ref().unwrap().display());
            text.lines().any(|line| {
                line.trim()
                    .strip_prefix("set(LLVM_ENABLE_FFI ")
                    .and_then(|rest| rest.strip_suffix(')'))
                    .is_some_and(|value| {
                        matches!(value.to_ascii_uppercase().as_str(), "ON" | "TRUE" | "YES" | "1")
                    })
            })
        }
        // Without the CMake package, assume FFI as inkwell used to.
        _ => true,
    };
    if enabled {
        println!("cargo:rustc-link-lib=dylib=ffi");
    }
}
