use std::{
    collections::HashSet,
    env,
    ffi::OsString,
    path::{Path, PathBuf},
    process::Command,
};

const LLVM_PREFIX_ENV: &str = "LLVM_SYS_221_PREFIX";

fn command_output(program: &Path, arguments: &[&str]) -> Option<String> {
    let output = Command::new(program).args(arguments).output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn path_command(name: &str) -> Option<PathBuf> {
    let path = env::var_os("PATH")?;
    env::split_paths(&path)
        .map(|directory| directory.join(name))
        .find(|candidate| candidate.is_file())
}

fn llvm_config_candidates() -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    if let Some(prefix) = env::var_os(LLVM_PREFIX_ENV) {
        candidates.push(PathBuf::from(prefix).join("bin/llvm-config"));
    }
    if let Some(config) = env::var_os("DEP_LLVM_22_CONFIG_PATH") {
        candidates.push(PathBuf::from(config));
    }
    for name in [
        "llvm-config-22",
        "llvm-config-22.1",
        "llvm-config22",
        "llvm-config",
    ] {
        if let Some(candidate) = path_command(name) {
            candidates.push(candidate);
        }
    }

    if let Some(brew) = path_command("brew") {
        for formula in ["llvm@22", "llvm"] {
            if let Some(prefix) = command_output(&brew, &["--prefix", formula]) {
                candidates.push(PathBuf::from(prefix).join("bin/llvm-config"));
            }
        }
    }

    for prefix in [
        "/opt/homebrew/opt/llvm@22",
        "/opt/homebrew/opt/llvm",
        "/usr/local/opt/llvm@22",
        "/usr/local/opt/llvm",
        "/usr/lib/llvm-22",
    ] {
        candidates.push(Path::new(prefix).join("bin/llvm-config"));
    }
    candidates
}

fn find_llvm_config() -> PathBuf {
    let mut seen = HashSet::<OsString>::new();
    let mut attempts = Vec::new();
    for candidate in llvm_config_candidates() {
        if !seen.insert(candidate.clone().into_os_string()) || !candidate.is_file() {
            continue;
        }
        let Some(version) = command_output(&candidate, &["--version"]) else {
            attempts.push(format!("{} (unusable)", candidate.display()));
            continue;
        };
        if version == "22.1" || version.starts_with("22.1.") {
            return candidate;
        }
        attempts.push(format!("{} (version {version})", candidate.display()));
    }

    panic!(
        "could not find LLVM 22.1.x for the ThinLTO shim; set {LLVM_PREFIX_ENV} to the LLVM prefix. Checked: {}",
        if attempts.is_empty() {
            "no llvm-config candidates".to_owned()
        } else {
            attempts.join(", ")
        }
    );
}

fn main() {
    println!("cargo:rerun-if-env-changed={LLVM_PREFIX_ENV}");
    println!("cargo:rerun-if-env-changed=DEP_LLVM_22_CONFIG_PATH");
    println!("cargo:rerun-if-env-changed=PATH");
    println!("cargo:rerun-if-changed=native/llvm_shims.cpp");

    let llvm_config = find_llvm_config();
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
