use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use crate::{
    cfg::TargetInfo, compile::config::PackageKind, compile::context::GlobalContext,
    error::CompileResult,
};
use inkwell::targets::TargetMachine;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LinkPlatform {
    Darwin,
    Linux,
    OtherUnix,
    Windows,
    Unknown,
}

impl LinkPlatform {
    fn from_target(target: &TargetInfo) -> Self {
        if target.matches_os("macos") {
            Self::Darwin
        } else if target.matches_os("linux") {
            Self::Linux
        } else if target.family == "unix" {
            Self::OtherUnix
        } else if target.family == "windows" {
            Self::Windows
        } else {
            Self::Unknown
        }
    }
}

#[derive(Debug)]
struct LinkPlan {
    program: PathBuf,
    args: Vec<OsString>,
}

impl LinkPlan {
    fn command(&self) -> Command {
        let mut command = Command::new(&self.program);
        command.args(&self.args);
        command
    }
}

#[allow(clippy::too_many_arguments)]
fn build_link_plan(
    target_triple: &str,
    host_triple: &str,
    linker: Option<&Path>,
    sysroot: Option<&Path>,
    darwin_sdk: Option<&Path>,
    darwin_linker: Option<&Path>,
    object_inputs: &[PathBuf],
    library_inputs: &[PathBuf],
    output: &Path,
) -> Result<LinkPlan, String> {
    let target = TargetInfo::from_triple(target_triple);
    let host = TargetInfo::from_triple(host_triple);
    let target_platform = LinkPlatform::from_target(&target);
    let host_platform = LinkPlatform::from_target(&host);

    match target_platform {
        LinkPlatform::Windows => {
            return Err(format!(
                "linking target `{target_triple}` is not supported by the Unix linker backend"
            ));
        }
        LinkPlatform::OtherUnix | LinkPlatform::Unknown => {
            return Err(format!(
                "linking target `{target_triple}` is not supported yet; supported target OSes are Darwin and Linux"
            ));
        }
        LinkPlatform::Darwin | LinkPlatform::Linux => {}
    }

    if target_platform != host_platform && (linker.is_none() || sysroot.is_none()) {
        return Err(format!(
            "cross-OS linking `{host_triple}` -> `{target_triple}` requires both --linker and --sysroot"
        ));
    }

    let same_arch = target.matches_arch(&host.arch);
    if target_platform == LinkPlatform::Linux
        && host_platform == LinkPlatform::Linux
        && !same_arch
        && linker.is_none()
        && sysroot.is_none()
    {
        return Err(format!(
            "cross-architecture Linux linking `{host_triple}` -> `{target_triple}` requires --linker or --sysroot"
        ));
    }

    let mut args = vec![OsString::from(format!("--target={target_triple}"))];
    match target_platform {
        LinkPlatform::Darwin => {
            let sdk = sysroot.or(darwin_sdk).ok_or_else(|| {
                format!(
                    "linking Darwin target `{target_triple}` requires a macOS SDK; pass --sysroot when xcrun is unavailable"
                )
            })?;
            args.push(OsString::from("-isysroot"));
            args.push(sdk.as_os_str().to_owned());
            args.push(OsString::from(format!("-Wl,-syslibroot,{}", sdk.display())));
        }
        LinkPlatform::Linux => {
            if let Some(sysroot) = sysroot {
                args.push(OsString::from(format!("--sysroot={}", sysroot.display())));
            }
        }
        LinkPlatform::OtherUnix | LinkPlatform::Windows | LinkPlatform::Unknown => unreachable!(),
    }

    // Order matters for static libraries on Unix linkers: objects first, then archives.
    args.extend(object_inputs.iter().map(|path| path.as_os_str().to_owned()));
    args.extend(
        library_inputs
            .iter()
            .map(|path| path.as_os_str().to_owned()),
    );

    if target_platform == LinkPlatform::Linux {
        // Some math intrinsics lower to libm, while panic unwinding and the
        // runtime's dynamic-loader support require libunwind and libdl.
        args.extend(["-lm", "-lunwind", "-ldl"].map(OsString::from));
    }

    args.push(OsString::from("-o"));
    args.push(output.as_os_str().to_owned());

    let program = match (linker, target_platform) {
        (Some(linker), _) => linker.to_path_buf(),
        (None, LinkPlatform::Darwin) => darwin_linker
            .ok_or_else(|| {
                format!(
                    "linking Darwin target `{target_triple}` requires Apple Clang from xcrun; pass --linker when xcrun is unavailable"
                )
            })?
            .to_path_buf(),
        (None, _) => PathBuf::from("clang"),
    };

    Ok(LinkPlan { program, args })
}

/// Link all known object files into a single executable for the current package.
/// Assumes `taro_start`/`main` are already present in the LLVM output.
pub fn link_executable(gcx: GlobalContext) -> CompileResult<Option<PathBuf>> {
    // Only produce an executable for executable/both packages.
    match gcx.config.kind {
        PackageKind::Executable | PackageKind::Both => {}
        PackageKind::Library => return Ok(None),
    }

    let objects = gcx.all_object_files();
    if objects.is_empty() {
        gcx.dcx()
            .emit_error("no object files available for linking".into(), None);
        return Err(crate::error::ReportedError);
    }

    let mut obj_inputs: Vec<PathBuf> = vec![];
    let mut lib_inputs: Vec<PathBuf> = vec![];
    for path in objects {
        match path.extension().and_then(|e| e.to_str()) {
            Some("a") | Some("lib") => lib_inputs.push(path),
            _ => obj_inputs.push(path),
        }
    }
    if obj_inputs.is_empty() {
        gcx.dcx()
            .emit_error("no object files available for linking".into(), None);
        return Err(crate::error::ReportedError);
    }

    let out_dir = gcx.output_root().clone();
    if let Err(e) = fs::create_dir_all(&out_dir) {
        let msg = format!("failed to create output directory: {e}");
        gcx.dcx().emit_error(msg.into(), None);
        return Err(crate::error::ReportedError);
    }
    let base = out_dir
        .parent()
        .map(|p| p.to_path_buf())
        .unwrap_or(out_dir.clone());
    let output = gcx
        .config
        .executable_out
        .clone()
        .unwrap_or_else(|| base.join(gcx.config.identifier.as_ref()));
    if let Some(parent) = output.parent() {
        if let Err(e) = fs::create_dir_all(parent) {
            let msg = format!("failed to create output directory: {e}");
            gcx.dcx().emit_error(msg.into(), None);
            return Err(crate::error::ReportedError);
        }
    }

    let target_triple = gcx.store.target_layout.triple_string();
    let host_triple = TargetMachine::get_default_triple()
        .as_str()
        .to_string_lossy()
        .into_owned();
    let linker = gcx.store.linker.borrow().clone();
    let sysroot = gcx.store.linker_sysroot.borrow().clone();
    let target_info = TargetInfo::from_triple(&target_triple);
    let darwin_sdk = if target_info.matches_os("macos") && sysroot.is_none() {
        macos_sdk_path()
    } else {
        None
    };
    // A random `clang` earlier in PATH may be too old to map the host Darwin
    // version to the matching macOS deployment target. The SDK's Apple Clang
    // and linker are versioned together, so use that pair by default.
    let darwin_linker = if target_info.matches_os("macos") && linker.is_none() {
        macos_clang_path()
    } else {
        None
    };
    let plan = build_link_plan(
        &target_triple,
        &host_triple,
        linker.as_deref(),
        sysroot.as_deref(),
        darwin_sdk.as_deref(),
        darwin_linker.as_deref(),
        &obj_inputs,
        &lib_inputs,
        &output,
    )
    .map_err(|message| {
        gcx.dcx().emit_error(message, None);
        crate::error::ReportedError
    })?;
    let mut cmd = plan.command();

    match cmd.status() {
        Ok(status) if status.success() => Ok(Some(output)),
        Ok(status) => {
            let msg = format!("linker failed with status {status}");
            gcx.dcx().emit_error(msg.into(), None);
            Err(crate::error::ReportedError)
        }
        Err(e) => {
            let msg = format!("failed to invoke linker: {e}");
            gcx.dcx().emit_error(msg.into(), None);
            Err(crate::error::ReportedError)
        }
    }
}

fn macos_sdk_path() -> Option<PathBuf> {
    xcrun_path(&["--sdk", "macosx", "--show-sdk-path"])
}

fn macos_clang_path() -> Option<PathBuf> {
    xcrun_path(&["--sdk", "macosx", "--find", "clang"])
}

fn xcrun_path(arguments: &[&str]) -> Option<PathBuf> {
    #[cfg(not(target_os = "macos"))]
    {
        let _ = arguments;
        return None;
    }

    #[cfg(target_os = "macos")]
    {
        let out = Command::new("xcrun").args(arguments).output().ok()?;
        if !out.status.success() {
            return None;
        }
        let raw = String::from_utf8_lossy(&out.stdout);
        let path = raw.trim();
        if path.is_empty() {
            None
        } else {
            Some(PathBuf::from(path))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{build_link_plan, link_executable};
    use crate::{
        PackageIndex,
        compile::{
            config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
            context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        },
        diagnostics::DiagCtx,
    };
    use rustc_hash::FxHashMap;
    use std::{path::PathBuf, rc::Rc};

    fn args(plan: &super::LinkPlan) -> Vec<String> {
        plan.args
            .iter()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect()
    }

    fn with_test_gcx<R>(kind: PackageKind, f: impl for<'ctx> FnOnce(Gcx<'ctx>) -> R) -> R {
        let root = std::env::temp_dir().join(format!(
            "taro-link-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        std::fs::create_dir_all(&root).expect("temp dir");

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx, store);
        let config = icx.store.arenas.configs.alloc(Config {
            name: "link-test".into(),
            identifier: "link-test".into(),
            src: PathBuf::from("link-test.tr"),
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind,
            executable_out: None,
            no_std_prelude: true,
            is_script: true,
            profile: BuildProfile::Debug,
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
                debug_info: Default::default(),
            },
            test_mode: false,
            std_mode: StdMode::BootstrapStd,
            is_std_provider: false,
        });

        f(Gcx::new(&icx, config))
    }

    #[test]
    fn library_without_object_files_skips_linking() {
        with_test_gcx(PackageKind::Library, |gcx| {
            let result = link_executable(gcx);

            match result {
                Ok(None) => {}
                Ok(Some(path)) => panic!("library unexpectedly linked {}", path.display()),
                Err(_) => panic!("library link should be skipped"),
            }
            assert_eq!(gcx.dcx().error_count(), 0);
        });
    }

    #[test]
    fn executable_without_object_files_errors() {
        with_test_gcx(PackageKind::Executable, |gcx| {
            let result = link_executable(gcx);

            assert!(result.is_err());
            assert_eq!(gcx.dcx().error_count(), 1);
        });
    }

    #[test]
    fn darwin_cross_arch_plan_uses_target_and_sdk() {
        let objects = vec![PathBuf::from("main.o")];
        let libraries = vec![PathBuf::from("libtaro_runtime.a")];
        let plan = build_link_plan(
            "x86_64-apple-darwin",
            "arm64-apple-darwin25.5.0",
            None,
            None,
            Some(std::path::Path::new("/SDKs/MacOSX.sdk")),
            Some(std::path::Path::new("/Xcode/usr/bin/clang")),
            &objects,
            &libraries,
            std::path::Path::new("app"),
        )
        .expect("same-OS Darwin cross-link plan");
        let args = args(&plan);

        assert_eq!(plan.program, PathBuf::from("/Xcode/usr/bin/clang"));
        assert!(args.contains(&"--target=x86_64-apple-darwin".into()));
        assert!(
            args.windows(2)
                .any(|pair| pair == ["-isysroot", "/SDKs/MacOSX.sdk"])
        );
        assert!(
            args.iter().position(|arg| arg == "main.o")
                < args.iter().position(|arg| arg == "libtaro_runtime.a")
        );
        assert!(!args.contains(&"-lm".into()));
    }

    #[test]
    fn linux_plan_uses_explicit_linker_sysroot_and_runtime_libraries() {
        let plan = build_link_plan(
            "aarch64-unknown-linux-gnu",
            "x86_64-apple-darwin",
            Some(std::path::Path::new("/cross/bin/clang")),
            Some(std::path::Path::new("/cross/sysroot")),
            None,
            None,
            &[PathBuf::from("main.o")],
            &[PathBuf::from("libtaro_runtime.a")],
            std::path::Path::new("app"),
        )
        .expect("configured cross-OS Linux plan");
        let args = args(&plan);

        assert_eq!(plan.program, PathBuf::from("/cross/bin/clang"));
        assert!(args.contains(&"--target=aarch64-unknown-linux-gnu".into()));
        assert!(args.contains(&"--sysroot=/cross/sysroot".into()));
        assert!(args.contains(&"-lm".into()));
        assert!(args.contains(&"-lunwind".into()));
        assert!(args.contains(&"-ldl".into()));
    }

    #[test]
    fn cross_os_plan_requires_linker_and_sysroot() {
        let error = build_link_plan(
            "aarch64-unknown-linux-gnu",
            "arm64-apple-darwin",
            None,
            None,
            None,
            None,
            &[],
            &[],
            std::path::Path::new("app"),
        )
        .expect_err("unconfigured cross-OS link must fail");

        assert!(error.contains("requires both --linker and --sysroot"));
    }

    #[test]
    fn windows_target_is_rejected_by_unix_linker_backend() {
        let error = build_link_plan(
            "x86_64-pc-windows-msvc",
            "x86_64-unknown-linux-gnu",
            Some(std::path::Path::new("clang")),
            Some(std::path::Path::new("sysroot")),
            None,
            None,
            &[],
            &[],
            std::path::Path::new("app"),
        )
        .expect_err("Windows link is outside this backend");

        assert!(error.contains("not supported by the Unix linker backend"));
    }

    #[test]
    fn explicit_darwin_linker_overrides_xcrun_default() {
        let plan = build_link_plan(
            "arm64-apple-darwin25.5.0",
            "arm64-apple-darwin25.5.0",
            Some(std::path::Path::new("/custom/bin/clang")),
            None,
            Some(std::path::Path::new("/SDKs/MacOSX.sdk")),
            Some(std::path::Path::new("/Xcode/usr/bin/clang")),
            &[PathBuf::from("main.o")],
            &[],
            std::path::Path::new("app"),
        )
        .expect("explicit Darwin linker should remain authoritative");

        assert_eq!(plan.program, PathBuf::from("/custom/bin/clang"));
    }

    #[test]
    fn darwin_plan_requires_xcrun_linker_when_not_explicit() {
        let error = build_link_plan(
            "arm64-apple-darwin25.5.0",
            "arm64-apple-darwin25.5.0",
            None,
            None,
            Some(std::path::Path::new("/SDKs/MacOSX.sdk")),
            None,
            &[PathBuf::from("main.o")],
            &[],
            std::path::Path::new("app"),
        )
        .expect_err("Darwin linking needs an SDK-matched default linker");

        assert!(error.contains("requires Apple Clang from xcrun"));
    }
}
