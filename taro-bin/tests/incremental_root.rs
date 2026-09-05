use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    time::{SystemTime, UNIX_EPOCH},
};

struct TempProject(PathBuf);

impl TempProject {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "taro-root-incremental-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        fs::create_dir_all(root.join("src")).expect("project source directory");
        fs::create_dir_all(root.join("dep/src")).expect("dependency source directory");
        fs::write(
            root.join("package.toml"),
            "[package]\nname = \"github.com/example/root-cache\"\nkind = \"executable\"\n\n[require]\n\"github.com/example/root-cache-dep\" = { path = \"dep\", alias = \"dep\" }\n",
        )
        .expect("manifest");
        fs::write(
            root.join("dep/package.toml"),
            "[package]\nname = \"github.com/example/root-cache-dep\"\nkind = \"library\"\n",
        )
        .expect("dependency manifest");
        fs::write(
            root.join("dep/src/lib.tr"),
            "public func dependencyValue() -> int32 { 1 }\n",
        )
        .expect("dependency source");
        Self(root)
    }

    fn write_source(&self, marker: &str) {
        fs::write(
            self.0.join("src/main.tr"),
            format!(
                "func main() {{\n    print(\"{marker}\\n\")\n}}\n\n@test\nfunc alpha() {{}}\n\n@test\nfunc beta() {{}}\n"
            ),
        )
        .expect("source");
    }

    fn write_dependency(&self, value: i32) {
        fs::write(
            self.0.join("dep/src/lib.tr"),
            format!("public func dependencyValue() -> int32 {{ {value} }}\n"),
        )
        .expect("dependency source");
    }
}

impl Drop for TempProject {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

fn distribution_is_available(dist: &Path) -> bool {
    dist.join("lib/taro/runtime/libtaro_runtime.a").is_file()
        && dist
            .join("lib/taro/runtime/libtaro_runtime.a.manifest.toml")
            .is_file()
        && directory_contains(&dist.join("lib/taro/std"), "std.taro_meta")
}

fn directory_contains(root: &Path, file_name: &str) -> bool {
    let Ok(entries) = fs::read_dir(root) else {
        return false;
    };
    entries.filter_map(Result::ok).any(|entry| {
        let path = entry.path();
        path.file_name().and_then(|name| name.to_str()) == Some(file_name)
            || (path.is_dir() && directory_contains(&path, file_name))
    })
}

fn run_taro(dist: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_taro-bin"))
        .env("TARO_HOME", dist)
        .args(args)
        .output()
        .expect("run taro")
}

fn assert_success(output: &Output) {
    assert!(
        output.status.success(),
        "command failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn small_enum_abi_round_trips_through_cached_dependency() {
    let dist = workspace_root().join("dist");
    if !distribution_is_available(&dist) {
        eprintln!("skipping enum ABI integration test: dist artifacts are unavailable");
        return;
    }
    let project = TempProject::new();
    fs::write(
        project.0.join("dep/src/lib.tr"),
        r#"
public enum Small { case empty; case value(int64) }
@noinline
public func produce(_ value: int64) -> Result[int64, int64] {
    if value < 0 { return .err(value) }
    return .ok(value + 1)
}
@noinline
public func consume(_ value: Result[int64, int64]) -> int64 {
    match value {
        case .ok(v) => return v * 2
        case .err(e) => return e * 3
    }
}
@noinline
public func empty() -> Small { .empty }
@noinline
public func word(_ value: int64) -> Small { .value(value) }
@noinline
public func smallValue(_ value: Small) -> int64 {
    match value {
        case .empty => return 0
        case .value(v) => return v
    }
}
@noinline
public func managed(_ value: int64) -> Result[&int64, int64] {
    var stored = value
    return .ok(&stored)
}
@noinline
public func readManaged(_ value: Result[&int64, int64]) -> int64 {
    std.runtime.collect()
    match value {
        case .ok(reference) => return *reference
        case .err(error) => return error
    }
}
"#,
    )
    .expect("enum dependency");
    let source = r#"
import dep.{produce, consume, empty, word, smallValue, managed, readManaged}
func main() {
    var sum: int64 = 0
    var i: int64 = 0
    while i < 100 {
        sum += consume(produce(i)) + consume(produce(-1))
        sum += smallValue(empty()) + smallValue(word(i))
        i += 1
    }
    let reference = managed(42)
    std.runtime.collect()
    sum += readManaged(reference)
    printf("%v\n", sum)
}
"#;
    let source_path = project.0.join("src/main.tr");
    let executable = project.0.join("enum-test");
    for profile in ["0", "2"] {
        for cached in [false, true] {
            fs::write(&source_path, format!("{source}\n// {profile} {cached}\n"))
                .expect("enum caller");
            let output = run_taro(
                &dist,
                &[
                    "build",
                    &project.0.to_string_lossy(),
                    "--release",
                    "-O",
                    profile,
                    "--timings",
                    "-o",
                    &executable.to_string_lossy(),
                ],
            );
            assert_success(&output);
            if cached {
                assert!(
                    stderr(&output)
                        .contains("Reusing (metadata+object) – github.com/example/root-cache-dep")
                );
            }
            let result = Command::new(&executable)
                .env("TARO_WORKERS", "1")
                .env("TARO_GC_STRESS", "1")
                .output()
                .expect("execute enum test");
            assert_success(&result);
            assert_eq!(String::from_utf8_lossy(&result.stdout).trim(), "14792");
        }
    }
}

#[test]
fn bounded_leaf_inlines_from_source_and_cached_dependency() {
    let dist = workspace_root().join("dist");
    if !distribution_is_available(&dist) {
        eprintln!("skipping inline CLI integration test: dist artifacts are unavailable");
        return;
    }
    let project = TempProject::new();
    fs::write(
        project.0.join("dep/src/lib.tr"),
        r#"
public func mix(_ a: &mut uint64, _ b: &mut uint64, _ c: &mut uint64, _ d: &mut uint64) {
    *a += *b
    *c += *d
    *b = (*b << 13) | (*b >> 51)
    *b ^= *a
    *d = (*d << 16) | (*d >> 48)
    *d ^= *c
    *a = (*a << 32) | (*a >> 32)
    *c += *b
    *a += *d
    *b = (*b << 17) | (*b >> 47)
    *b ^= *c
    *d = (*d << 21) | (*d >> 43)
    *d ^= *a
    *c = (*c << 32) | (*c >> 32)
}
@noinline
public func barrier(_ value: uint64) -> uint64 { value }
"#,
    )
    .expect("leaf dependency");
    let source = r#"
import dep.{mix, barrier}
func main() {
    var a = barrier(1_u64)
    var b = 2_u64
    var c = 3_u64
    var d = 4_u64
    mix(&mut a, &mut b, &mut c, &mut d)
    printf("%v %v %v %v\n", a, b, c, d)
}
"#;
    let source_path = project.0.join("src/main.tr");
    fs::write(&source_path, source).expect("caller");
    let path = project.0.to_string_lossy();
    let executable = project.0.join("leaf-test");
    let executable_path = executable.to_string_lossy();
    for cached in [false, true] {
        if cached {
            // Recompile only the caller so its inliner must use hydrated MIR.
            fs::write(&source_path, format!("{source}\n// rebuild caller\n"))
                .expect("changed caller");
        }
        let output = run_taro(
            &dist,
            &[
                "build",
                &path,
                "--release",
                "-O2",
                "--dump-llvm",
                "--timings",
                "-o",
                &executable_path,
            ],
        );
        assert_success(&output);
        let log = stderr(&output);
        if cached {
            assert!(log.contains("Reusing (metadata+object) – github.com/example/root-cache-dep"));
        }
        let caller_ir = log.rsplit("=== LLVM IR for ").next().expect("caller IR");
        assert!(caller_ir.contains("define "), "missing LLVM dump");
        let calls = |name: &str| {
            caller_ir.lines().any(|line| {
                (line.contains("call ") || line.contains("invoke ")) && line.contains(name)
            })
        };
        assert!(!calls("__mix__"), "leaf call survived (cached={cached})");
        assert!(calls("__barrier__"), "@noinline call disappeared");
        let result = Command::new(&executable)
            .output()
            .expect("execute leaf test");
        assert_success(&result);
        assert_eq!(
            String::from_utf8_lossy(&result.stdout).trim(),
            "12885164039 2147893258 70411693850624 562655657991"
        );
    }
}

#[test]
fn root_and_script_commands_reuse_incremental_artifacts() {
    let dist = workspace_root().join("dist");
    if !distribution_is_available(&dist) {
        eprintln!("skipping incremental CLI integration test: dist artifacts are unavailable");
        return;
    }

    let project = TempProject::new();
    project.write_source("cache-v1");
    let project_path = project.0.to_string_lossy().into_owned();
    let root_name = "github.com/example/root-cache";
    let dependency_name = "github.com/example/root-cache-dep";

    let first_check = run_taro(&dist, &["check", &project_path, "--timings"]);
    assert_success(&first_check);
    assert!(stderr(&first_check).contains(&format!("Checking – {root_name}")));

    let second_check = run_taro(&dist, &["check", &project_path, "--timings"]);
    assert_success(&second_check);
    assert!(stderr(&second_check).contains(&format!("Reusing (metadata) – {root_name}")));

    project.write_dependency(2);
    let changed_dependency = run_taro(&dist, &["check", &project_path, "--timings"]);
    assert_success(&changed_dependency);
    let changed_dependency_stderr = stderr(&changed_dependency);
    assert!(changed_dependency_stderr.contains(&format!("Checking – {dependency_name}")));
    assert!(changed_dependency_stderr.contains(&format!("Checking – {root_name}")));

    let release_check = run_taro(&dist, &["check", &project_path, "--timings", "--release"]);
    assert_success(&release_check);
    assert!(stderr(&release_check).contains(&format!("Checking – {root_name}")));

    let overflow_check = run_taro(
        &dist,
        &["check", &project_path, "--timings", "--no-overflow-checks"],
    );
    assert_success(&overflow_check);
    assert!(stderr(&overflow_check).contains(&format!("Checking – {root_name}")));

    let cold_check = run_taro(
        &dist,
        &["check", &project_path, "--timings", "--no-incremental"],
    );
    assert_success(&cold_check);
    let cold_stderr = stderr(&cold_check);
    assert!(cold_stderr.contains(&format!("Checking – {root_name}")));
    assert!(!cold_stderr.contains(&format!("Reusing (metadata) – {root_name}")));

    project.write_source("cache-v2");
    let changed_check = run_taro(&dist, &["check", &project_path, "--timings"]);
    assert_success(&changed_check);
    assert!(stderr(&changed_check).contains(&format!("Checking – {root_name}")));

    let first_exe = project.0.join("first-output");
    let second_exe = project.0.join("second-output");
    let first_exe_arg = first_exe.to_string_lossy().into_owned();
    let second_exe_arg = second_exe.to_string_lossy().into_owned();
    let first_build = run_taro(
        &dist,
        &["build", &project_path, "--timings", "-o", &first_exe_arg],
    );
    assert_success(&first_build);
    let second_build = run_taro(
        &dist,
        &["build", &project_path, "--timings", "-o", &second_exe_arg],
    );
    assert_success(&second_build);
    assert!(stderr(&second_build).contains(&format!("Reusing (metadata+object) – {root_name}")));
    assert!(first_exe.is_file());
    assert!(second_exe.is_file());

    let cold_build = run_taro(
        &dist,
        &[
            "build",
            &project_path,
            "--timings",
            "--no-incremental",
            "-o",
            &second_exe_arg,
        ],
    );
    assert_success(&cold_build);
    let cold_build_stderr = stderr(&cold_build);
    assert!(cold_build_stderr.contains(&format!("Compiling – {root_name}")));
    assert!(!cold_build_stderr.contains(&format!("Reusing (metadata+object) – {root_name}")));

    let run = run_taro(&dist, &["run", &project_path, "--timings"]);
    assert_success(&run);
    assert!(stderr(&run).contains(&format!("Reusing (metadata+object) – {root_name}")));
    assert!(String::from_utf8_lossy(&run.stdout).contains("cache-v2"));

    let first_test = run_taro(
        &dist,
        &["test", &project_path, "--timings", "--filter", "alpha"],
    );
    assert_success(&first_test);
    let repeated_test = run_taro(
        &dist,
        &["test", &project_path, "--timings", "--filter", "alpha"],
    );
    assert_success(&repeated_test);
    assert!(
        stderr(&repeated_test).contains(&format!("Reusing tests (metadata+object) – {root_name}"))
    );
    let changed_selection = run_taro(
        &dist,
        &["test", &project_path, "--timings", "--filter", "beta"],
    );
    assert_success(&changed_selection);
    assert!(stderr(&changed_selection).contains(&format!("Compiling tests – {root_name}")));

    let script = project.0.join("standalone.tr");
    fs::write(&script, "func main() { print(\"script\\n\") }\n").expect("script");
    let script_path = script.to_string_lossy().into_owned();
    let first_script_check = run_taro(&dist, &["check", &script_path, "--timings"]);
    assert_success(&first_script_check);
    let second_script_check = run_taro(&dist, &["check", &script_path, "--timings"]);
    assert_success(&second_script_check);
    assert!(stderr(&second_script_check).contains("Reusing (metadata) – standalone"));

    let script_exe = project.0.join("standalone-output");
    let script_exe_arg = script_exe.to_string_lossy().into_owned();
    let first_script_build = run_taro(
        &dist,
        &["build", &script_path, "--timings", "-o", &script_exe_arg],
    );
    assert_success(&first_script_build);
    let second_script_build = run_taro(
        &dist,
        &["build", &script_path, "--timings", "-o", &script_exe_arg],
    );
    assert_success(&second_script_build);
    assert!(stderr(&second_script_build).contains("Reusing (metadata+object) – standalone"));
}
