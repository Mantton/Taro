use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

#[path = "../../test_support.rs"]
mod test_support;
use test_support::TempDir;

struct TempProject(TempDir);

impl TempProject {
    fn new() -> Self {
        let root = TempDir::new("root-incremental");
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

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .to_path_buf()
}

// Validation can use a matched candidate SDK while preserving installed dist.
fn distribution_root() -> PathBuf {
    std::env::var_os("TARO_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|| workspace_root().join("dist"))
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

#[test]
fn crlf_sources_match_lf_execution_and_diagnostics() {
    let dist = distribution_root();
    assert!(
        distribution_is_available(&dist),
        "build dist before CLI integration tests"
    );
    let project = TempProject::new();
    let source_path = project.0.join("src/main.tr");
    let executable = project.0.join("crlf-test");
    let source = "//+cfg family(\"unix\")\nfunc main() {\n    value := 40\n        + 2\n    /* first line\n       second line */\n    assert(value == 42, \"line continuation\")\n    print(\"PASS: source line endings\\n\")\n}\n";
    fs::write(
        project.0.join("src/excluded.tr"),
        "//+cfg os(\"windows\")\r\ninvalid excluded source\r\n",
    )
    .unwrap();
    for input in [&source_path, &project.0.to_path_buf()] {
        for text in [source.to_string(), source.replace('\n', "\r\n")] {
            fs::write(&source_path, text).unwrap();
            let output = run_taro(
                &dist,
                &[
                    "run",
                    &input.to_string_lossy(),
                    "--no-incremental",
                    "-o",
                    &executable.to_string_lossy(),
                ],
            );
            assert_success(&output);
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                "PASS: source line endings\n"
            );
        }
    }
    let invalid = "func main() {\n    var value: int32 = true\n}\n";
    let mut diagnostics = Vec::new();
    for text in [invalid.to_string(), invalid.replace('\n', "\r\n")] {
        fs::write(&source_path, text).unwrap();
        let output = run_taro(
            &dist,
            &["check", &source_path.to_string_lossy(), "--no-incremental"],
        );
        assert!(!output.status.success());
        assert!(stderr(&output).contains(":2:"));
        diagnostics.push(output.stderr);
    }
    assert_eq!(diagnostics[0], diagnostics[1]);
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn enum_abi_round_trips_through_cached_dependency() {
    let dist = distribution_root();
    if !distribution_is_available(&dist) {
        eprintln!("skipping enum ABI integration test: dist artifacts are unavailable");
        return;
    }
    let project = TempProject::new();
    fs::write(
        project.0.join("dep/src/lib.tr"),
        r#"
public enum Small { case empty; case value(int64) }
public enum Wide { case empty; case pair(int64, int64); case text(string) }
@inline
public func echo[T](_ value: T) -> T { value }
@noinline
public func cachedIdentity[Unused, T](_ value: T, _ unused: Unused) -> T {
    echo(value)
}
@noinline
public func wide(_ value: int64) -> Wide { .pair(value, value + 1) }
@noinline
public func wrapWide(_ value: int64) -> Result[Wide, int64] { .ok(wide(value)) }
@noinline
public func unwrapWide(_ value: Result[Wide, int64]) -> Wide {
    match value {
        case .ok(found) => return found
        case .err(_) => return .empty
    }
}

@noinline
public func wideValue(_ value: Wide) -> int64 {
    match value {
        case .empty => return 0
        case .pair(a, b) => return a + b
        case .text(text) => return if text == "cached" { 9 } else { -1000 }
    }
}

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
public func managed(_ value: &int64) -> Result[&int64, int64] {
    return .ok(value)
}
@noinline
public func readManaged(_ value: Result[&int64, int64]) -> int64 {
    match value {
        case .ok(reference) => return *reference
        case .err(error) => return error
    }
}
"#,
    )
    .expect("enum dependency");
    let source = r#"
import dep::{Wide, cachedIdentity, wrapWide, unwrapWide, wideValue, produce, consume, empty, word, smallValue, managed, readManaged}
func main() {
    // Imported generic callers must specialize their helper's arguments using
    // the caller's indices, including cached MIR and multiword value payloads.
    var payload: Wide = .pair(12, 13)
    assert(wideValue(cachedIdentity(payload, false)) == 25, "cached generic payload")
    assert(cachedIdentity(true, 17_i32), "cached generic scalar")
    var sum: int64 = 0
    var wideValues: List[Wide] = List::new()
    var i: int64 = 0
    while i < 100 {
        sum += consume(produce(i)) + consume(produce(-1))
        sum += smallValue(empty()) + smallValue(word(i))
        wideValues.append(unwrapWide(wrapWide(i)))
        sum += wideValue(wideValues[i as usize]) + wideValue(unwrapWide(.err(-1))) + wideValue(.text("cached"))
        i += 1
    }
    // Exercise a reference payload alongside inline multiword payloads.
    var stored: int64 = 42
    assert(*cachedIdentity(&stored, true) == 42, "cached generic reference")
    reference := managed(&stored)
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
                .output()
                .expect("execute enum test");
            assert_success(&result);
            assert_eq!(String::from_utf8_lossy(&result.stdout).trim(), "25692");
        }
    }
}

#[test]
fn bounded_leaf_inlines_from_source_and_cached_dependency() {
    let dist = distribution_root();
    if !distribution_is_available(&dist) {
        eprintln!("skipping inline CLI integration test: dist artifacts are unavailable");
        return;
    }
    let project = TempProject::new();
    fs::write(
        project.0.join("dep/src/lib.tr"),
        r#"
public func mix(_ a: &uint64, _ b: &uint64, _ c: &uint64, _ d: &uint64) {
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
import dep::{mix, barrier}
func main() {
    var a = barrier(1_u64)
    var b = 2_u64
    var c = 3_u64
    var d = 4_u64
    mix(&a, &b, &c, &d)
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
    let dist = distribution_root();
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

#[test]
fn generic_dependency_survives_cold_warm_and_edited_builds() {
    let dist = distribution_root();
    if !distribution_is_available(&dist) {
        eprintln!("skipping generic dependency integration test: dist artifacts are unavailable");
        return;
    }
    let project = TempProject::new();
    let dependency = |separator: &str, greeting: &str| {
        format!(
            r#"
public interface Describe {{
    func describe() -> string
}}
public struct Pair[T] {{
    public first: T
    public second: T
}}
extend[T: Describe] Pair[T] {{
    public func joined() -> string {{
        return self.first.describe() + "{separator}" + self.second.describe()
    }}
}}
public final class Box[T] {{
    public value: T
}}
extend[T] Box[T] {{
    public init(_ value: T) {{ self.value = value }}
}}
public func mapAll[T, U, F: Fn(T) -> U](_ items: std::collections::List[T], _ f: F) -> std::collections::List[U] {{
    var out = std::collections::List[U]::new()
    for item in items {{ out.append(f(item)) }}
    return out
}}
public static var GREETING: string = "{greeting}"
"#
        )
    };
    let application = |marker: &str| {
        format!(
            r##"
import dep::{{Describe, Pair, Box, mapAll, GREETING}}
struct Tag {{ name: string }}
conform Tag to Describe {{
    public func describe() -> string {{ return "<" + self.name + ">" }}
}}
func main() {{
    boxed := Box[Pair[Tag]](Pair[Tag] {{ first: Tag {{ name: "a" }}, second: Tag {{ name: "b" }} }})
    var numbers = std::collections::List[int32]::new()
    numbers.append(1)
    numbers.append(2)
    labels := mapAll(numbers, (n: int32) => std::sprintf("#%d", n))
    std::printf("%s %s %s %s {marker}\n", boxed.value.joined(), labels[0], labels[1], GREETING)
}}
"##
        )
    };
    let executable = project.0.join("generic-test");
    for profile in ["0", "2"] {
        // A fresh cache per profile: the first build of each is cold.
        let _ = fs::remove_dir_all(project.0.join("target"));
        let steps = [
            ("+", "v1", "app-v1", false, "<a>+<b> #1 #2 v1 app-v1"),
            ("+", "v1", "app-v1", true, "<a>+<b> #1 #2 v1 app-v1"),
            ("&", "v2", "app-v1", false, "<a>&<b> #1 #2 v2 app-v1"),
            ("&", "v2", "app-v2", true, "<a>&<b> #1 #2 v2 app-v2"),
        ];
        for (separator, greeting, marker, dependency_reused, expected) in steps {
            fs::write(
                project.0.join("dep/src/lib.tr"),
                dependency(separator, greeting),
            )
            .expect("generic dependency");
            fs::write(project.0.join("src/main.tr"), application(marker))
                .expect("generic application");
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
            assert_eq!(
                stderr(&output)
                    .contains("Reusing (metadata+object) – github.com/example/root-cache-dep"),
                dependency_reused,
                "-O{profile} step {expected:?}\n{}",
                stderr(&output)
            );
            let result = Command::new(&executable)
                .env("TARO_WORKERS", "1")
                .output()
                .expect("execute generic test");
            assert_success(&result);
            assert_eq!(String::from_utf8_lossy(&result.stdout).trim(), expected);
        }
    }
}

/// An instance call graph may recurse across packages even though the package
/// dependency graph is acyclic: the library calls a concrete client's witness.
/// Compare cold metadata in both root dependency orders, then hydrate those
/// templates while recompiling only the caller. The MIR unit test separately
/// reverses body visitation order, which cannot reverse a legal package DAG.
#[test]
fn cross_package_recursive_templates_keep_cached_metadata_deterministic() {
    use std::collections::BTreeMap;
    fn metadata(root: &Path, directory: &Path, result: &mut BTreeMap<PathBuf, Vec<u8>>) {
        for entry in fs::read_dir(directory).expect("metadata directory") {
            let path = entry.expect("metadata entry").path();
            if path.is_dir() {
                metadata(root, &path, result);
            } else if path
                .extension()
                .is_some_and(|extension| extension == "taro_meta")
                && path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| {
                        name.starts_with("root-cache-dep-")
                            || name.starts_with("root-cache-partner-")
                    })
            {
                result.insert(
                    path.strip_prefix(root).unwrap().to_path_buf(),
                    fs::read(path).unwrap(),
                );
            }
        }
    }
    let dist = distribution_root();
    if !distribution_is_available(&dist) {
        eprintln!("skipping recursive cache test: dist artifacts are unavailable");
        return;
    }
    let project = TempProject::new();
    fs::create_dir_all(project.0.join("partner/src")).unwrap();
    fs::write(
        project.0.join("dep/src/lib.tr"),
        r#"
public interface Step {
    static func next(_ depth: int32) -> int32
}
@inline
public func entry[S: Step](_ depth: int32) -> int32 {
    if depth == 0 { return 7 }
    return S::next(depth - 1) + 1
}
"#,
    )
    .unwrap();
    fs::write(
        project.0.join("partner/package.toml"),
        "[package]\nname = \"github.com/example/root-cache-partner\"\nkind = \"library\"\n",
    )
    .unwrap();
    fs::write(
        project.0.join("partner/src/lib.tr"),
        "public func marker() -> int32 { 13 }\n",
    )
    .unwrap();
    let source = r#"
import dep::{Step, entry}
import partner::marker
struct Loop {}
conform Loop to Step {
    @inline
    static func next(_ depth: int32) -> int32 {
        if depth == 0 { return 7 }
        return entry[Loop](depth - 1) + 1
    }
}
func main() {
    assert(entry[Loop](20) == 27, "cross-package recursion")
    assert(marker() == 13, "independent sibling dependency")
}
"#;
    let dependency =
        "\"github.com/example/root-cache-dep\" = { path = \"dep\", alias = \"dep\" }\n";
    let partner =
        "\"github.com/example/root-cache-partner\" = { path = \"partner\", alias = \"partner\" }\n";
    let mut expected = None;
    let mut expected_mir = None;
    for reverse in [false, true] {
        for directory in ["target", "dep/target", "partner/target"] {
            let path = project.0.join(directory);
            if path.exists() {
                fs::remove_dir_all(path).unwrap();
            }
        }
        let requirements = if reverse {
            format!("{partner}{dependency}")
        } else {
            format!("{dependency}{partner}")
        };
        fs::write(project.0.join("package.toml"), format!("[package]\nname = \"github.com/example/root-cache\"\nkind = \"executable\"\n[require]\n{requirements}")).unwrap();
        for cached in [false, true] {
            fs::write(
                project.0.join("src/main.tr"),
                format!("{source}// cached={cached}\n"),
            )
            .unwrap();
            let executable = project.0.join("recursive-test");
            let output = run_taro(
                &dist,
                &[
                    "build",
                    &project.0.to_string_lossy(),
                    "--release",
                    "-O3",
                    "--timings",
                    "--dump-mir",
                    "-o",
                    &executable.to_string_lossy(),
                ],
            );
            assert_success(&output);
            if cached {
                for package in ["root-cache-dep", "root-cache-partner"] {
                    assert!(
                        stderr(&output).contains(&format!(
                            "Reusing (metadata+object) – github.com/example/{package}"
                        )),
                        "{}",
                        stderr(&output)
                    );
                }
            }
            let mut mir = BTreeMap::new();
            for section in stderr(&output).split("\n=== Final instance MIR: ").skip(1) {
                let (name, text) = section.split_once(" ===\n").expect("MIR heading");
                if ["__entry__", "__next__", "__main__"]
                    .iter()
                    .any(|part| name.contains(part))
                {
                    let body = text
                        .lines()
                        .take_while(|line| line.is_empty() || line.starts_with("    "))
                        .collect::<Vec<_>>()
                        .join("\n");
                    assert!(body.contains("bb"), "MIR blocks");
                    mir.insert(name.to_owned(), body.trim_end().to_owned());
                }
            }
            assert!(!mir.is_empty(), "the recursive caller must emit MIR");
            if let Some(previous) = &expected_mir {
                assert_eq!(
                    &mir, previous,
                    "concrete recursive MIR changed with cache or dependency order"
                );
            } else {
                expected_mir = Some(mir);
            }
            let mut snapshot = BTreeMap::new();
            metadata(&project.0, &project.0, &mut snapshot);
            assert_eq!(
                snapshot.len(),
                2,
                "both dependency MIR/fingerprint artifacts"
            );
            if let Some(previous) = &expected {
                assert!(
                    &snapshot == previous,
                    "canonical dependency metadata changed with cache or root dependency order: {:?}",
                    snapshot.keys()
                );
            } else {
                expected = Some(snapshot);
            }
            let result = Command::new(executable)
                .env("TARO_WORKERS", "1")
                .env("TARO_GC_STRESS", "1")
                .output()
                .unwrap();
            assert_success(&result);
        }
    }
}

#[test]
fn derived_codable_survives_cached_dependency_metadata() {
    let dist = distribution_root();
    assert!(
        distribution_is_available(&dist),
        "build dist before CLI integration tests"
    );
    let project = TempProject::new();
    fs::write(
        project.0.join("dep/src/lib.tr"),
        r#"
import std::encoding::Codable
public struct Item: Codable { public text: string; public count: int32; }
public struct Plain {}
public class EncodingObject[T]: std::encoding::Encodable { public value: T }
extend[T] EncodingObject[T] { public required init(_ value: T) { self.value = value } }
public class CodingObject[T]: Codable { public value: T }
type DecodeResult[T, E] = Result[T, E]
public class SizedObject[const N: usize]: std::encoding::Decodable { public value: int32; public stamp: usize }
extend[const M: usize] SizedObject[M] {
    public init(_ value: int32) { self.value = value; self.stamp = M }
    public required convenience init[D: std::encoding::Decoder](from decoder: D) -> DecodeResult[Self, D::Error] {
        item := Item::decode(from: decoder)!
        self.init(item.count)
    }
}
public class CustomObject: std::encoding::Decodable { public value: int32; private opaque: Plain }
extend CustomObject {
    public required init[D: std::encoding::Decoder](from decoder: D) -> Result[Self, D::Error] {
        item := Item::decode(from: decoder)!
        self.value = item.count + 1
        self.opaque = Plain {}
    }
}
public enum Event[T]: Codable { case item { value: &T }; case pair(T, T) }
public struct Envelope[T, Phantom]: Codable { public value: T; public note: string?; }
public func echo[T: Codable](_ value: T) -> T {
    text := std::json::encode(&value).unwrap()
    std::json::decode[T](text).unwrap()
}
"#,
    )
    .unwrap();
    let source = r#"
import dep::{Item, Plain, Envelope, Event, EncodingObject, CodingObject, CustomObject, SizedObject, echo}
final class EncodingLeaf[T]: EncodingObject[List[T]] { extra: int32 = 13 }
final class CodingLeaf[T]: CodingObject[List[T]] { extra: string = "cached ".concat("default") }
final class CustomLeaf: CustomObject { extra: int32 = 13 }
final class SizedLeaf[const N: usize]: SizedObject[N] { extra: int32 = 13 }
func main() {
    value := std::json::decode[Envelope[Item, Plain]](
        "{\"value\":{\"text\":\"cached\\u0020record\",\"count\":42}}",
    ).unwrap()
    result := echo(value)
    std::runtime::collect()
    assert(result.value.text == "cached record" && result.value.count == 42, "cached generic codec")
    assert(result.note.isNone(), "absent optional field")
    assert(std::json::encode(&result).unwrap() == "{\"value\":{\"text\":\"cached record\",\"count\":42},\"note\":null}", "declaration order")
    event := echo(Event[Item]::item(value: &result.value))
    std::runtime::collect()
    match event {
        case .item { value } => assert(value.text == "cached record" && value.count == 42, "cached enum with reference payload")
        case _ => panic("cached enum variant")
    }
    pair := echo(Event[int32]::pair(1, 2))
    match pair {
        case .pair(left, right) => assert(left == 1 && right == 2, "cached tuple payload")
        case _ => panic("cached tuple variant")
    }
    leaf := EncodingLeaf[int32]([1, 2])
    leaf.extra = 17
    var object: EncodingObject[List[int32]] = leaf
    assert(std::json::encode(&object).unwrap() == "{\"value\":[1,2]}", "cached generic class encoder")
    assert(std::json::encode(&leaf).unwrap() == "{\"value\":[1,2]}", "inherited class encoder keeps base generic coordinates")
    decoded := std::json::decode[CodingLeaf[int32]]("{\"value\":[3,4]}").unwrap()
    custom := std::json::decode[CustomLeaf]("{\"text\":\"manual\",\"count\":41}").unwrap()
    sized := std::json::decode[SizedLeaf[7]]("{\"text\":\"sized\",\"count\":41}").unwrap()
    std::runtime::collect()
    assert(sized.value == 41 && sized.stamp == 7 && sized.extra == 13, "cached renamed const initializer and Result alias")
    var decodedBase: CodingObject[List[int32]] = decoded
    assert(decoded.value[1] == 4 && decoded.extra == "cached default", "cached inherited class decoder")
    assert(decodedBase is CodingLeaf[int32], "cached subclass descriptor")
    assert(custom.value == 42 && custom.extra == 13, "cached custom required decoding initializer")
    print("PASS: derived Codable metadata\n")
}
"#;
    for optimization in ["0", "3"] {
        for warm in [false, true] {
            // Change only the root: the second invocation must reconstruct
            // synthetic codec signatures and MIR from dependency metadata.
            fs::write(
                project.0.join("src/main.tr"),
                format!("{source}\n// warm={warm}\n"),
            )
            .unwrap();
            let output = Command::new(env!("CARGO_BIN_EXE_taro-bin"))
                .env("TARO_HOME", &dist)
                .env("TARO_WORKERS", "1")
                .env("TARO_GC_STRESS", "1")
                .args([
                    "run",
                    &project.0.to_string_lossy(),
                    "--release",
                    "-O",
                    optimization,
                    "--timings",
                ])
                .output()
                .expect("run derived codec fixture");
            assert_success(&output);
            assert_eq!(
                String::from_utf8_lossy(&output.stdout),
                "PASS: derived Codable metadata\n"
            );
            if warm {
                assert!(
                    String::from_utf8_lossy(&output.stderr)
                        .contains("Reusing (metadata+object) – github.com/example/root-cache-dep"),
                    "dependency must be reused: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        }
    }
}
