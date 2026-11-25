use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use compiler::{compile::config::PackageKind, constants::MANIFEST_FILE, error::ReportedError, package::manifest::Manifest};

use crate::{
    TestArgs,
    command::{CommandOutcome, CommandResult},
};

static NEXT_TEMP_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DocTest {
    pub source_path: PathBuf,
    /// 1-based line number of the opening fence in `source_path`.
    pub fence_line: usize,
    /// Original 1-based line number in `source_path` for each line of `code`.
    pub line_numbers: Vec<usize>,
    pub lines: Vec<String>,
    pub ignore: bool,
    pub no_run: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct WrappedDocTest {
    source: String,
    /// `line_map[generated_line_1_based - 1]` is the original 1-based line in `source_path`.
    line_map: Vec<usize>,
}

struct TempDirGuard(PathBuf);

impl TempDirGuard {
    fn new(prefix: &str) -> Result<Self, String> {
        let base = std::env::temp_dir();
        let pid = std::process::id();
        let seq = NEXT_TEMP_ID.fetch_add(1, Ordering::Relaxed);
        let dir = base.join(format!("{prefix}-{pid}-{seq}"));
        fs::create_dir_all(&dir)
            .map_err(|e| format!("failed to create temp directory '{}': {e}", dir.display()))?;
        Ok(Self(dir))
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn run(arguments: TestArgs) -> CommandResult {
    let target_path = arguments.common.path.clone();
    let filter = arguments.normalized_test_filter();

    let mut tests = discover_doctests(&target_path).map_err(|err| {
        eprintln!("error: {err}");
        ReportedError
    })?;

    if let Some(filter) = filter.as_deref() {
        let needle = filter.to_ascii_lowercase();
        tests.retain(|test| {
            let label = format!("{} (line {})", test.source_path.display(), test.fence_line);
            label.to_ascii_lowercase().contains(&needle)
        });
    }

    println!("running {} doc tests", tests.len());
    if tests.is_empty() {
        println!("\ndoc test result: ok. 0 passed; 0 failed; 0 ignored");
        return Ok(CommandOutcome::Success);
    }

    let taro_exe = std::env::current_exe().map_err(|err| {
        eprintln!("error: failed to locate current taro binary: {err}");
        ReportedError
    })?;

    let work_dir = TempDirGuard::new("taro-doctest").map_err(|err| {
        eprintln!("error: {err}");
        ReportedError
    })?;


    let mut passed = 0usize;
    let mut failed = 0usize;
    let mut ignored = 0usize;
    let mut failure_reports: Vec<(String, String)> = Vec::new();

    for (idx, test) in tests.iter().enumerate() {
        let label = format!("{} (line {})", test.source_path.display(), test.fence_line);
        if test.ignore {
            println!("test {label} ... ignored");
            ignored += 1;
            continue;
        }

        let case_dir = work_dir.path().join(format!("case_{idx}"));
        if let Err(err) = fs::create_dir_all(&case_dir) {
            eprintln!("error: failed to create doctest dir: {err}");
            return Err(ReportedError);
        }

        let wrapped = wrap_doctest_source(test);
        let (build_target, temp_src_path) = if let Some((pkg_name, pkg_root)) = detect_library_package(&test.source_path).map_err(|err| {
            eprintln!("error: {err}");
            ReportedError
        })? {
            let src_dir = case_dir.join("src");
            if let Err(err) = fs::create_dir_all(&src_dir) {
                eprintln!("error: failed to create doctest src dir: {err}");
                return Err(ReportedError);
            }
            // The normal package resolver derives the import name from the final
            // component of the library's identifier.
            let manifest = format!(
                "[package]\nname = \"local.test/doctests/example_{idx}\"\nkind = \"executable\"\n\n[require]\n{} = {{ path = {} }}\n",
                toml::Value::String(pkg_name),
                toml::Value::String(pkg_root.to_string_lossy().into_owned()),
            );
            if let Err(err) = fs::write(case_dir.join(MANIFEST_FILE), manifest) {
                eprintln!("error: failed to write doctest manifest: {err}");
                return Err(ReportedError);
            }
            let main_path = src_dir.join("main.tr");
            if let Err(err) = fs::write(&main_path, &wrapped.source) {
                eprintln!("error: failed to write doctest source: {err}");
                return Err(ReportedError);
            }
            (case_dir.clone(), main_path)
        } else {
            let src_path = case_dir.join(format!("doctest_{idx}.tr"));
            if let Err(err) = fs::write(&src_path, &wrapped.source) {
                eprintln!("error: failed to write doctest source: {err}");
                return Err(ReportedError);
            }
            (src_path.clone(), src_path)
        };

        let output_exe = case_dir.join(format!("doctest_{idx}"));
        let mut build_cmd = Command::new(&taro_exe);
        if test.no_run {
            build_cmd.arg("check").arg(&build_target);
        } else {
            build_cmd
                .arg("build")
                .arg(&build_target)
                .arg("--output")
                .arg(&output_exe);
        }
        forward_common_flags(&mut build_cmd, &arguments.common);

        let build_out = match build_cmd.output() {
            Ok(out) => out,
            Err(err) => {
                println!("test {label} ... FAILED");
                failed += 1;
                failure_reports.push((label, format!("failed to invoke compiler: {err}")));
                continue;
            }
        };

        if !build_out.status.success() {
            println!("test {label} ... FAILED");
            failed += 1;
            let raw = combine_output(&build_out.stdout, &build_out.stderr);
            let remapped = remap_locations(&raw, &temp_src_path, &test.source_path, &wrapped.line_map);
            failure_reports.push((label, remapped));
            continue;
        }

        if test.no_run {
            println!("test {label} ... ok");
            passed += 1;
            continue;
        }

        let run_out = match Command::new(&output_exe).output() {
            Ok(out) => out,
            Err(err) => {
                println!("test {label} ... FAILED");
                failed += 1;
                failure_reports.push((label, format!("failed to execute doctest binary: {err}")));
                continue;
            }
        };

        if run_out.status.success() {
            println!("test {label} ... ok");
            passed += 1;
        } else {
            println!("test {label} ... FAILED");
            failed += 1;
            let raw = combine_output(&run_out.stdout, &run_out.stderr);
            let remapped = remap_locations(&raw, &temp_src_path, &test.source_path, &wrapped.line_map);
            let detail = if remapped.trim().is_empty() {
                format!(
                    "doctest exited with status {} at {}:{}",
                    run_out.status,
                    test.source_path.display(),
                    test.fence_line
                )
            } else {
                remapped
            };
            failure_reports.push((label, detail));
        }
    }

    if !failure_reports.is_empty() {
        println!("\nfailures:");
        for (label, detail) in &failure_reports {
            println!("\n---- {label} ----");
            println!("{}", detail.trim_end());
        }
    }

    let status_word = if failed == 0 { "ok" } else { "FAILED" };
    println!(
        "\ndoc test result: {status_word}. {passed} passed; {failed} failed; {ignored} ignored"
    );

    if failed == 0 {
        Ok(CommandOutcome::Success)
    } else {
        Ok(CommandOutcome::ChildExit(1))
    }
}

fn forward_common_flags(cmd: &mut Command, common: &crate::CommonCompileArgs) {
    if let Some(std_path) = &common.std_path {
        cmd.arg("--std-path").arg(std_path);
    }
    if let Some(runtime_path) = &common.runtime_path {
        cmd.arg("--runtime-path").arg(runtime_path);
    }
    if let Some(target) = &common.target {
        cmd.arg("--target").arg(target);
    }
    if let Some(linker) = &common.linker {
        cmd.arg("--linker").arg(linker);
    }
    if let Some(sysroot) = &common.sysroot {
        cmd.arg("--sysroot").arg(sysroot);
    }
    if common.release {
        cmd.arg("--release");
    }
    if common.overflow_checks {
        cmd.arg("--overflow-checks");
    }
    if common.no_overflow_checks {
        cmd.arg("--no-overflow-checks");
    }
}

fn detect_library_package(source: &Path) -> Result<Option<(String, PathBuf)>, String> {
    let path = source.canonicalize().map_err(|err| err.to_string())?;
    for directory in path.ancestors().skip(1) {
        let manifest = directory.join(MANIFEST_FILE);
        if manifest.is_file() {
            let package = Manifest::parse(manifest)?.package;
            if matches!(package.kind, PackageKind::Library | PackageKind::Both) && package.name != "github.com/taro/std" {
                return Ok(Some((package.name.to_string(), directory.to_owned())));
            }
            break;
        }
    }
    Ok(None)
}

fn combine_output(stdout: &[u8], stderr: &[u8]) -> String {
    let mut out = String::new();
    let s_out = String::from_utf8_lossy(stdout);
    let s_err = String::from_utf8_lossy(stderr);
    if !s_out.trim().is_empty() {
        out.push_str(&s_out);
        if !out.ends_with('\n') {
            out.push('\n');
        }
    }
    if !s_err.trim().is_empty() {
        out.push_str(&s_err);
    }
    out
}

pub(crate) fn discover_doctests(root: &Path) -> Result<Vec<DocTest>, String> {
    if !root.exists() {
        return Err(format!("path '{}' does not exist", root.display()));
    }

    let mut files = Vec::new();
    if root.is_file() {
        files.push(root.to_path_buf());
    } else {
        collect_doc_files(root, &mut files)?;
    }
    files.sort();

    let mut tests = Vec::new();
    for file in files {
        let ext = file.extension().and_then(|e| e.to_str()).unwrap_or("");
        let content = fs::read_to_string(&file)
            .map_err(|e| format!("failed to read '{}': {e}", file.display()))?;
        match ext {
            "md" => tests.extend(extract_markdown_doctests(&file, &content)),
            "tr" => tests.extend(extract_taro_doc_comment_tests(&file, &content)),
            _ => {}
        }
    }
    Ok(tests)
}

fn collect_doc_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("failed to read directory '{}': {e}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("failed to read entry in '{}': {e}", dir.display()))?;
        let path = entry.path();
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        if path.is_dir() {
            if matches!(name_str.as_ref(), "target" | ".git" | "node_modules" | "dist") {
                continue;
            }
            collect_doc_files(&path, out)?;
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("tr" | "md")
        ) {
            out.push(path);
        }
    }
    Ok(())
}

fn parse_fence_info(info: &str) -> Option<(bool, bool)> {
    let tokens: Vec<&str> = info
        .split(|c: char| c == ',' || c.is_ascii_whitespace())
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    if tokens.first().copied() != Some("taro") {
        return None;
    }
    let mut ignore = false;
    let mut no_run = false;
    for token in &tokens[1..] {
        match *token {
            "ignore" => ignore = true,
            "no_run" => no_run = true,
            _ => {}
        }
    }
    Some((ignore, no_run))
}

fn extract_fenced_blocks(source_path: &Path, numbered_lines: &[(usize, String)]) -> Vec<DocTest> {
    let mut tests = Vec::new();
    let mut active: Option<(usize, usize, bool, bool, Vec<usize>, Vec<String>)> = None;

    for (line_no, text) in numbered_lines {
        let trimmed = text.trim_start();
        if let Some((fence_len, fence_line, ignore, no_run, mut line_numbers, mut lines)) =
            active.take()
        {
            let backticks = trimmed.bytes().take_while(|&b| b == b'`').count();
            if backticks >= fence_len && trimmed[backticks..].trim().is_empty() {
                tests.push(DocTest {
                    source_path: source_path.to_path_buf(),
                    fence_line,
                    line_numbers,
                    lines,
                    ignore,
                    no_run,
                });
            } else {
                line_numbers.push(*line_no);
                lines.push(text.clone());
                active = Some((fence_len, fence_line, ignore, no_run, line_numbers, lines));
            }
        } else {
            let backticks = trimmed.bytes().take_while(|&b| b == b'`').count();
            if backticks >= 3 {
                let info = trimmed[backticks..].trim();
                if let Some((ignore, no_run)) = parse_fence_info(info) {
                    active = Some((backticks, *line_no, ignore, no_run, Vec::new(), Vec::new()));
                }
            }
        }
    }

    tests
}

pub(crate) fn extract_markdown_doctests(source_path: &Path, content: &str) -> Vec<DocTest> {
    let numbered: Vec<(usize, String)> = content
        .lines()
        .enumerate()
        .map(|(idx, line)| (idx + 1, line.to_string()))
        .collect();
    extract_fenced_blocks(source_path, &numbered)
}

pub(crate) fn extract_taro_doc_comment_tests(source_path: &Path, content: &str) -> Vec<DocTest> {
    let mut tests = Vec::new();
    let mut block: Vec<(usize, String)> = Vec::new();

    for (idx, line) in content.lines().enumerate() {
        let trimmed = line.trim_start();
        if let Some(rest) = trimmed.strip_prefix("///") {
            // Skip `////` divider comments.
            if rest.starts_with('/') {
                if !block.is_empty() {
                    tests.extend(extract_fenced_blocks(source_path, &block));
                    block.clear();
                }
                continue;
            }
            let stripped = rest.strip_prefix(' ').unwrap_or(rest);
            block.push((idx + 1, stripped.to_string()));
        } else if !block.is_empty() {
            tests.extend(extract_fenced_blocks(source_path, &block));
            block.clear();
        }
    }
    if !block.is_empty() {
        tests.extend(extract_fenced_blocks(source_path, &block));
    }

    tests
}

fn has_main_function(lines: &[String]) -> bool {
    lines.iter().any(|line| {
        let trimmed = line.trim_start();
        trimmed.starts_with("func main(")
            || trimmed.starts_with("public func main(")
            || trimmed.starts_with("async func main(")
            || trimmed.starts_with("public async func main(")
    })
}

fn wrap_doctest_source(test: &DocTest) -> WrappedDocTest {
    if has_main_function(&test.lines) {
        let mut source = test.lines.join("\n");
        source.push('\n');
        return WrappedDocTest {
            source,
            line_map: test.line_numbers.clone(),
        };
    }

    let mut imports = Vec::new();
    let mut body = Vec::new();
    let mut in_imports = true;
    for (line, &line_no) in test.lines.iter().zip(&test.line_numbers) {
        let trimmed = line.trim_start();
        if in_imports && (trimmed.is_empty() || trimmed.starts_with("import ")) {
            imports.push((line.clone(), line_no));
        } else {
            in_imports = false;
            body.push((line.clone(), line_no));
        }
    }

    let mut out_lines = Vec::new();
    let mut line_map = Vec::new();
    for (line, line_no) in imports {
        out_lines.push(line);
        line_map.push(line_no);
    }

    out_lines.push("func main() {".to_string());
    line_map.push(test.fence_line);

    for (line, line_no) in body {
        out_lines.push(line);
        line_map.push(line_no);
    }

    out_lines.push("}".to_string());
    line_map.push(test.line_numbers.last().copied().unwrap_or(test.fence_line));

    let mut source = out_lines.join("\n");
    source.push('\n');
    WrappedDocTest { source, line_map }
}

fn remap_locations(
    output: &str,
    temp_path: &Path,
    original_path: &Path,
    line_map: &[usize],
) -> String {
    let mut patterns = vec![temp_path.to_string_lossy().to_string()];
    if let Ok(canon) = fs::canonicalize(temp_path) {
        let canon_str = canon.to_string_lossy().to_string();
        if !patterns.contains(&canon_str) {
            patterns.push(canon_str);
        }
    }
    if let Ok(cwd) = std::env::current_dir() {
        if let Ok(relative) = temp_path.strip_prefix(cwd) {
            patterns.push(relative.to_string_lossy().into_owned());
        }
    }
    if temp_path.ends_with("src/main.tr") {
        patterns.push("src/main.tr".into());
    } else if let Some(name) = temp_path.file_name() {
        patterns.push(name.to_string_lossy().into_owned());
    }
    patterns.sort_by_key(|p| std::cmp::Reverse(p.len()));
    patterns.dedup();
    let original_str = original_path.to_string_lossy();

    // Scan once so replacement text (which itself can end in main.tr) is
    // never remapped. Only replace complete diagnostic paths with a line.
    let mut out = String::with_capacity(output.len());
    let mut rest = output;
    while !rest.is_empty() {
        let boundary = rest.len() == output.len()
            || output[..output.len() - rest.len()].ends_with(|c: char| c.is_whitespace() || matches!(c, '(' | '\'' | '"'));
        let found = boundary.then(|| patterns.iter().find(|p| {
            rest.strip_prefix(p.as_str()).and_then(|r| r.strip_prefix(':'))
                .is_some_and(|r| r.starts_with(|c: char| c.is_ascii_digit()))
        })).flatten();
        let Some(needle) = found else {
            let ch = rest.chars().next().unwrap();
            out.push(ch);
            rest = &rest[ch.len_utf8()..];
            continue;
        };
        out.push_str(&original_str);
        rest = &rest[needle.len()..];
        if let Some(after_colon) = rest.strip_prefix(':') {
            let digits_len = after_colon
                .bytes()
                .take_while(|b| b.is_ascii_digit())
                .count();
            if digits_len > 0 {
                if let Ok(gen_line) = after_colon[..digits_len].parse::<usize>() {
                    let mapped = gen_line
                        .checked_sub(1)
                        .and_then(|idx| line_map.get(idx).copied())
                        .unwrap_or(gen_line);
                    out.push(':');
                    out.push_str(&mapped.to_string());
                    rest = &after_colon[digits_len..];
                }
            }
        }
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remaps_relative_package_spans_only_for_the_wrapper() {
        let tmp = std::env::current_dir().unwrap().join("target/case_0/src/main.tr");
        let output = " -> target/case_0/src/main.tr:2:3\n -> src/main.tr:1:8\n -> dep/src/main.tr:1:9";
        assert_eq!(remap_locations(output, &tmp, Path::new("docs/main.tr"), &[12, 13]),
            " -> docs/main.tr:13:3\n -> docs/main.tr:12:8\n -> dep/src/main.tr:1:9");
    }

    #[test]
    fn extracts_markdown_fences_and_preserves_lines() {
        let md = "# Guide\n\n```taro\nx := 1\nassert(x == 1)\n```\n\n```taro,ignore\ninvalid syntax(\n```\n\n```sh\necho hi\n```\n";
        let tests = extract_markdown_doctests(Path::new("guide.md"), md);
        assert_eq!(tests.len(), 2);
        assert_eq!(tests[0].fence_line, 3);
        assert_eq!(tests[0].line_numbers, vec![4, 5]);
        assert!(!tests[0].ignore);
        assert_eq!(tests[1].fence_line, 8);
        assert!(tests[1].ignore);
    }

    #[test]
    fn extracts_taro_doc_comment_fences_with_original_lines() {
        let src = "/// Example:\n/// ```taro\n/// value := 2 + 2\n/// assert(value == 4)\n/// ```\nfunc demo() {}\n\n/// Ignored:\n/// ```taro,ignore\n/// broken(\n/// ```\nfunc other() {}\n";
        let tests = extract_taro_doc_comment_tests(Path::new("demo.tr"), src);
        assert_eq!(tests.len(), 2);
        assert_eq!(tests[0].fence_line, 2);
        assert_eq!(tests[0].line_numbers, vec![3, 4]);
        assert!(!tests[0].ignore);
        assert_eq!(tests[1].fence_line, 9);
        assert_eq!(tests[1].line_numbers, vec![10]);
        assert!(tests[1].ignore);
    }

    #[test]
    fn remaps_wrapped_line_numbers_to_original_source() {
        let test = DocTest {
            source_path: PathBuf::from("docs/example.md"),
            fence_line: 10,
            line_numbers: vec![11, 12],
            lines: vec!["x := 1".into(), "assert(x == 2)".into()],
            ignore: false,
            no_run: false,
        };
        let wrapped = wrap_doctest_source(&test);
        // Line 1 is `func main() {`, line 2 is `x := 1` (orig 11), line 3 is `assert(x == 2)` (orig 12).
        let remapped = remap_locations(
            " -> /tmp/doctest_0.tr:3:5\npanic at /tmp/doctest_0.tr:3:5",
            Path::new("/tmp/doctest_0.tr"),
            &test.source_path,
            &wrapped.line_map,
        );
        assert_eq!(
            remapped,
            " -> docs/example.md:12:5\npanic at docs/example.md:12:5"
        );
    }
}
