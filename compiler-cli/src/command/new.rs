use std::{
    fs::{self, File},
    io::Write,
    path::{Path, PathBuf},
};

use compiler::error::{CompileResult, ReportedError};
use compiler::package::utils::{get_package_name, normalize_module_path};

use crate::{NewArgs, NewProjectKind};

pub fn run(arguments: NewArgs) -> CompileResult<()> {
    let package_name = normalize_package_name(&arguments.package).map_err(|message| {
        eprintln!("{message}");
        ReportedError
    })?;
    let project_path = create_project(&package_name, arguments.kind)?;

    println!(
        "Created new project '{}' in '{}'",
        package_name,
        project_path.display()
    );

    Ok(())
}

fn normalize_package_name(input: &str) -> Result<String, String> {
    normalize_module_path(input).map_err(|e| invalid_package_name_message(&e))
}

fn invalid_package_name_message(error: &str) -> String {
    format!(
        "error: invalid package name: {error}\nnote: package name must be in the format 'host/owner/repo'"
    )
}

fn create_project(package_name: &str, kind: NewProjectKind) -> CompileResult<PathBuf> {
    let dir_name = get_package_name(package_name).map_err(|_| {
        eprintln!("error: could not derive directory name from package name");
        ReportedError
    })?;
    let project_path = PathBuf::from(dir_name.as_str());

    if project_path.exists() {
        eprintln!(
            "error: destination '{}' already exists",
            project_path.display()
        );
        return Err(ReportedError);
    }

    fs::create_dir_all(&project_path).map_err(|e| {
        eprintln!(
            "error: failed to create directory '{}': {}",
            project_path.display(),
            e
        );
        ReportedError
    })?;

    let src_path = project_path.join("src");
    fs::create_dir_all(&src_path).map_err(|e| {
        eprintln!(
            "error: failed to create directory '{}': {}",
            src_path.display(),
            e
        );
        ReportedError
    })?;

    write_manifest(&project_path.join("package.toml"), package_name, kind)?;
    write_source_template(&src_path, kind)?;

    Ok(project_path)
}

fn write_manifest(path: &Path, package_name: &str, kind: NewProjectKind) -> CompileResult<()> {
    let mut package_toml = File::create(path).map_err(|e| {
        eprintln!("error: failed to create file '{}': {}", path.display(), e);
        ReportedError
    })?;

    writeln!(
        package_toml,
        r#"[package]
name = "{}"
version = "0.1.0"
kind = "{}"
"#,
        package_name,
        kind.manifest_kind()
    )
    .map_err(|e| {
        eprintln!("error: failed to write to '{}': {}", path.display(), e);
        ReportedError
    })
}

fn write_source_template(src_path: &Path, kind: NewProjectKind) -> CompileResult<()> {
    let source_path = src_path.join(kind.source_file_name());
    let mut source_file = File::create(&source_path).map_err(|e| {
        eprintln!(
            "error: failed to create file '{}': {}",
            source_path.display(),
            e
        );
        ReportedError
    })?;

    writeln!(source_file, "{}", kind.source_template()).map_err(|e| {
        eprintln!(
            "error: failed to write to '{}': {}",
            source_path.display(),
            e
        );
        ReportedError
    })
}

impl NewProjectKind {
    fn manifest_kind(self) -> &'static str {
        match self {
            NewProjectKind::Executable => "executable",
            NewProjectKind::Library => "library",
        }
    }

    fn source_file_name(self) -> &'static str {
        match self {
            NewProjectKind::Executable => "main.tr",
            NewProjectKind::Library => "lib.tr",
        }
    }

    fn source_template(self) -> &'static str {
        match self {
            NewProjectKind::Executable => "func main() {\n    print(\"Hello, World!\\n\")\n}",
            NewProjectKind::Library => "public func hello() {\n    print(\"Hello, World!\\n\")\n}",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{create_project, invalid_package_name_message, normalize_package_name};
    use crate::NewProjectKind;
    use std::{
        fs::{self, create_dir_all, read_to_string, write},
        path::PathBuf,
        sync::{Mutex, OnceLock},
    };

    #[test]
    fn executable_scaffold_writes_manifest_and_main() {
        with_test_cwd("new-executable", |root| {
            let project_path =
                match create_project("github.com/acme/app", NewProjectKind::Executable) {
                    Ok(path) => path,
                    Err(_) => panic!("expected executable scaffold to succeed"),
                };

            assert_eq!(project_path, PathBuf::from("app"));
            assert_eq!(
                read_to_string(root.join(&project_path).join("package.toml")).expect("manifest"),
                "[package]\nname = \"github.com/acme/app\"\nversion = \"0.1.0\"\nkind = \"executable\"\n\n"
            );
            assert_eq!(
                read_to_string(root.join(&project_path).join("src/main.tr")).expect("main"),
                "func main() {\n    print(\"Hello, World!\\n\")\n}\n"
            );
        });
    }

    #[test]
    fn library_scaffold_writes_manifest_and_lib() {
        with_test_cwd("new-library", |root| {
            let project_path = match create_project("github.com/acme/lib", NewProjectKind::Library)
            {
                Ok(path) => path,
                Err(_) => panic!("expected library scaffold to succeed"),
            };

            assert_eq!(project_path, PathBuf::from("lib"));
            assert_eq!(
                read_to_string(root.join(&project_path).join("package.toml")).expect("manifest"),
                "[package]\nname = \"github.com/acme/lib\"\nversion = \"0.1.0\"\nkind = \"library\"\n\n"
            );
            assert_eq!(
                read_to_string(root.join(&project_path).join("src/lib.tr")).expect("lib"),
                "public func hello() {\n    print(\"Hello, World!\\n\")\n}\n"
            );
        });
    }

    #[test]
    fn invalid_package_name_message_includes_guidance() {
        let error = normalize_package_name("not-a-package").expect_err("expected invalid package");

        assert_eq!(
            error,
            invalid_package_name_message("module path must be host/owner/repo")
        );
        assert!(error.contains("host/owner/repo"));
    }

    #[test]
    fn existing_destination_fails_without_overwriting() {
        with_test_cwd("new-existing-destination", |root| {
            let destination = root.join("app");
            create_dir_all(destination.join("src")).expect("src");
            write(destination.join("sentinel.txt"), "keep me").expect("sentinel");

            let result = create_project("github.com/acme/app", NewProjectKind::Executable);
            assert!(result.is_err());
            assert_eq!(
                read_to_string(destination.join("sentinel.txt")).expect("sentinel"),
                "keep me"
            );
            assert!(!destination.join("src/main.tr").exists());
        });
    }

    fn with_test_cwd(name: &str, f: impl FnOnce(PathBuf)) {
        let _guard = cwd_lock()
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        let root = temp_dir(name);
        let _cwd = TestCwdGuard::enter(root.clone());

        f(root.clone());
    }

    fn cwd_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "taro-new-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        create_dir_all(&path).expect("temp dir");
        path
    }

    struct TestCwdGuard {
        original: PathBuf,
        root: PathBuf,
    }

    impl TestCwdGuard {
        fn enter(root: PathBuf) -> Self {
            let original = std::env::current_dir().expect("current dir");
            std::env::set_current_dir(&root).expect("set current dir");
            Self { original, root }
        }
    }

    impl Drop for TestCwdGuard {
        fn drop(&mut self) {
            std::env::set_current_dir(&self.original).expect("restore current dir");
            fs::remove_dir_all(&self.root).expect("cleanup temp dir");
        }
    }
}
