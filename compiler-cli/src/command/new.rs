use std::{
    fs::{self, File},
    io::Write,
    path::PathBuf,
};

use compiler::error::{CompileResult, ReportedError};

use crate::{
    CommandLineArguments,
    package::utils::{get_package_name, normalize_module_path},
};

pub fn run(arguments: CommandLineArguments) -> CompileResult<()> {
    // 1. Validate and normalize the input name which functions as the package name
    let input_name = arguments.path.to_string_lossy();
    let package_name = normalize_module_path(&input_name).map_err(|e| {
        eprintln!("error: invalid package name: {}", e);
        eprintln!("note: package name must be in the format 'host/owner/repo'");
        ReportedError
    })?;

    // 2. Derive the directory name from the package name (the repo part)
    let dir_name = get_package_name(&package_name).map_err(|_| {
        // Should logically not happen if normalize passed, but safe guard
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

    // Create root directory
    fs::create_dir_all(&project_path).map_err(|e| {
        eprintln!(
            "error: failed to create directory '{}': {}",
            project_path.display(),
            e
        );
        ReportedError
    })?;

    // Create src directory
    let src_path = project_path.join("src");
    fs::create_dir_all(&src_path).map_err(|e| {
        eprintln!(
            "error: failed to create directory '{}': {}",
            src_path.display(),
            e
        );
        ReportedError
    })?;

    // Create package.toml
    let package_toml_path = project_path.join("package.toml");
    let mut package_toml = File::create(&package_toml_path).map_err(|e| {
        eprintln!(
            "error: failed to create file '{}': {}",
            package_toml_path.display(),
            e
        );
        ReportedError
    })?;

    writeln!(
        package_toml,
        r#"[package]
name = "{}"
version = "0.1.0"
"#,
        package_name
    )
    .map_err(|e| {
        eprintln!(
            "error: failed to write to '{}': {}",
            package_toml_path.display(),
            e
        );
        ReportedError
    })?;

    // Create src/main.tr
    let main_tr_path = src_path.join("main.tr");
    let mut main_tr = File::create(&main_tr_path).map_err(|e| {
        eprintln!(
            "error: failed to create file '{}': {}",
            main_tr_path.display(),
            e
        );
        ReportedError
    })?;

    writeln!(
        main_tr,
        r#"func main() {{
    print("Hello, World!\n")
}}"#
    )
    .map_err(|e| {
        eprintln!(
            "error: failed to write to '{}': {}",
            main_tr_path.display(),
            e
        );
        ReportedError
    })?;

    println!(
        "Created new project '{}' in '{}'",
        package_name,
        project_path.display()
    );

    Ok(())
}
