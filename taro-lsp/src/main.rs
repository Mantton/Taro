mod bundle;
mod features;
mod project;
mod protocol;
mod server;
mod standard_library;
mod supervisor;
mod worker;

use std::{env, error::Error, ffi::OsString, fs, path::PathBuf};

use compiler::compile::target_facts::TargetFacts;

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    let mut arguments = env::args_os().skip(1).peekable();
    if arguments
        .peek()
        .is_some_and(|argument| argument == "--prepare-bundle")
    {
        arguments.next();
        let output = path_argument(arguments.next(), "--prepare-bundle")?;
        let std_source = path_argument(arguments.next(), "standard-library checkout")?;
        bundle::create(
            &output,
            &std_source,
            &arguments.map(PathBuf::from).collect::<Vec<_>>(),
        )?;
        return Ok(());
    }
    let mut child = false;
    let mut target = None;
    let mut installed = None;
    while let Some(argument) = arguments.next() {
        if argument == "--worker" {
            child = true;
        } else if argument == "--stdio" {
            // Editor clients can select the default transport explicitly.
        } else if argument == "--target-facts" {
            target = Some(path_argument(arguments.next(), "--target-facts")?);
        } else if argument == "--bundle" {
            installed = Some(path_argument(arguments.next(), "--bundle")?);
        } else if argument == "--help" {
            println!(
                "Usage: taro-lsp [--stdio] [--bundle <directory>]\n       taro-lsp --prepare-bundle <new-directory> <std-source> <target-facts.toml>..."
            );
            return Ok(());
        } else {
            return Err(format!("unknown argument {:?}", argument).into());
        }
    }
    if target.is_some() && installed.is_some() {
        return Err("--target-facts and --bundle are mutually exclusive".into());
    }
    let executable = env::current_exe()?;
    let (flag, source) = if let Some(target) = target {
        ("--target-facts", fs::canonicalize(target)?)
    } else {
        let path = installed.unwrap_or_else(|| {
            executable
                .parent()
                .expect("executable directory")
                .join("../share/taro-lsp")
        });
        ("--bundle", fs::canonicalize(path)?)
    };
    if child {
        let environment = if flag == "--bundle" {
            worker::Environment::Installed(bundle::Bundle::load(&source)?)
        } else {
            let descriptor: TargetFacts = toml::from_str(&fs::read_to_string(source)?)?;
            worker::Environment::Bootstrap(descriptor)
        };
        worker::run(environment)?;
    } else {
        let installed_std = (flag == "--bundle").then(|| bundle::std_path(&source));
        let launch = supervisor::Launch {
            program: executable,
            arguments: vec![
                OsString::from("--worker"),
                OsString::from(flag),
                source.into_os_string(),
            ],
        };
        server::run(launch, installed_std)?;
    }
    Ok(())
}

fn path_argument(
    argument: Option<OsString>,
    option: &str,
) -> Result<PathBuf, Box<dyn Error + Send + Sync>> {
    argument
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing path for {option}").into())
}
