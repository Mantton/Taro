mod bundle;
mod features;
mod project;
mod protocol;
mod sdk;
mod server;
mod standard_library;
mod supervisor;
mod worker;

use std::{env, error::Error, ffi::OsString, fs, path::PathBuf};

use compiler::compile::target_facts::TargetFacts;
use standard_library::Installation;

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
    let mut portable = None;
    let mut sdk_home = None;
    while let Some(argument) = arguments.next() {
        if argument == "--worker" {
            child = true;
        } else if argument == "--stdio" {
            // Editor clients can select the default transport explicitly.
        } else if argument == "--target-facts" {
            target = Some(path_argument(arguments.next(), "--target-facts")?);
        } else if argument == "--bundle" {
            portable = Some(path_argument(arguments.next(), "--bundle")?);
        } else if argument == "--sdk" {
            sdk_home = Some(path_argument(arguments.next(), "--sdk")?);
        } else if argument == "--help" {
            println!(
                "Usage: taro-lsp [--stdio] [--sdk <directory> | --bundle <directory>]\n       taro-lsp --prepare-bundle <new-directory> <std-source> <target-facts.toml>..."
            );
            return Ok(());
        } else {
            return Err(format!("unknown argument {:?}", argument).into());
        }
    }
    if [&target, &portable, &sdk_home]
        .into_iter()
        .filter(|path| path.is_some())
        .count()
        > 1
    {
        return Err("--target-facts, --bundle, and --sdk are mutually exclusive".into());
    }
    let executable = env::current_exe()?;
    let (flag, source) = if let Some(target) = target {
        ("--target-facts", fs::canonicalize(target)?)
    } else if let Some(path) = portable {
        ("--bundle", fs::canonicalize(path)?)
    } else {
        (
            "--sdk",
            sdk_home.map_or_else(sdk::discover, fs::canonicalize)?,
        )
    };
    if child {
        let environment = match flag {
            "--bundle" => worker::Environment::Installed(Installation::Portable(
                bundle::Bundle::load(&source)?,
            )),
            "--sdk" => worker::Environment::Installed(Installation::Sdk(sdk::Sdk::load(&source)?)),
            _ => {
                let descriptor: TargetFacts = toml::from_str(&fs::read_to_string(source)?)?;
                worker::Environment::Bootstrap(descriptor)
            }
        };
        worker::run(environment)?;
    } else {
        let installed_std = match flag {
            "--sdk" => Some(sdk::std_root(&source)?),
            "--bundle" => Some(bundle::std_path(&source)),
            _ => None,
        };
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
