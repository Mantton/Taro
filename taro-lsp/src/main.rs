mod protocol;
mod server;
mod supervisor;
mod worker;

use std::{env, error::Error, ffi::OsString, fs, path::PathBuf};

use compiler::compile::target_facts::TargetFacts;

fn main() -> Result<(), Box<dyn Error + Send + Sync>> {
    let mut arguments = env::args_os().skip(1);
    let mut child = false;
    let mut target = None;
    while let Some(argument) = arguments.next() {
        if argument == "--worker" {
            child = true;
        } else if argument == "--target-facts" {
            target = arguments.next().map(PathBuf::from);
        } else if argument == "--help" {
            println!("Usage: taro-lsp --target-facts <target-facts.toml>");
            return Ok(());
        } else {
            return Err(format!("unknown argument {:?}", argument).into());
        }
    }
    let target = target.ok_or("pass --target-facts with a matching Taro descriptor")?;
    let target = fs::canonicalize(target)?;
    if child {
        let descriptor: TargetFacts = toml::from_str(&fs::read_to_string(target)?)?;
        worker::run(descriptor)?;
    } else {
        let launch = supervisor::Launch {
            program: env::current_exe()?,
            arguments: vec![
                OsString::from("--worker"),
                OsString::from("--target-facts"),
                target.into_os_string(),
            ],
        };
        server::run(launch)?;
    }
    Ok(())
}
