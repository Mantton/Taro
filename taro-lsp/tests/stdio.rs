use std::{
    fs,
    io::{self, BufReader, Read, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, Stdio},
    sync::{
        atomic::{AtomicU64, Ordering},
        mpsc::{self, Receiver},
    },
    thread,
    time::Duration,
};

use lsp_server::{Message, Notification, Request};
use serde_json::{Value, json};

struct Fixture {
    root: PathBuf,
    facts: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(1);
        let id = NEXT.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!("taro-lsp-test-{}-{id}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let facts = root.join("target-facts.toml");
        fs::write(
            &facts,
            "triple = 'x86_64-unknown-linux-gnu'\npointer_bits = 64\n",
        )
        .unwrap();
        Self { root, facts }
    }

    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_taro-lsp"));
        command.arg("--target-facts").arg(&self.facts);
        command
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

struct Session<Message> {
    child: Child,
    input: ChildStdin,
    replies: Receiver<Message>,
}

impl<T: Send + 'static> Session<T> {
    fn spawn(
        command: &mut Command,
        read: impl Fn(&mut BufReader<std::process::ChildStdout>) -> io::Result<Option<T>>
        + Send
        + 'static,
    ) -> Self {
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let mut stdout = BufReader::new(child.stdout.take().unwrap());
        let (messages, replies) = mpsc::channel();
        thread::spawn(move || {
            while let Some(value) = read(&mut stdout).unwrap() {
                if messages.send(value).is_err() {
                    break;
                }
            }
        });
        Self {
            child,
            input,
            replies,
        }
    }

    #[track_caller]
    fn next(&self) -> T {
        self.replies
            .recv_timeout(Duration::from_secs(40))
            .expect("response from language server")
    }
}

impl<T> Drop for Session<T> {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn read_worker(input: &mut impl Read) -> io::Result<Option<Value>> {
    let mut length = [0u8; 4];
    if input.read(&mut length[..1])? == 0 {
        return Ok(None);
    }
    input.read_exact(&mut length[1..])?;
    let mut payload = vec![0u8; u32::from_be_bytes(length) as usize];
    input.read_exact(&mut payload)?;
    Ok(Some(
        serde_json::from_slice::<Value>(&payload)?["data"].clone(),
    ))
}

fn send_worker(input: &mut impl Write, data: Value) {
    let frame = serde_json::to_vec(&json!({"schema": 1, "data": data})).unwrap();
    input
        .write_all(&(frame.len() as u32).to_be_bytes())
        .unwrap();
    input.write_all(&frame).unwrap();
    input.flush().unwrap();
}

fn as_uri(path: &Path) -> url::Url {
    url::Url::from_file_path(path).unwrap()
}

fn copy_fixture_tree(from: &Path, to: &Path) {
    fs::create_dir(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let destination = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_fixture_tree(&entry.path(), &destination);
        } else {
            fs::copy(entry.path(), destination).unwrap();
        }
    }
}

#[test]
fn worker_checks_unsaved_siblings_then_updates_only_one_buffer() {
    let fixture = Fixture::new();
    let mut command = fixture.command();
    let mut worker = Session::spawn(command.arg("--worker"), read_worker);
    let first = fixture.root.join("src/first.tr");
    let second = fixture.root.join("src/second.tr");
    send_worker(
        &mut worker.input,
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": 1},
                "inputs": { "Reset": {
                    "root": fixture.root,
                    "documents": {
                        first.to_str().unwrap(): "func call() { _ = selected() }",
                        second.to_str().unwrap(): "func selected() -> int32 { 15 }",
                    },
                }},
            }
        }),
    );
    let first_reply = worker.next();
    let product = &first_reply["Finished"]["result"]["Ok"];
    assert_eq!(product["complete"], true, "{first_reply}");
    assert_eq!(product["revision"], 1);
    assert!(
        product["occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .any(|occurrence| { occurrence["declaration"]["name"] == "selected" })
    );

    send_worker(
        &mut worker.input,
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": 2},
                "inputs": { "Delta": {
                    second.to_str().unwrap(): "func selected() -> bool { true }",
                }},
            }
        }),
    );
    let second_reply = worker.next();
    let product = &second_reply["Finished"]["result"]["Ok"];
    assert_eq!(product["complete"], true, "{second_reply}");
    assert_eq!(product["revision"], 2);
    assert_eq!(product["bodies"].as_array().unwrap().len(), 2);
    assert!(
        product["occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .any(|entry| entry["ty"] == "Bool")
    );
}

#[test]
fn stdio_reserves_stdout_for_lsp_messages_and_exits_on_shutdown() {
    let fixture = Fixture::new();
    let mut server = Session::spawn(&mut fixture.command(), Message::read);
    Message::Request(Request::new(
        1.into(),
        "initialize".into(),
        json!({
            "capabilities": {},
            "workspaceFolders": [{"name": "test", "uri": as_uri(&fixture.root).as_str()}],
        }),
    ))
    .write(&mut server.input)
    .unwrap();
    let Message::Response(initialized) = server.next() else {
        panic!("initialize response")
    };
    let capabilities = initialized.response_result.unwrap();
    assert_eq!(
        capabilities["capabilities"]["textDocumentSync"]["openClose"],
        true
    );
    Message::Notification(Notification::new("initialized".into(), json!({})))
        .write(&mut server.input)
        .unwrap();
    Message::Request(Request::new(2.into(), "shutdown".into(), Value::Null))
        .write(&mut server.input)
        .unwrap();
    loop {
        if let Message::Response(response) = server.next() {
            assert_eq!(response.id, 2.into());
            assert!(response.response_result.is_ok(), "{response:?}");
            break;
        }
    }
    Message::Notification(Notification::new("exit".into(), Value::Null))
        .write(&mut server.input)
        .unwrap();
    let deadline = std::time::Instant::now() + Duration::from_secs(4);
    while std::time::Instant::now() < deadline {
        if let Some(status) = server.child.try_wait().unwrap() {
            assert!(status.success());
            return;
        }
        thread::sleep(Duration::from_millis(5));
    }
    panic!("server did not exit after shutdown");
}

#[test]
fn installed_bundle_resolves_std_sources_and_rebuilds_for_target_changes() {
    let fixture = Fixture::new();
    let std = fixture.root.join("std-dev");
    fs::create_dir(&std).unwrap();
    let repository_std = Path::new(env!("CARGO_MANIFEST_DIR")).join("../std");
    fs::copy(
        repository_std.join("package.toml"),
        std.join("package.toml"),
    )
    .unwrap();
    copy_fixture_tree(&repository_std.join("src"), &std.join("src"));
    let std_text = concat!(
        "@cfg(arch(\"x86_64\"))\npublic func selected() -> int32 { 15 }\n",
        "@cfg(arch(\"aarch64\"))\npublic func selected() -> bool { true }\n",
    );
    fs::write(std.join("src/lsp_bundle_fixture.tr"), std_text).unwrap();
    let arm = fixture.root.join("aarch64.toml");
    fs::write(
        &arm,
        "triple = 'aarch64-unknown-linux-gnu'\npointer_bits = 64\n",
    )
    .unwrap();
    let bundle = fixture.root.join("bundle");
    assert!(
        Command::new(env!("CARGO_BIN_EXE_taro-lsp"))
            .arg("--prepare-bundle")
            .arg(&bundle)
            .arg(&std)
            .arg(&fixture.facts)
            .arg(&arm)
            .status()
            .unwrap()
            .success()
    );

    let project = fixture.root.join("project");
    fs::create_dir_all(project.join("src")).unwrap();
    let manifest = project.join("package.toml");
    let package =
        "[package]\nname = 'github.com/test/project'\nkind = 'library'\nno_std_prelude = true\n";
    fs::write(&manifest, package).unwrap();
    let open_path = project.join("src/use.tr");
    let text = "func check() { _ = std::selected() }";
    let reset = |revision| {
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": revision},
                "inputs": {"Reset": {
                    "root": project,
                    "documents": {open_path.to_str().unwrap(): text},
                }},
            },
        })
    };
    let delta = |revision, text: Option<&str>| {
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": revision},
                "inputs": {"Delta": {open_path.to_str().unwrap(): text}},
            },
        })
    };
    let mut command = Command::new(env!("CARGO_BIN_EXE_taro-lsp"));
    let mut worker = Session::spawn(
        command.arg("--worker").arg("--bundle").arg(&bundle),
        read_worker,
    );
    send_worker(&mut worker.input, reset(1));
    let reply = worker.next();
    let first = &reply["Finished"]["result"]["Ok"];
    assert_eq!(first["complete"], true, "{reply}");
    let installed = bundle
        .canonicalize()
        .unwrap()
        .join("std/src/lsp_bundle_fixture.tr");
    let same_signature = |product: &Value, line: u64| {
        product["occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .find(|fact| {
                fact["declaration"]["name"] == "selected" && fact["declaration"]["package"] == "std"
            })
            .is_some_and(|fact| {
                fact["declaration"]["source"]["path"] == installed.to_str().unwrap()
                    && fact["declaration"]["source"]["start"]["line"] == line
            })
    };
    assert!(same_signature(first, 1), "{first}");

    send_worker(&mut worker.input, delta(2, None));
    assert_eq!(worker.next()["Finished"]["result"]["Ok"]["complete"], true);
    send_worker(&mut worker.input, delta(3, Some(text)));
    let warm = worker.next();
    assert!(
        same_signature(&warm["Finished"]["result"]["Ok"], 1),
        "{warm}"
    );

    fs::write(
        &manifest,
        format!("{package}\n[language_server]\ntarget = 'aarch64-unknown-linux-gnu'\n"),
    )
    .unwrap();
    send_worker(&mut worker.input, reset(4));
    let switched = worker.next();
    let second = &switched["Finished"]["result"]["Ok"];
    assert_eq!(second["complete"], true, "{switched}");
    assert!(same_signature(second, 3), "{second}");
    assert!(
        second["occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .any(|fact| fact["ty"] == "Bool")
    );

    fs::write(
        &manifest,
        format!("{package}\n[language_server]\nstd_digest = 'different'\n"),
    )
    .unwrap();
    send_worker(&mut worker.input, reset(5));
    let mismatch = worker.next();
    assert!(
        mismatch["Finished"]["result"]["Err"]
            .as_str()
            .is_some_and(|message| message.contains("different standard-library source identity")),
        "{mismatch}"
    );

    fs::write(&manifest, package).unwrap();
    fs::write(installed, format!("{std_text}\n// Different source.")).unwrap();
    send_worker(&mut worker.input, reset(6));
    let stale = worker.next();
    assert!(
        stale["Finished"]["result"]["Err"]
            .as_str()
            .is_some_and(|message| message.contains("sources do not match")),
        "{stale}"
    );
}
