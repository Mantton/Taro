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

    fn next(&self) -> T {
        self.replies
            .recv_timeout(Duration::from_secs(10))
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
