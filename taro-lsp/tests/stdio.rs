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

use lsp_server::{Message, Notification, Request, Response};
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
    let frame = serde_json::to_vec(&json!({"schema": 2, "data": data})).unwrap();
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

fn copy_std(to: &Path) {
    fs::create_dir(to).unwrap();
    let repository = Path::new(env!("CARGO_MANIFEST_DIR")).join("../std");
    fs::copy(repository.join("package.toml"), to.join("package.toml")).unwrap();
    copy_fixture_tree(&repository.join("src"), &to.join("src"));
}

impl Session<Message> {
    fn notify(&mut self, method: &str, params: Value) {
        Message::Notification(Notification::new(method.into(), params))
            .write(&mut self.input)
            .unwrap();
    }

    fn request(&mut self, id: i32, method: &str, params: Value) {
        Message::Request(Request::new(id.into(), method.into(), params))
            .write(&mut self.input)
            .unwrap();
    }

    fn response(&self, id: i32) -> Value {
        loop {
            if let Message::Response(response) = self.next() {
                assert_eq!(response.id, id.into());
                return response.response_result.unwrap();
            }
        }
    }

    fn open(&mut self, uri: &str, text: &str) {
        self.notify(
            "textDocument/didOpen",
            json!({
                "textDocument": { "uri": uri, "version": 1, "languageId": "taro", "text": text },
            }),
        );
    }

    fn change(&mut self, uri: &str, version: i32, text: &str) {
        self.notify(
            "textDocument/didChange",
            json!({
                "textDocument": { "uri": uri, "version": version },
                "contentChanges": [{ "text": text }],
            }),
        );
    }
}

fn at(uri: &str, text: &str, needle: &str) -> Value {
    let (line, before) = text
        .lines()
        .enumerate()
        .find_map(|(line, text)| Some((line, &text[..text.find(needle)?])))
        .unwrap();
    json!({
        "textDocument": { "uri": uri },
        "position": { "line": line, "character": before.encode_utf16().count() },
    })
}

#[test]
fn definitions_follow_qualified_paths_and_resolved_fields() {
    let fixture = Fixture::new();
    let mut server = Session::spawn(&mut fixture.command(), Message::read);
    server.request(
        1,
        "initialize",
        json!({"capabilities": {}, "rootUri": as_uri(&fixture.root).as_str()}),
    );
    server.response(1);
    server.notify("initialized", json!({}));

    let declarations = as_uri(&fixture.root.join("src/definitions.tr"));
    let active = as_uri(&fixture.root.join("src/active.tr"));
    let module = as_uri(&fixture.root.join("src/utilities/helpers.tr"));
    let declared_module = as_uri(&fixture.root.join("src/declared/helpers.tr"));
    let definitions = "namespace Outer {\n\
        public namespace Inner {\n\
        public struct Packet { count: int32 }\n\
        public func select(_ v: int32) -> int32 { v }\n\
        public func select(_ v: bool) -> bool { v }\n\
        }\n\
        }\n\
        struct Other { count: bool }\n\
        class Base[T] { stored: T }\n\
        class Child: Base[int32] {}\n\
        struct Callback { invoke: (int32) -> int32 }\n";
    let uses = "func inspect(child: Child, callback: Callback) {\n\
        first := Outer::Inner::Packet { count: 1 }\n\
        second := Other { count: true }\n\
        _ = \"🌱\"; _ = first.count\n\
        _ = second.count\n\
        _ = child.stored\n\
        _ = Outer::Inner::select(true)\n\
        _ = utilities::produce()\n\
        _ = declared::answer()\n\
        _ = callback.invoke(3)\n\
        }\n";
    let helpers = "public func produce() -> int32 { 1 }";
    let declared_helpers = "public mod declared;\npublic func answer() -> int32 { 2 }";
    server.open(declarations.as_str(), definitions);
    server.open(module.as_str(), helpers);
    server.open(declared_module.as_str(), declared_helpers);
    server.open(active.as_str(), uses);

    loop {
        if let Message::Notification(note) = server.next()
            && note.method == "textDocument/publishDiagnostics"
            && note.params["uri"] == active.as_str()
        {
            assert_eq!(note.params["diagnostics"], json!([]));
            break;
        }
    }

    for (index, (use_prefix, token, declaration_prefix, declaration_text, uri)) in [
        (
            "first := ",
            "Outer",
            "namespace ",
            definitions,
            &declarations,
        ),
        (
            "Outer::",
            "Inner",
            "public namespace ",
            definitions,
            &declarations,
        ),
        (
            "Inner::",
            "Packet",
            "public struct ",
            definitions,
            &declarations,
        ),
        (
            "Packet { ",
            "count",
            "Packet { ",
            definitions,
            &declarations,
        ),
        ("Other { ", "count", "Other { ", definitions, &declarations),
        ("first.", "count", "Packet { ", definitions, &declarations),
        ("second.", "count", "Other { ", definitions, &declarations),
        ("child.", "stored", "Base[T] { ", definitions, &declarations),
        (
            "Inner::",
            "select",
            "public func ",
            definitions,
            &declarations,
        ),
        ("utilities::", "produce", "public func ", helpers, &module),
        (
            "_ = ",
            "declared",
            "public mod ",
            declared_helpers,
            &declared_module,
        ),
        (
            "callback.",
            "invoke",
            "Callback { ",
            definitions,
            &declarations,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let id = 2 + index as i32;
        let start = |uri: &url::Url, text: &str, prefix: &str, suffix: &str| {
            let mut params = at(uri.as_str(), text, &format!("{prefix}{token}{suffix}"));
            let column = params["position"]["character"].as_u64().unwrap();
            params["position"]["character"] = (column + prefix.len() as u64).into();
            params
        };
        server.request(
            id,
            "textDocument/definition",
            start(&active, uses, use_prefix, ""),
        );
        let mut expected = start(
            uri,
            declaration_text,
            declaration_prefix,
            if token == "select" { "(_ v: bool" } else { "" },
        )["position"]
            .clone();
        let begin = expected.clone();
        expected["character"] = (begin["character"].as_u64().unwrap() + token.len() as u64).into();
        assert_eq!(
            server.response(id),
            json!({"uri": uri.as_str(), "range": {"start": begin, "end": expected}}),
            "definition of {use_prefix}{token}"
        );
    }

    server.request(
        20,
        "textDocument/definition",
        at(active.as_str(), uses, "utilities::"),
    );
    assert_eq!(server.response(20), Value::Null);

    server.request(
        21,
        "textDocument/hover",
        at(declarations.as_str(), definitions, "Packet {"),
    );
    assert!(
        server.response(21)["contents"]["value"]
            .as_str()
            .unwrap()
            .ends_with("Packet")
    );
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
    assert_eq!(second_reply["Finished"]["mode"], "Package");
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
fn worker_merges_clean_body_edits_and_falls_back_for_import_warnings_or_moved_ranges() {
    let fixture = Fixture::new();
    let root = fixture.root.canonicalize().unwrap();
    let path = root.join("src/main.tr");
    fs::write(
        root.join("package.toml"),
        "[package]\nname = 'github.com/test/project'\nkind = 'library'\n",
    )
    .unwrap();
    fs::create_dir_all(root.join("src/helpers")).unwrap();
    fs::write(
        root.join("src/helpers/count.tr"),
        "public func count() -> int32 { 12 }",
    )
    .unwrap();
    let mut worker = Session::spawn(fixture.command().arg("--worker"), read_worker);
    let mut oracle = Session::spawn(fixture.command().arg("--worker"), read_worker);
    let request = |revision, inputs| json!({"Analyze": {"stamp": {"generation": 1, "revision": revision}, "inputs": inputs}});
    let reset = |revision, text| {
        request(
            revision,
            json!({"Reset": {"root": root, "documents": {path.to_str().unwrap(): text}}}),
        )
    };
    let original = r#"import project::helpers::count
func changed() -> int32 {
    // Leave room for a nested declaration without shifting later ranges.
    value := count()
    value
}
func later() -> int32 { 42 }
func caller() -> int32 { changed() + later() }
"#;
    let rename = original.replace("value", "renamedLocal");
    let warning = rename.replace("count()", "13");
    let shifted = rename.replace("    renamedLocal\n", "\n    renamedLocal\n");
    let two_bodies = rename.replace("42", "43");
    let nested = rename
        .replace(
            "// Leave room for a nested declaration without shifting later ranges.",
            "func localCount() -> int32 { count() }",
        )
        .replace("renamedLocal := count()", "renamedLocal := localCount()");
    let local_const = rename
        .replace(
            "// Leave room for a nested declaration without shifting later ranges.",
            "const LOCAL: int32 = 9",
        )
        .replace("renamedLocal := count()", "renamedLocal := count() + LOCAL");
    send_worker(&mut worker.input, reset(1, original));
    let initial = worker.next();
    assert_eq!(
        initial["Finished"]["result"]["Ok"]["complete"], true,
        "{initial}"
    );
    assert_eq!(
        initial["Finished"]["result"]["Ok"]["diagnostics"],
        json!([])
    );

    let compare = |reply: &Value, expected: &Value| {
        let normalized = |reply: &Value| {
            let mut product = reply["Finished"]["result"]["Ok"].clone();
            assert_eq!(product["complete"], true, "{reply}");
            product["declarations"]
                .as_array_mut()
                .unwrap()
                .sort_by_key(Value::to_string);
            product
        };
        assert_eq!(normalized(reply), normalized(expected));
    };
    for (revision, text, mode) in [
        (2, rename.as_str(), "Body"),
        (3, warning.as_str(), "Package"),
        (4, rename.as_str(), "Package"),
        (5, shifted.as_str(), "Package"),
        (6, rename.as_str(), "Package"),
        (7, original, "Body"),
        (8, two_bodies.as_str(), "Package"),
        (9, nested.as_str(), "Package"),
        (10, rename.as_str(), "Package"),
        (11, local_const.as_str(), "Package"),
        (12, rename.as_str(), "Package"),
    ] {
        send_worker(
            &mut worker.input,
            request(revision, json!({"Delta": {path.to_str().unwrap(): text}})),
        );
        let reply = worker.next();
        assert_eq!(reply["Finished"]["mode"], mode, "revision {revision}");
        send_worker(&mut oracle.input, reset(revision, text));
        compare(&reply, &oracle.next());
        if revision == 3 {
            let warning = &reply["Finished"]["result"]["Ok"]["diagnostics"][0];
            assert_eq!(warning["message"], "unused import 'count'");
            assert_eq!(warning["source"]["start"]["line"], 0);
        }
    }
}

#[test]
fn worker_observes_asset_changes_on_the_next_edit_without_a_file_event() {
    let fixture = Fixture::new();
    let root = fixture.root.canonicalize().unwrap();
    let path = root.join("src/main.tr");
    let asset = root.join("src/note.txt");
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(
        root.join("src/asset.tr"),
        "func note() -> string { #embed(\"note.txt\") }",
    )
    .unwrap();
    fs::write(&asset, "initial").unwrap();
    let source = "func inspect() {\n    _ = note()\n}";
    let mut worker = Session::spawn(fixture.command().arg("--worker"), read_worker);
    send_worker(
        &mut worker.input,
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": 1},
                "inputs": {"Reset": {"root": root, "documents": {path.to_str().unwrap(): source}}},
            },
        }),
    );
    let original = worker.next();
    assert_eq!(
        original["Finished"]["result"]["Ok"]["complete"], true,
        "{original}"
    );

    fs::write(&asset, [0xff]).unwrap();
    let replacement = source.replace("_ = note()", "_ = note(); _ = 1");
    send_worker(
        &mut worker.input,
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": 2},
                "inputs": {"Delta": {path.to_str().unwrap(): replacement}},
            },
        }),
    );
    let changed = worker.next();
    let product = &changed["Finished"]["result"]["Ok"];
    assert_eq!(changed["Finished"]["mode"], "Package");
    assert_eq!(product["complete"], false, "{changed}");
    assert!(
        product["diagnostics"]
            .as_array()
            .unwrap()
            .iter()
            .any(|diagnostic| {
                diagnostic["message"]
                    .as_str()
                    .unwrap()
                    .contains("not valid UTF-8")
            }),
        "{changed}"
    );
}

#[test]
fn registered_file_events_invalidate_cached_disk_sources() {
    let fixture = Fixture::new();
    let mut server = Session::spawn(&mut fixture.command(), Message::read);
    let definitions = fixture.root.join("src/definitions.tr");
    fs::create_dir_all(definitions.parent().unwrap()).unwrap();
    fs::write(&definitions, "func selected() -> int32 { 15 }").unwrap();
    server.request(
        1,
        "initialize",
        json!({
            "capabilities": {"workspace": {"didChangeWatchedFiles": {"dynamicRegistration": true}}},
            "workspaceFolders": [{"name": "test", "uri": as_uri(&fixture.root).as_str()}],
        }),
    );
    server.response(1);
    server.notify("initialized", json!({}));
    let Message::Request(registration) = server.next() else {
        panic!("expected watcher registration");
    };
    assert_eq!(registration.method, "client/registerCapability");
    let watch = &registration.params["registrations"][0];
    assert_eq!(watch["method"], "workspace/didChangeWatchedFiles");
    assert_eq!(
        watch["registerOptions"]["watchers"][0]["globPattern"],
        "**/*.tr"
    );
    Message::Response(Response::new_ok(registration.id, Value::Null))
        .write(&mut server.input)
        .unwrap();

    let active = as_uri(&fixture.root.join("src/main.tr"));
    let text = "func inspect() { result := selected(); _ = result }";
    server.open(active.as_str(), text);
    server.request(2, "textDocument/hover", at(active.as_str(), text, "result"));
    assert_eq!(server.response(2)["contents"]["value"], "int32");

    fs::write(&definitions, "func selected() -> bool { true }").unwrap();
    server.notify(
        "workspace/didChangeWatchedFiles",
        json!({"changes": [{"uri": as_uri(&definitions).as_str(), "type": 2}]}),
    );
    server.request(3, "textDocument/hover", at(active.as_str(), text, "result"));
    assert_eq!(server.response(3)["contents"]["value"], "bool");
}

#[test]
fn stdio_reserves_stdout_for_lsp_messages_and_exits_on_shutdown() {
    let fixture = Fixture::new();
    let mut server = Session::spawn(fixture.command().arg("--stdio"), Message::read);
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
    copy_std(&std);
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
    let staging = fixture.root.join("staging");
    assert!(
        Command::new(env!("CARGO_BIN_EXE_taro-lsp"))
            .arg("--prepare-bundle")
            .arg(&staging)
            .arg(&std)
            .arg(&fixture.facts)
            .arg(&arm)
            .status()
            .unwrap()
            .success()
    );
    let bundle = fixture.root.join("installed-bundle");
    fs::rename(staging, &bundle).unwrap();

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
    let arm_snapshot = bundle.join("targets/aarch64-unknown-linux-gnu.std");
    assert!(fs::metadata(&arm_snapshot).unwrap().len() > 32);
    fs::write(arm_snapshot, b"invalid snapshot").unwrap();
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

#[test]
fn sdk_uses_canonical_sources_and_reuses_the_snapshot_after_restart() {
    let fixture = Fixture::new();
    let root = fixture.root.canonicalize().unwrap();
    let sdk = root.join("sdk");
    let runtime = sdk.join("lib/taro/runtime");
    fs::create_dir_all(&runtime).unwrap();
    fs::copy(&fixture.facts, runtime.join("target-facts.toml")).unwrap();
    let std = sdk.join("std");
    copy_std(&std);
    let selected = std.join("src/lsp_sdk_fixture.tr");
    fs::write(&selected, "public func sdkSelected() -> int32 { 15 }\n").unwrap();

    let project = root.join("project");
    fs::create_dir(&project).unwrap();
    let open_path = project.join("src/use.tr");
    let reset = |revision| {
        json!({
            "Analyze": {
                "stamp": {"generation": 1, "revision": revision},
                "inputs": {"Reset": {
                    "root": project,
                    "documents": {open_path.to_str().unwrap(): "func check() { _ = std::sdkSelected() }"},
                }},
            },
        })
    };
    let cache = root.join("cache");
    let snapshot = cache.join("std.snapshot");
    let mut command = Command::new(env!("CARGO_BIN_EXE_taro-lsp"));
    command
        .arg("--worker")
        .env("TARO_HOME", &sdk)
        .env("TARO_LSP_CACHE_DIR", &cache);
    let assert_definition = |reply: Value, ty: Value| {
        let product = &reply["Finished"]["result"]["Ok"];
        assert_eq!(product["complete"], true, "{reply}");
        assert!(
            product["occurrences"]
                .as_array()
                .unwrap()
                .iter()
                .any(|item| {
                    item["declaration"]["name"] == "sdkSelected"
                        && item["declaration"]["source"]["path"] == selected.to_str().unwrap()
                        && item["ty"] == ty
                }),
            "{product}"
        );
    };
    let mut worker = Session::spawn(&mut command, read_worker);
    send_worker(&mut worker.input, reset(1));
    assert_definition(worker.next(), json!({"Int": "I32"}));
    let cached = fs::metadata(&snapshot).unwrap();
    assert!(cached.len() > 96);
    drop(worker);

    command
        .arg("--sdk")
        .arg(&sdk)
        .env("TARO_HOME", root.join("invalid"));
    let mut worker = Session::spawn(&mut command, read_worker);
    send_worker(&mut worker.input, reset(1));
    assert_definition(worker.next(), json!({"Int": "I32"}));
    assert_eq!(
        fs::metadata(&snapshot).unwrap().modified().unwrap(),
        cached.modified().unwrap()
    );

    fs::write(&selected, "public func sdkSelected() -> bool { true }\n").unwrap();
    send_worker(&mut worker.input, reset(2));
    assert_definition(worker.next(), json!("Bool"));
    assert_ne!(
        fs::metadata(&snapshot).unwrap().modified().unwrap(),
        cached.modified().unwrap()
    );
    assert_eq!(fs::read_dir(cache).unwrap().count(), 2);
}

#[test]
fn definitions_continue_inside_sdk_sources() {
    let fixture = Fixture::new();
    let root = fixture.root.canonicalize().unwrap();
    let sdk = root.join("sdk");
    let runtime = sdk.join("lib/taro/runtime");
    fs::create_dir_all(&runtime).unwrap();
    fs::copy(&fixture.facts, runtime.join("target-facts.toml")).unwrap();
    let std = sdk.join("std");
    copy_std(&std);
    let entry = as_uri(&std.join("src/lsp_navigation_entry.tr"));
    let sibling = as_uri(&std.join("src/lsp_navigation_target.tr"));
    let entry_text = "public func sdkEntry() -> int32 { std::sdkTarget() }\n";
    let sibling_text = "public func sdkTarget() -> int32 { 42 }\n";
    fs::write(entry.to_file_path().unwrap(), entry_text).unwrap();
    fs::write(sibling.to_file_path().unwrap(), sibling_text).unwrap();

    let project = root.join("project");
    fs::create_dir(&project).unwrap();
    let active = as_uri(&project.join("src/use.tr"));
    let active_text = "func check() { _ = std::sdkEntry() }";
    let mut command = Command::new(env!("CARGO_BIN_EXE_taro-lsp"));
    command
        .arg("--sdk")
        .arg(&sdk)
        .env("TARO_LSP_CACHE_DIR", root.join("cache"));
    let mut server = Session::spawn(&mut command, Message::read);
    server.request(
        1,
        "initialize",
        json!({"capabilities": {}, "rootUri": as_uri(&project).as_str()}),
    );
    server.response(1);
    server.notify("initialized", json!({}));
    server.open(active.as_str(), active_text);
    loop {
        if let Message::Notification(note) = server.next()
            && note.method == "textDocument/publishDiagnostics"
            && note.params["uri"] == active.as_str()
        {
            assert_eq!(note.params["diagnostics"], json!([]));
            break;
        }
    }
    server.request(
        2,
        "textDocument/definition",
        at(active.as_str(), active_text, "sdkEntry"),
    );
    assert_eq!(server.response(2)["uri"], entry.as_str());

    server.open(entry.as_str(), entry_text);
    server.request(
        3,
        "textDocument/definition",
        at(entry.as_str(), entry_text, "sdkTarget"),
    );
    assert_eq!(
        server.response(3),
        json!({"uri": sibling.as_str(), "range": {
            "start": {"line": 0, "character": 12}, "end": {"line": 0, "character": 21}
        }})
    );

    let shifted = format!("\n{sibling_text}");
    server.open(sibling.as_str(), &shifted);
    server.request(
        4,
        "textDocument/definition",
        at(entry.as_str(), entry_text, "sdkTarget"),
    );
    assert_eq!(server.response(4)["range"]["start"]["line"], 1);
    server.request(
        5,
        "textDocument/definition",
        at(active.as_str(), active_text, "sdkEntry"),
    );
    assert_eq!(server.response(5)["uri"], entry.as_str());

    for uri in [&entry, &sibling] {
        server.notify(
            "textDocument/didClose",
            json!({"textDocument": {"uri": uri.as_str()}}),
        );
    }
    server.request(
        6,
        "textDocument/definition",
        at(entry.as_str(), entry_text, "sdkTarget"),
    );
    assert_eq!(server.response(6), Value::Null);
    server.open(entry.as_str(), entry_text);
    server.request(
        7,
        "textDocument/definition",
        at(entry.as_str(), entry_text, "sdkTarget"),
    );
    assert_eq!(server.response(7)["range"]["start"]["line"], 0);
}

#[test]
fn editor_features_follow_two_unsaved_files_and_clear_repaired_diagnostics() {
    let fixture = Fixture::new();
    let mut server = Session::spawn(&mut fixture.command(), Message::read);
    let root = as_uri(&fixture.root);
    server.request(
        1,
        "initialize",
        json!({
            "capabilities": {},
            "workspaceFolders": [{ "name": "test", "uri": root.as_str() }],
        }),
    );
    let capabilities = server.response(1);
    assert_eq!(capabilities["capabilities"]["hoverProvider"], true);
    server.notify("initialized", json!({}));

    let definitions = as_uri(&fixture.root.join("src/definitions.tr"));
    let active = as_uri(&fixture.root.join("src/active.tr"));
    server.open(
        definitions.as_str(),
        concat!(
            "func choose(_ value: int32) -> int32 { value }\n",
            "func choose(_ value: bool) -> string { \"selected\" }\n",
            "struct Sample { count: int32 }\n",
            "extend Sample {\n",
            "    public func show() -> int32 { self.count }\n",
            "    public static func make() -> Sample { Sample { count: 1 } }\n",
            "}\n",
        ),
    );
    let original = concat!(
        "func inspect() {\n",
        "    input := 7\n",
        "    _ = \"🌱\"; value := choose(input)\n",
        "    _ = value\n",
        "    item := Sample::make()\n",
        "    _ = item.show()\n",
        "}\n",
    );
    server.open(active.as_str(), original);
    server.request(
        2,
        "textDocument/definition",
        at(active.as_str(), original, "choose"),
    );
    let first = server.response(2);
    assert_eq!(first["uri"], definitions.as_str());
    assert_eq!(first["range"]["start"]["line"], 0);

    let changed = original.replace("input := 7", "input := true");
    server.change(active.as_str(), 2, &changed);
    server.request(
        3,
        "textDocument/definition",
        at(active.as_str(), &changed, "choose"),
    );
    let second = server.response(3);
    assert_eq!(second["uri"], definitions.as_str());
    assert_eq!(second["range"]["start"]["line"], 1);
    server.request(
        4,
        "textDocument/hover",
        at(active.as_str(), &changed, "value"),
    );
    assert_eq!(server.response(4)["contents"]["value"], "string");

    let dot = changed.replace("_ = item.show()", "item.");
    server.change(active.as_str(), 3, &dot);
    let mut caret = at(active.as_str(), &dot, "item.");
    let character = caret["position"]["character"].as_u64().unwrap() + 5;
    caret["position"]["character"] = character.into();
    server.request(5, "textDocument/completion", caret);
    let mut saw_diagnostic = false;
    loop {
        match server.next() {
            Message::Notification(note)
                if note.method == "textDocument/publishDiagnostics"
                    && note.params["uri"] == active.as_str()
                    && note.params["version"] == 3 =>
            {
                saw_diagnostic = !note.params["diagnostics"].as_array().unwrap().is_empty();
            }
            Message::Response(response) => {
                assert_eq!(response.id, 5.into());
                let completions = response.response_result.unwrap();
                let labels = completions
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|item| item["label"].as_str().unwrap())
                    .collect::<Vec<_>>();
                assert_eq!(labels, ["count", "show"]);
                break;
            }
            _ => {}
        }
    }
    assert!(saw_diagnostic);

    server.change(active.as_str(), 4, &changed);
    loop {
        if let Message::Notification(note) = server.next()
            && note.method == "textDocument/publishDiagnostics"
            && note.params["uri"] == active.as_str()
            && note.params["version"] == 4
        {
            assert!(note.params["diagnostics"].as_array().unwrap().is_empty());
            break;
        }
    }
    let qualifier = at(active.as_str(), &changed, "Sample::make");
    server.request(6, "textDocument/hover", qualifier.clone());
    assert_eq!(server.response(6)["contents"]["value"], "Sample");
    server.request(7, "textDocument/definition", qualifier);
    let definition = server.response(7);
    assert_eq!(definition["uri"], definitions.as_str());
    assert_eq!(definition["range"]["start"]["line"], 2);

    server.request(8, "shutdown", Value::Null);
    assert_eq!(server.response(8), Value::Null);
    server.notify("exit", Value::Null);
}
