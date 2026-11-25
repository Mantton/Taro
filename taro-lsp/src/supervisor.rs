//! Keep the editor connection alive independently of a compiler process.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsString,
    io::{self, BufReader, BufWriter},
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

use compiler::compile::analysis_products::AnalysisProduct;
use crossbeam_channel::{Receiver, Sender, TryRecvError, bounded};

use crate::protocol::{self, AnalysisRequest, FromWorker, Inputs, Stamp, ToWorker};

const MAX_PENDING_FILES: usize = 256;

#[derive(Clone)]
pub struct Launch {
    pub program: PathBuf,
    pub arguments: Vec<OsString>,
}

#[derive(Clone, Copy)]
pub struct Policy {
    pub timeout: Duration,
    pub restart_delay: Duration,
    pub restart_limit: Duration,
}

impl Default for Policy {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            restart_delay: Duration::from_millis(100),
            restart_limit: Duration::from_secs(3),
        }
    }
}

pub enum Notice {
    Current(Box<AnalysisProduct>),
    Unavailable(String),
}

pub struct Supervisor {
    root: PathBuf,
    launch: Launch,
    policy: Policy,
    process: Option<Process>,
    generation: u64,
    revision: u64,
    flight: Option<Flight>,
    documents: BTreeMap<PathBuf, Document>,
    pending: BTreeSet<PathBuf>,
    reset: bool,
    failures: u32,
    restart_at: Instant,
}

struct Document {
    version: i32,
    text: String,
}

struct Flight {
    stamp: Stamp,
    started: Instant,
    cancel_sent: bool,
}

impl Supervisor {
    pub fn new(root: PathBuf, launch: Launch, policy: Policy) -> Self {
        Self {
            root,
            launch,
            policy,
            process: None,
            generation: 0,
            revision: 1,
            flight: None,
            documents: BTreeMap::new(),
            pending: BTreeSet::new(),
            reset: true,
            failures: 0,
            restart_at: Instant::now(),
        }
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn set_document(&mut self, path: PathBuf, version: i32, text: String) -> bool {
        if self
            .documents
            .get(&path)
            .is_some_and(|document| document.version >= version)
        {
            return false;
        }
        self.documents
            .insert(path.clone(), Document { version, text });
        self.changed(path);
        true
    }

    pub fn close_document(&mut self, path: &Path) -> bool {
        if self.documents.remove(path).is_none() {
            return false;
        }
        self.changed(path.to_path_buf());
        true
    }

    pub fn filesystem_changed(&mut self) {
        self.advance();
        self.reset = true;
        self.pending.clear();
    }

    fn changed(&mut self, path: PathBuf) {
        self.advance();
        if self.reset {
            return;
        }
        self.pending.insert(path);
        if self.pending.len() > MAX_PENDING_FILES {
            self.reset = true;
            self.pending.clear();
        }
    }

    fn advance(&mut self) {
        self.revision = self
            .revision
            .checked_add(1)
            .expect("workspace revision exhausted");
    }

    /// Perform a bounded amount of scheduling work on the protocol thread.
    /// I/O with the compiler is isolated in the child process and pipe threads.
    pub fn drive(&mut self, now: Instant) -> Option<Notice> {
        if let Some(process) = &self.process {
            match process.replies.try_recv() {
                Ok(Ok(reply)) => {
                    if let Some(notice) = self.accept(reply, now) {
                        return Some(notice);
                    }
                }
                Ok(Err(error)) => return Some(self.failed(now, error)),
                Err(TryRecvError::Disconnected) => {
                    return Some(self.failed(now, "analysis worker disconnected".into()));
                }
                Err(TryRecvError::Empty) => {}
            }
        }

        if let Some(flight) = &mut self.flight {
            if now.duration_since(flight.started) >= self.policy.timeout {
                return Some(self.failed(now, "analysis worker timed out".into()));
            }
            if flight.stamp.revision < self.revision
                && !flight.cancel_sent
                && let Some(process) = &self.process
            {
                flight.cancel_sent = process
                    .commands
                    .try_send(ToWorker::Cancel {
                        revision: flight.stamp.revision,
                    })
                    .is_ok();
            }
            return None;
        }

        if self.process.is_none() {
            if now < self.restart_at {
                return None;
            }
            match Process::launch(&self.launch) {
                Ok(process) => self.process = Some(process),
                Err(error) => {
                    return Some(self.failed(now, format!("cannot launch worker: {error}")));
                }
            }
            self.generation = self
                .generation
                .checked_add(1)
                .expect("worker generations exhausted");
        }
        if !self.reset && self.pending.is_empty() {
            return None;
        }
        let inputs = if self.reset {
            Inputs::Reset {
                root: self.root.clone(),
                documents: self
                    .documents
                    .iter()
                    .map(|(path, document)| (path.clone(), document.text.clone()))
                    .collect(),
            }
        } else {
            Inputs::Delta(
                self.pending
                    .iter()
                    .map(|path| {
                        (
                            path.clone(),
                            self.documents
                                .get(path)
                                .map(|document| document.text.clone()),
                        )
                    })
                    .collect(),
            )
        };
        let stamp = Stamp {
            generation: self.generation,
            revision: self.revision,
        };
        let request = ToWorker::Analyze(AnalysisRequest { stamp, inputs });
        if self
            .process
            .as_ref()
            .unwrap()
            .commands
            .try_send(request)
            .is_err()
        {
            return Some(self.failed(
                now,
                "analysis worker did not accept the next revision".into(),
            ));
        }
        self.flight = Some(Flight {
            stamp,
            started: now,
            cancel_sent: false,
        });
        self.reset = false;
        self.pending.clear();
        None
    }

    fn accept(&mut self, reply: FromWorker, now: Instant) -> Option<Notice> {
        let stamp = reply.stamp();
        if self.flight.as_ref().map(|flight| flight.stamp) != Some(stamp) {
            return None;
        }
        self.flight = None;
        if stamp.revision != self.revision {
            return None;
        }
        match reply {
            FromWorker::Finished {
                result: Ok(product),
                ..
            } if product.revision == stamp.revision => {
                self.failures = 0;
                Some(Notice::Current(product))
            }
            FromWorker::Finished {
                result: Err(error), ..
            } => Some(Notice::Unavailable(error)),
            FromWorker::Finished { .. } => {
                Some(self.failed(now, "worker reply used a different revision".into()))
            }
            FromWorker::Cancelled(_) => {
                Some(self.failed(now, "worker cancelled the current revision".into()))
            }
        }
    }

    fn failed(&mut self, now: Instant, error: String) -> Notice {
        self.process.take();
        self.flight = None;
        self.reset = true;
        self.pending.clear();
        let multiplier = 2u32.pow(self.failures.min(8));
        let delay = self
            .policy
            .restart_delay
            .saturating_mul(multiplier)
            .min(self.policy.restart_limit);
        self.restart_at = now + delay;
        self.failures = self.failures.saturating_add(1);
        Notice::Unavailable(error)
    }
}

struct Process {
    child: Child,
    commands: Sender<ToWorker>,
    replies: Receiver<Result<FromWorker, String>>,
    io: Option<(JoinHandle<()>, JoinHandle<()>)>,
}

impl Process {
    fn launch(launch: &Launch) -> io::Result<Self> {
        let mut child = Command::new(&launch.program)
            .args(&launch.arguments)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        let stdin = child.stdin.take().expect("piped worker input");
        let stdout = child.stdout.take().expect("piped worker output");
        let (commands, requests) = bounded::<ToWorker>(2);
        let (events, replies) = bounded(1);
        let writing_errors = events.clone();
        let writer = thread::spawn(move || {
            let mut output = BufWriter::new(stdin);
            for request in requests {
                if let Err(error) = protocol::write(&mut output, &request) {
                    let _ = writing_errors.send(Err(error.to_string()));
                    return;
                }
            }
        });
        let reader = thread::spawn(move || {
            let mut input = BufReader::new(stdout);
            loop {
                let event = match protocol::read(&mut input) {
                    Ok(Some(reply)) => Ok(reply),
                    Ok(None) => Err("analysis worker exited".into()),
                    Err(error) => Err(error.to_string()),
                };
                let ended = event.is_err();
                if events.send(event).is_err() || ended {
                    break;
                }
            }
        });
        Ok(Self {
            child,
            commands,
            replies,
            io: Some((reader, writer)),
        })
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        // Closing the channels before joining releases a blocked sender or
        // receiver even when the worker is hung or the parent stops polling.
        self.commands = bounded(0).0;
        self.replies = bounded(0).1;
        let _ = self.child.kill();
        let _ = self.child.wait();
        if let Some((reader, writer)) = self.io.take() {
            let _ = reader.join();
            let _ = writer.join();
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{
        ffi::OsString,
        path::PathBuf,
        thread,
        time::{Duration, Instant},
    };

    use super::{Launch, Notice, Policy, Supervisor};

    fn supervisor(timeout: Duration) -> Supervisor {
        Supervisor::new(
            PathBuf::from("/workspace"),
            Launch {
                program: PathBuf::from("python3"),
                arguments: vec![
                    OsString::from("-c"),
                    OsString::from(include_str!("../tests/worker_probe.py")),
                ],
            },
            Policy {
                timeout,
                restart_delay: Duration::from_millis(25),
                restart_limit: Duration::from_millis(100),
            },
        )
    }

    #[test]
    fn recover_crash_and_hang_with_two_unsaved_files() {
        for (directive, expected) in [("force crash", "exited"), ("force hang", "timed out")] {
            let mut supervisor = supervisor(Duration::from_millis(450));
            supervisor.set_document("/workspace/src/a.tr".into(), 1, directive.into());
            supervisor.set_document("/workspace/src/b.tr".into(), 1, "unsaved sibling".into());
            let deadline = Instant::now() + Duration::from_secs(7);
            let mut recovered = false;
            let mut unavailable = false;
            while Instant::now() < deadline {
                match supervisor.drive(Instant::now()) {
                    Some(Notice::Unavailable(message)) => {
                        assert!(message.contains(expected), "{message}");
                        unavailable = true;
                        supervisor.set_document(
                            "/workspace/src/b.tr".into(),
                            2,
                            "updated sibling".into(),
                        );
                    }
                    Some(Notice::Current(product)) => {
                        assert!(unavailable);
                        assert_eq!(supervisor.generation, 2);
                        assert_eq!(
                            product.diagnostics[0].message,
                            format!("{directive}\nupdated sibling")
                        );
                        recovered = true;
                        break;
                    }
                    None => thread::sleep(Duration::from_millis(4)),
                }
            }
            assert!(recovered, "{directive}");
        }
    }

    #[test]
    fn a_late_reply_is_discarded_and_edits_coalesce_into_latest_text() {
        let mut supervisor = supervisor(Duration::from_secs(3));
        supervisor.set_document("/workspace/src/a.tr".into(), 1, "delay reply".into());
        supervisor.drive(Instant::now());
        let original_revision = supervisor.flight.as_ref().unwrap().stamp.revision;
        for version in 2..=300 {
            supervisor.set_document(
                "/workspace/src/a.tr".into(),
                version,
                format!("edited {version}"),
            );
        }
        supervisor.set_document("/workspace/src/b.tr".into(), 1, "second buffer".into());
        assert_eq!(supervisor.pending.len(), 2);
        assert!(!supervisor.set_document("/workspace/src/a.tr".into(), 2, "stale text".into()));
        let deadline = Instant::now() + Duration::from_secs(7);
        while Instant::now() < deadline {
            match supervisor.drive(Instant::now()) {
                Some(Notice::Current(product)) => {
                    assert!(product.revision > original_revision);
                    assert_eq!(product.revision, supervisor.revision);
                    assert_eq!(product.diagnostics[0].message, "edited 300\nsecond buffer");
                    assert_eq!(supervisor.generation, 1);
                    return;
                }
                Some(Notice::Unavailable(message)) => panic!("{message}"),
                None => thread::sleep(Duration::from_millis(4)),
            }
        }
        panic!("never received the current revision");
    }
}
