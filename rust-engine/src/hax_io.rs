//! This module helps communicating with `cargo-hax`.

use crate::ocaml_engine::ExtendedToEngine;
use hax_types::engine_api::protocol::FromEngine;
use std::io::{BufReader, Stdin, stdin, stdout};
use std::sync::{LazyLock, Mutex};

static STDIN: LazyLock<Mutex<serde_jsonlines::JsonLinesIter<BufReader<Stdin>, ExtendedToEngine>>> =
    LazyLock::new(|| {
        use serde_jsonlines::BufReadExt;
        Mutex::new(BufReader::new(stdin()).json_lines())
    });

/// Reads a `ExtendedToEngine` message
pub fn read() -> ExtendedToEngine {
    let mut stdin = STDIN.lock().unwrap();
    stdin
        .next()
        .expect("No message left! Did the engine crash?")
        .expect("Could not parse as a `ExtendedToEngine` message!")
}

/// Writes a `ExtendedFromEngine` message
pub fn write(message: &FromEngine) {
    use std::io::Write;

    let mut stdout = stdout();
    serde_json::to_writer(&mut stdout, message).unwrap();
    stdout.write_all(b"\n").unwrap();
    stdout.flush().unwrap();
}
