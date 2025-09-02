//! This module helps communicating with `cargo-hax`.

use crate::ocaml_engine::ExtendedToEngine;
use hax_types::engine_api::protocol::FromEngine;
use serde::Deserialize;
use std::io::{BufRead, BufReader, Stdin, stdin, stdout};
use std::sync::{LazyLock, Mutex};

static STDIN: LazyLock<Mutex<BufReader<Stdin>>> =
    LazyLock::new(|| Mutex::new(BufReader::new(stdin())));

/// Reads a `ExtendedToEngine` message
pub fn read() -> ExtendedToEngine {
    let mut stdin = STDIN.lock().unwrap();
    let mut slice = Vec::new();
    stdin
        .read_until(b'\n', &mut slice)
        .expect("No message left! Did the engine crash?");
    let mut de = serde_json::Deserializer::from_slice(&slice);
    de.disable_recursion_limit();
    ExtendedToEngine::deserialize(serde_stacker::Deserializer::new(&mut de))
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
