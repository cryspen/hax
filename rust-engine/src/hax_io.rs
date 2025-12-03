//! This module helps communicating with `cargo-hax`.

use hax_types::engine_api::protocol::FromEngine;
use serde::de::DeserializeOwned;
use std::io::{BufRead, BufReader, Stdin, stdin, stdout};
use std::sync::{LazyLock, Mutex};

use hax_frontend_exporter::id_table::WithTable;
use hax_types::engine_api::{EngineOptions, protocol::ToEngine};

static STDIN: LazyLock<Mutex<BufReader<Stdin>>> =
    LazyLock::new(|| Mutex::new(BufReader::new(stdin())));

/// Reads a message of any type from stdin
fn read<T: DeserializeOwned>() -> T {
    let mut stdin = STDIN.lock().unwrap();
    let mut slice = Vec::new();
    stdin
        .read_until(b'\n', &mut slice)
        .expect("No message left! Did the engine crash?");
    let mut de = serde_json::Deserializer::from_slice(&slice);
    de.disable_recursion_limit();
    T::deserialize(serde_stacker::Deserializer::new(&mut de)).unwrap_or_else(|err| {
        panic!(
            "Could not parse as a `{}` message! Error: {err}",
            std::any::type_name::<T>()
        )
    })
}

/// Reads a `ToEngine` message from the engine
pub fn read_to_engine_message() -> ToEngine {
    read()
}

/// Reads the engine input JSON payload.
pub fn read_engine_input_message() -> WithTable<EngineOptions> {
    read()
}

/// Reads a table of `EngineOptions`
pub fn read_query()
-> hax_frontend_exporter::id_table::WithTable<hax_types::engine_api::EngineOptions> {
    let mut stdin = STDIN.lock().unwrap();
    let mut slice = Vec::new();
    stdin
        .read_until(b'\n', &mut slice)
        .expect("No message left! Did the engine crash?");
    let mut de = serde_json::Deserializer::from_slice(&slice);
    de.disable_recursion_limit();
    hax_frontend_exporter::id_table::WithTable::deserialize(serde_stacker::Deserializer::new(
        &mut de,
    ))
    .expect("Could not parse as a table of EngineOptions!")
}

/// Writes a `ExtendedFromEngine` message
pub fn write(message: &FromEngine) {
    use std::io::Write;

    let mut stdout = stdout();
    serde_json::to_writer(&mut stdout, message).unwrap();
    stdout.write_all(b"\n").unwrap();
    stdout.flush().unwrap();
}
