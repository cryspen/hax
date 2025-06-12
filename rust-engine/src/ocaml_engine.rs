//! This module implements an interface to the OCaml hax engine. Via this
//! interface, the rust engine can communicate with the OCaml engine, and reuse
//! some of its components.

use hax_frontend_exporter::ThirBody;
use hax_types::engine_api::{
    protocol::{FromEngine, ToEngine},
    EngineOptions,
};

/// A query for the OCaml engine
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
pub struct Query {
    pub hax_version: String,
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    pub kind: QueryKind,
}

/// The payload of the query. [`Response`] below mirrors this enum to represent
/// the response from the engine.
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
pub enum QueryKind {
    /// Ask the OCaml engine to import the given THIR from the frontend
    ImportThir {
        input: Vec<hax_frontend_exporter::Item<ThirBody>>,
    },
}

#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
pub enum Response {
    /// Return imported THIR as an internal AST from Rust engine
    ImportThir { output: Vec<crate::ast::Item> },
}

/// Extends the common `FromEngine` messages with one extra case: `Response`.
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
#[serde(untagged)]
pub enum ExtendedFromEngine {
    FromEngine(FromEngine),
    Response(Response),
}

/// Extends the common `ToEngine` messages with one extra case: `Input`.
#[derive(::serde::Deserialize, ::serde::Serialize)]
#[serde(untagged)]
pub enum ExtendedToEngine {
    ToEngine(ToEngine),
    Input(hax_frontend_exporter::id_table::WithTable<EngineOptions>),
}

impl Query {
    /// Execute the query synchronously.
    pub fn execute(&self) -> Option<Response> {
        use std::io::Write;
        use std::process::Command;

        macro_rules! send {
            ($where: expr, $value:expr) => {
                serde_json::to_writer(&mut $where, $value).unwrap();
                $where.write_all(b"\n").unwrap();
                $where.flush().unwrap();
            };
        }

        let mut engine_subprocess = Command::new("hax-engine")
            .arg("driver_rust_engine")
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();

        let mut stdin = std::io::BufWriter::new(
            engine_subprocess
                .stdin
                .as_mut()
                .expect("Could not write on stdin"),
        );

        // TODO: send a table here
        send!(stdin, self);

        let mut response = None;
        let stdout = std::io::BufReader::new(engine_subprocess.stdout.take().unwrap());
        for msg in stdout.lines() {
            let msg = msg.unwrap();

            let mut de = Deserializer::from_str(&msg);
            de.disable_recursion_limit();
            let de = serde_stacker::Deserializer::new(&mut de);
            let msg = ExtendedFromEngine::deserialize(de);
            // for msg in json_lines(stdout) {
            let msg = msg.expect(
                "Hax engine sent an invalid json value. \
                            This might be caused by debug messages on stdout, \
                            which is reserved for JSON communication with cargo-hax",
            );
            match msg {
                ExtendedFromEngine::Response(res) => response = Some(res),
                ExtendedFromEngine::FromEngine(FromEngine::Exit) => break,
                // Proxy messages from the OCaml engine
                ExtendedFromEngine::FromEngine(from_engine) => {
                    crate::hax_io::write(&from_engine);
                    if from_engine.requires_response() {
                        let ExtendedToEngine::ToEngine(response) = crate::hax_io::read() else {
                            panic!("The frontend sent an incorrect message: expected `ExtendedToEngine::ToEngine` since we sent a `ExtendedFromEngine::FromEngine`.")
                        };
                        send!(stdin, &response);
                    }
                }
            }
        }
        drop(stdin);

        let exit_status = engine_subprocess.wait().unwrap();
        if !exit_status.success() {
            eprintln!("ocaml engine crashed, {:#?}", exit_status);
        }

        response
    }
}

// use json_lines_stupid as json_lines;

// pub fn json_lines_stupid<'a, R, T: 'static>(
//     reader: R,
// ) -> impl Iterator<Item = Result<T, serde_json::Error>> + 'a
// where
//     R: BufRead + 'a,
//     T: Deserialize<'a>,
// {
//     reader.lines().flat_map(|line| line).map(|line| {
//         let mut de = Deserializer::from_str(&line);
//         de.disable_recursion_limit();
//         let de = serde_stacker::Deserializer::new(&mut de);
//         let v = T::deserialize(de).unwrap();
//         todo!()
//     })
//     // let it: Vec<_> = reader
//     //     .split(b'\n')
//     //     .filter_map(|res| match res {
//     //         Ok(bytes) if !bytes.is_empty() => Some(bytes),
//     //         _ => None, // skip empty or failed lines
//     //     })
//     //     .collect();
//     // it.iter().map(|bytes| {
//     //     let mut de = Deserializer::from_slice(bytes);
//     //     de.disable_recursion_limit();
//     //     let de = serde_stacker::Deserializer::new(&mut de);
//     //     Ok(T::deserialize(de).unwrap())
//     // }).collect::Vec<_>()
// }

use serde::de::Deserialize;
use serde_json::de::Deserializer;
use serde_stacker;
use std::io::{self, BufRead, Read};

/// Returns an iterator over JSON values parsed one line at a time,
/// without buffering the whole line or allocating unnecessary memory.
pub fn json_lines_opt<'a, R, T>(
    mut reader: R,
) -> impl Iterator<Item = Result<T, serde_json::Error>> + 'a
where
    R: BufRead + 'a,
    T: Deserialize<'a>,
{
    /// A reader adapter that injects an artificial EOF after the first newline.
    pub struct LineAsEOF<'a, R: BufRead> {
        reader: &'a mut R,
        done: bool,
    }

    impl<'a, R: BufRead> LineAsEOF<'a, R> {
        pub fn new(reader: &'a mut R) -> Self {
            Self {
                reader,
                done: false,
            }
        }
    }

    impl<'a, R: BufRead> Read for LineAsEOF<'a, R> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            if self.done {
                return Ok(0); // Simulate EOF
            }

            let available = self.reader.fill_buf()?;

            if available.is_empty() {
                return Ok(0); // Upstream EOF
            }

            let newline_pos = available.iter().position(|&b| b == b'\n');
            let to_read = match newline_pos {
                Some(pos) => {
                    self.done = true;
                    pos + 1 // include newline
                }
                None => available.len(),
            };

            let to_copy = to_read.min(buf.len());
            buf[..to_copy].copy_from_slice(&available[..to_copy]);
            self.reader.consume(to_copy);
            Ok(to_copy)
        }
    }
    std::iter::from_fn(move || {
        let mut sub_reader = LineAsEOF::new(&mut reader);
        let mut de = Deserializer::from_reader(&mut sub_reader);
        de.disable_recursion_limit();

        let de = serde_stacker::Deserializer::new(&mut de);

        match T::deserialize(de) {
            Ok(val) => Some(Ok(val)),
            Err(err) if err.is_eof() => None, // Proper end
            Err(err) => Some(Err(err)),
        }
    })
}
