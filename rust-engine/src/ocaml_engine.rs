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
        use serde_jsonlines::BufReadExt;
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
        for msg in stdout.json_lines() {
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
            panic!("ocaml engine crashed");
        }

        response
    }
}
