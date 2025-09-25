//! This module implements an interface to the OCaml hax engine. Via this
//! interface, the rust engine can communicate with the OCaml engine, and reuse
//! some of its components.

use std::io::BufRead;

use hax_frontend_exporter::{
    ThirBody,
    id_table::{Table, WithTable},
};
use hax_types::engine_api::{
    EngineOptions,
    protocol::{FromEngine, ToEngine},
};
use serde::Deserialize;

/// A query for the OCaml engine
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
pub struct Query {
    /// The version of hax currently used
    pub hax_version: String,
    /// Dictionary from `DefId`s to `impl_infos`
    pub impl_infos: Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    /// The kind of query we want to send to the engine
    pub kind: QueryKind,
}

/// The payload of the query. [`Response`] below mirrors this enum to represent
/// the response from the engine.
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
pub enum QueryKind {
    /// Ask the OCaml engine to import the given THIR from the frontend
    ImportThir {
        /// The input THIR items
        input: Vec<hax_frontend_exporter::Item<ThirBody>>,
        /// Temporary option to enable a set of default phases
        apply_phases: bool,
        /// Translation options which contains include clauses (items filtering)
        translation_options: hax_types::cli_options::TranslationOptions,
    },
}

/// A Response after a [`Query`]
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
pub enum Response {
    /// Return imported THIR as an internal AST from Rust engine
    ImportThir {
        /// The output Rust AST items
        output: Vec<crate::ast::Item>,
    },
}

/// Extends the common `ToEngine` messages with one extra case: `Query`.
#[derive(::serde::Deserialize, ::serde::Serialize)]
#[serde(untagged)]
pub enum ExtendedToEngine {
    /// A standard `ToEngine` message
    ToEngine(ToEngine),
    /// A `Query`
    Query(Box<WithTable<EngineOptions>>),
}

/// Extends the common `FromEngine` messages with one extra case: `Response`.
#[derive(Debug, Clone, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)]
#[serde(untagged)]
pub enum ExtendedFromEngine {
    /// A standard `FromEngine` message
    FromEngine(FromEngine),
    /// A `Response`
    Response(Response),
}

impl Query {
    /// Execute the query synchronously.
    pub fn execute(&self, table: Table) -> Option<Response> {
        use std::io::Write;
        use std::process::Command;

        macro_rules! send {
            ($where: expr, $value:expr) => {
                serde_json::to_writer(&mut $where, $value).unwrap();
                $where.write_all(b"\n").unwrap();
                $where.flush().unwrap();
            };
        }

        let mut engine_subprocess =
            Command::new(std::env::var("HAX_ENGINE_BINARY").unwrap_or("hax-engine".into()))
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

        WithTable::run(table, self, |with_table| {
            send!(stdin, with_table);
        });

        let mut response = None;
        let stdout = std::io::BufReader::new(engine_subprocess.stdout.take().unwrap());
        // TODO: this should be streaming (i.e. use a `LineAsEOF` reader wrapper that consumes a reader until `\n` occurs)
        //       See https://github.com/cryspen/hax/issues/1537.
        for slice in stdout.split(b'\n') {
            let msg = (|| {
                let slice = slice.ok()?;
                let mut de = serde_json::Deserializer::from_slice(&slice);
                de.disable_recursion_limit();
                let de = serde_stacker::Deserializer::new(&mut de);
                let msg = ExtendedFromEngine::deserialize(de);
                msg.ok()
            })()
            .expect(
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
                            panic!(
                                "The frontend sent an incorrect message: expected `ExtendedToEngine::ToEngine` since we sent a `ExtendedFromEngine::FromEngine`."
                            )
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
