use hax_rust_engine::{
    backends,
    ocaml_engine::{ExtendedToEngine, Response},
};
use hax_types::{cli_options::Backend, engine_api::File};

fn main() {
    let ExtendedToEngine::Query(input) = hax_rust_engine::hax_io::read() else {
        panic!()
    };
    let (value, table) = input.destruct();

    let query = hax_rust_engine::ocaml_engine::Query {
        hax_version: value.hax_version,
        impl_infos: value.impl_infos,
        kind: hax_rust_engine::ocaml_engine::QueryKind::ImportThir {
            input: value.input,
            apply_phases: !matches!(&value.backend.backend, Backend::GenerateRustEngineNames),
            translation_options: value.backend.translation_options,
        },
    };

    let Some(Response::ImportThir { output: items }) = query.execute(table) else {
        panic!()
    };

    let files = match &value.backend.backend {
        Backend::Fstar { .. }
        | Backend::Coq
        | Backend::Ssprove
        | Backend::Easycrypt
        | Backend::ProVerif { .. } => panic!(
            "The Rust engine cannot be called with backend {}.",
            value.backend.backend
        ),
        Backend::Lean => backends::apply_backend(backends::lean::LeanBackend, items),
        Backend::Rust => backends::apply_backend(backends::rust::RustBackend, items),
        Backend::GenerateRustEngineNames => vec![File {
            path: "generated.rs".into(),
            contents: hax_rust_engine::names::codegen::export_def_ids_to_mod(items),
            sourcemap: None,
        }],
    };
    for file in files {
        hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(file));
    }
}
