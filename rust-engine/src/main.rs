use hax_rust_engine::{
    backends::{self, lean::LeanBackend, rust::RustBackend},
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
            apply_phases: matches!(&value.backend.backend, Backend::Lean),
            translation_options: value.backend.translation_options,
        },
    };

    let Some(Response::ImportThir { output: items }) = query.execute(table) else {
        panic!()
    };

    let backend = &value.backend.backend;
    let files = match backend {
        Backend::Fstar { .. }
        | Backend::Coq
        | Backend::Ssprove
        | Backend::Easycrypt
        | Backend::ProVerif { .. } => panic!(
            "The Rust engine cannot be called with backend {}.",
            value.backend.backend
        ),
        Backend::Lean => backends::Backend::apply(&LeanBackend, items),
        Backend::Rust => backends::Backend::apply(&RustBackend, items),
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
