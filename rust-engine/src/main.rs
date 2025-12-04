use hax_rust_engine::{
    backends,
    ocaml_engine::{self, Response},
};
use hax_types::{cli_options::Backend, engine_api::File};
use std::collections::HashMap;

fn main() {
    let (value, table) = hax_rust_engine::hax_io::read_engine_input_message().destruct();

    ocaml_engine::initialize(ocaml_engine::Meta {
        hax_version: value.hax_version,
        impl_infos: value.impl_infos,
        debug_bind_phase: value.backend.debug_engine.is_some(),
        profiling: value.backend.profile,
    });

    let items = match value.input {
        hax_types::driver_api::Items::Legacy(input) => {
            let query = hax_rust_engine::ocaml_engine::QueryKind::ImportThir {
                input,
                translation_options: value.backend.translation_options,
            };

            let Some(Response::ImportThir { output }) = query.execute(Some(table)) else {
                panic!()
            };
            output
        }
        hax_types::driver_api::Items::FullDef(items) => {
            let items: Vec<_> = items
                .into_iter()
                .filter(|item| {
                    !matches!(
                        item.kind,
                        hax_frontend_exporter::FullDefKind::Use
                            | hax_frontend_exporter::FullDefKind::ExternCrate
                    )
                })
                .collect();
            let items_by_def_id = HashMap::from_iter(
                items
                    .iter()
                    .map(|item| (item.this.contents().def_id.clone(), item)),
            );
            items
                .iter()
                .flat_map(|item| hax_rust_engine::import_thir::import_item(&item, &items_by_def_id))
                .collect()
        }
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
