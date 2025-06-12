use hax_rust_engine::ocaml_engine::{ExtendedToEngine, Response};
use hax_types::engine_api::File;

fn main() {
    let ExtendedToEngine::Input(input) = hax_rust_engine::hax_io::read() else {
        panic!()
    };
    let (value, _map) = input.destruct();

    let query = hax_rust_engine::ocaml_engine::Query {
        hax_version: value.hax_version,
        impl_infos: value.impl_infos,
        kind: hax_rust_engine::ocaml_engine::QueryKind::ImportThir { input: value.input },
    };

    let Some(Response::ImportThir { output: items }) = query.execute() else {
        panic!()
    };

    if let Ok(path) = std::env::var("HAX_RUST_ENGINE_GENERATE_NAMES") {
        let file = hax_rust_engine::names::codegen::export_def_ids_to_mod(items);
        std::fs::write(path, file).expect("Unable to write file");
        return;
    }

    // TOOD: print items
    let _todo = items;

    hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(File {
        path: "empty_module.lean".into(),
        contents: "Hello world!".into(),
        sourcemap: None,
    }));
}
