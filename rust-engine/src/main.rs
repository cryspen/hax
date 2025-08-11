use hax_rust_engine::{
    ast::{span::Span, Item},
    lean::Lean,
    ocaml_engine::{ExtendedToEngine, Response},
    printer::{Allocator, self, Print},
};
use hax_types::{cli_options::Backend, engine_api::File};
use pretty::{DocAllocator, DocBuilder};

fn krate_name(items: &Vec<Item>) -> String {
    let head_item = items.get(0).unwrap();
    head_item.ident.krate()
}

fn lean_backend(items: Vec<Item>) {
    let krate = krate_name(&items);

    hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(File {
        path: krate + ".lean",
        contents: <Lean as printer::Print<_>>::print(Lean, printer::File (items)).unwrap().0,
        sourcemap: None,
    }));
}

fn main() {
    let ExtendedToEngine::Query(input) = hax_rust_engine::hax_io::read() else {
        panic!()
    };
    let (value, _map) = input.destruct();

    let query = hax_rust_engine::ocaml_engine::Query {
        hax_version: value.hax_version,
        impl_infos: value.impl_infos,
        kind: hax_rust_engine::ocaml_engine::QueryKind::ImportThir {
            input: value.input,
            apply_phases: !matches!(&value.backend.backend, Backend::GenerateRustEngineNames),
        },
    };

    let Some(Response::ImportThir { output: items }) = query.execute() else {
        panic!()
    };

    match &value.backend.backend {
        Backend::Fstar { .. }
        | Backend::Coq { .. }
        | Backend::Ssprove { .. }
        | Backend::Easycrypt { .. }
        | Backend::ProVerif { .. } => panic!(
            "The Rust engine cannot be called with backend {}.",
            value.backend.backend
        ),
        Backend::Lean => lean_backend(items),
        Backend::GenerateRustEngineNames => hax_rust_engine::hax_io::write(
            &hax_types::engine_api::protocol::FromEngine::File(File {
                path: "generated.rs".into(),
                contents: hax_rust_engine::names::codegen::export_def_ids_to_mod(items),
                sourcemap: None,
            }),
        ),
    }
}
