use hax_rust_engine::{
    generic_printer::{
        doc_printer::ToDoc, lean::LeanPrinter, print_context::PrintContextPayload,
        to_print_view::ToPrintView,
    },
    ocaml_engine::{ExtendedToEngine, Response},
};
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

    let docs = items.iter().map(|item| {
        LeanPrinter.to_doc(
            item.to_print_view(None),
            PrintContextPayload {
                position: "root".into(),
                parent: None,
            },
        )
    });

    let strings: Vec<_> = docs
        .map(|doc| {
            let mut w = Vec::new();
            doc.render(80, &mut w).unwrap();
            String::from_utf8(w).unwrap()
        })
        .collect();

    let header = "-- start \n".to_string();
    let footer = "\n -- eof \n".to_string();
    let contents: String = header + &strings.join("\n") + &footer;

    hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(File {
        path: "empty_module.lean".into(),
        contents: contents,
        sourcemap: None,
    }));
}
