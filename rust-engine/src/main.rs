use hax_rust_engine::{
    ast::span::Span,
    lean::Lean,
    ocaml_engine::{ExtendedToEngine, Response},
    printer::Allocator,
};
use hax_types::engine_api::File;

use pretty::{DocAllocator, DocBuilder};

fn main() {
    let ExtendedToEngine::Query(input) = hax_rust_engine::hax_io::read() else {
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

    let allocator = Allocator::new(Lean);
    // TOOD: print items
    let item_docs: DocBuilder<_, Span> = allocator.intersperse(
        items.iter(),
        allocator.hardline().append(allocator.hardline()),
    );

    let mut w = Vec::new();
    let _ = item_docs.render(80, &mut w);
    let content = String::from_utf8(w).unwrap();

    hax_rust_engine::hax_io::write(&hax_types::engine_api::protocol::FromEngine::File(File {
        path: "empty_module.lean".into(),
        contents: content,
        sourcemap: None,
    }));
}
