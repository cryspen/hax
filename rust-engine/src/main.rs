use hax_rust_engine::{
    ast::{Item, span::Span},
    backends,
    ocaml_engine::{ExtendedToEngine, Response},
};
use hax_types::{cli_options::Backend, engine_api::File};

use pretty::{DocAllocator, DocBuilder, docs};

fn krate_name(items: &Vec<Item>) -> String {
    let head_item = items.get(0).unwrap();
    head_item.ident.krate()
}

fn lean_backend(items: Vec<Item>) -> Vec<File> {
    use backends::lean::*;
    let krate = krate_name(&items);

    // For now, the main function always calls the Lean backend
    let allocator = &Allocator::new(Lean);

    let header = docs![
        allocator,
        allocator.intersperse(
            "
-- Experimental lean backend for Hax
-- Lib.lean can be found in hax/proof-libs/lean :
import Lib
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false"
                .lines(),
            allocator.hardline(),
        ),
        allocator.hardline(),
        allocator.hardline()
    ];

    let items = items
        .iter()
        .filter(|item: &&hax_rust_engine::ast::Item| Lean::printable_item(*item));
    let item_docs: DocBuilder<_, Span> =
        header.append(allocator.intersperse(items, allocator.hardline()));

    vec![File {
        path: krate + ".lean",
        contents: item_docs.pretty(80).to_string(),
        sourcemap: None,
    }]
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
            apply_phases: matches!(&value.backend.backend, Backend::Lean),
        },
    };

    let Some(Response::ImportThir { output: items }) = query.execute() else {
        panic!()
    };

    let files = match &value.backend.backend {
        Backend::Fstar { .. }
        | Backend::Coq { .. }
        | Backend::Ssprove { .. }
        | Backend::Easycrypt { .. }
        | Backend::ProVerif { .. } => panic!(
            "The Rust engine cannot be called with backend {}.",
            value.backend.backend
        ),
        Backend::TemplateBackend => {
            backends::apply_backend(backends::template::TemplateBackend, items)
        }
        Backend::Lean => lean_backend(items),
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
