mod visitors;
use quote::quote;
use syn::{File, visit::Visit, visit_mut::VisitMut};
use visitors::*;

mod helpers;
use helpers::*;
mod inline_mods;

pub(crate) fn main() {
    fn load_source_file_with_inlining() -> File {
        let mut module = read("../src/lib.rs");
        let mut inliner = inline_mods::ModuleInliner::new("../src");
        inliner.visit_file_mut(&mut module);
        module
    }

    let hax_sources = load_source_file_with_inlining();
    let types = &{
        let mut visitable_items = CollectVisitableItems::default();
        visitable_items.visit_file(&hax_sources);
        visitable_items.items
    };
    let mut modules = vec![];
    let mut manual_drivers = vec![];
    for diagnostic_set in [true, false] {
        for short_circuiting in [true, false] {
            for map in [true, false] {
                for reduce in [true, false] {
                    if diagnostic_set && !map {
                        continue;
                    }
                    let kind = VisitorKind {
                        short_circuiting,
                        mutable: map,
                        reduce,
                        diagnostic_set,
                    };
                    let mut make_visitor = VisitorBuilder {
                        kind,
                        types,
                        manual_drivers_templates: vec![],
                    };
                    modules.push(make_visitor.generate_module());
                    manual_drivers.extend_from_slice(&make_visitor.manual_drivers_templates);
                }
            }
        }
    }
    let file = quote! {#(#modules)*};
    write(&file, "../src/ast/visitors/generated.rs");
    let file = quote! {#(#manual_drivers)*};
    write(&file, "../src/ast/visitors/generated_manual_templates.rs");
}
