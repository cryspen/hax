//! A Rust backend for hax.
//! Note: for now, this contains only a minimal skeleton of Rust printer, which serves solely as an example printer.

use super::prelude::*;

/// The Rust printer.
#[setup_span_handling_struct]
#[derive(Default, Clone)]
pub struct RustPrinter;

impl Printer for RustPrinter {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![]
    }
}

const INDENT: isize = 4;

/// The Rust backend.
pub struct RustBackend;

impl Backend for RustBackend {
    type Printer = RustPrinter;

    fn module_path(&self, _module: &Module) -> camino::Utf8PathBuf {
        // TODO: dummy path for now, until we have GlobalId rendering (see #1599).
        camino::Utf8PathBuf::from("dummy.rs")
    }
}

#[prepend_associated_functions_with(install_pretty_helpers!(self: Self))]
// Note: the `const` wrapping makes my IDE and LSP happy. Otherwise, I don't get
// autocompletion of methods in the impl block below.
const _: () = {
    // Boilerplate: define local macros to disambiguate otherwise `std` macros.
    #[allow(unused)]
    macro_rules! todo {($($tt:tt)*) => {disambiguated_todo!($($tt)*)};}
    #[allow(unused)]
    macro_rules! line {($($tt:tt)*) => {disambiguated_line!($($tt)*)};}
    #[allow(unused)]
    macro_rules! concat {($($tt:tt)*) => {disambiguated_concat!($($tt)*)};}

    impl<A: 'static + Clone> PrettyAst<A> for RustPrinter {
        const NAME: &'static str = "Rust";

        fn module(&self, module: &Module) -> DocBuilder<A> {
            intersperse!(&module.items, docs![hardline!(), hardline!()])
        }
        fn item(&self, item: &Item) -> DocBuilder<A> {
            docs![&item.meta, item.kind()]
        }
        fn item_kind(&self, item_kind: &ItemKind) -> DocBuilder<A> {
            match item_kind {
                ItemKind::Fn {
                    name,
                    generics: _,
                    body,
                    params,
                    safety,
                } => {
                    docs![
                        safety,
                        text!("fn"),
                        space!(),
                        name,
                        intersperse!(params, docs![",", line!()])
                            .enclose(line_!(), line_!())
                            .nest(INDENT)
                            .parens()
                            .group(),
                        docs![line_!(), body, line_!(),].nest(INDENT).braces()
                    ]
                }
                _ => todo!(),
            }
        }
    }
};
