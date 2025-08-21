//! A Rust backend for hax.
//! Note: for now, this contains only a minimal skeleton of Rust printer, which serves solely as an example printer.

use super::prelude::*;

/// The Rust backend and printer.
pub struct Rust;

impl Printer for Rust {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![]
    }

    const NAME: &str = "Rust";
}

const INDENT: isize = 4;

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

    impl<'a, 'b, A: 'a + Clone> PrettyAst<'a, 'b, A> for Allocator<Rust> {
        fn module(&'a self, module: &'b Module) -> pretty::DocBuilder<'a, Self, A> {
            intersperse!(&module.items, docs![hardline!(), hardline!()])
        }
        fn item(&'a self, item: &'b Item) -> pretty::DocBuilder<'a, Self, A> {
            docs![&item.meta, item.kind()]
        }
        fn item_kind(&'a self, item_kind: &'b ItemKind) -> pretty::DocBuilder<'a, Self, A> {
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
