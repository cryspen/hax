//! An example template backend for hax.
//! Feel free to duplicate this backend to create your own, replacing `Template` by the name of your backend.

use super::prelude::*;

/// The printer.
#[derive(Default)]
pub struct TemplatePrinter;
impl_doc_allocator_for!(TemplatePrinter);

impl Printer for TemplatePrinter {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![]
    }

    const NAME: &'static str = "Template";
}

/// The backend.
pub struct TemplateBackend;

impl Backend for TemplateBackend {
    type Printer = TemplatePrinter;

    fn module_path(&self, _module: &Module) -> std::path::PathBuf {
        std::path::PathBuf::from("file.ext")
    }
}

#[prepend_associated_functions_with(install_pretty_helpers!(self: Self))]
// Tagging the `impl` directly with `prepend_associated_functions_with` prevent
// auto completion from Rust Analyzer, thus we have this `const`.
const _: () = {
    // Boilerplate: define local macros to disambiguate otherwise `std` macros.
    #[allow(unused)]
    macro_rules! todo {($($tt:tt)*) => {disambiguated_todo!($($tt)*)};}
    #[allow(unused)]
    macro_rules! line {($($tt:tt)*) => {disambiguated_line!($($tt)*)};}
    #[allow(unused)]
    macro_rules! concat {($($tt:tt)*) => {disambiguated_concat!($($tt)*)};}

    impl<'a, 'b, A: 'a + Clone> PrettyAst<'a, 'b, A> for TemplatePrinter {
        // To be completed.
    }
};
