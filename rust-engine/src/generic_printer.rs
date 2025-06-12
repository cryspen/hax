//! The generic printer. It resolves around a shallow print-friendly view of our
//! AST (module [`print_view`]) and extra resugaring AST fragments (module [`resugar`]).

pub mod print_context;
pub mod print_view;
pub mod resugar;
pub mod to_print_view;
