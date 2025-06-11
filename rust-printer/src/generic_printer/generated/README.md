This folder contains generated code by the crate `hax_engine_codegen`.

The following files are generated:
 - `print_view.rs`: a shallow view of the AST defined in module `ast`. This view
   is suited for pretty-printing. For more details, you can read the `README` in
   `hax_engine_codegen` or the documention of the modules `generated_printer::print_view` and `generated_printer::print_context`.
 - `to_print_view.rs`: implements the trait `ToPrintView` for every type of the
   AST. For more details, you can read the `README` in `hax_engine_codegen` or
   the documention of the module `generated_printer::to_print_view`.
