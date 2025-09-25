# Toolchain structure

Hax is composed of three main parts:

* The frontend, which interfaces with rustc to extract Rust intermediary representation ASTs (for MIR or THIR) out of Rust code.
* The engine, which imports the Rust THIR AST to the internal hax AST, and defines a set of transformation phases on this internal AST.
* The backends, which make use of a set of phases from the engine, and print it to a target verification framework or language. A backend also usually needs to provide a proof library and some more utilities.
