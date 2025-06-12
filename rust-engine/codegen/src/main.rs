mod generate_enum;
mod visitors;

use quote::{ToTokens, quote};
use std::{fs, path::Path};
use syn::{File, parse_file, visit_mut::VisitMut};

use crate::visitors::{
    ast_with_contextes::transform_ast_with_contextes, generate_to_print_view::GenerateBridges,
    utils::KeepStructsEnumsTyAliases,
};

fn write(file: &File, path: &str) {
    let out_path = Path::new(path);
    fs::write(&out_path, format!("{}", file.to_token_stream()))
        .expect(&format!("Failed to write `{}`", path));
    std::process::Command::new("rustfmt")
        .arg(&out_path)
        .status()
        .expect("failed to run rustfmt");
}
fn read(path: &str) -> File {
    let src_path = Path::new(path);
    let contents = fs::read_to_string(&src_path).expect(&format!("Failed to read `{}`", path));
    parse_file(&contents).expect(&format!("Failed to parse `{}` as a Rust file", path))
}

fn generate_to_print_view(mut ast: File) {
    GenerateBridges.visit_file_mut(&mut ast);
    write(&ast, "src/generic_printer/generated/to_print_view.rs")
}

fn generate_print_view(mut ast: File) {
    transform_ast_with_contextes(&mut ast);
    let fragment = (generate_enum::FragmentEnumGenerator {
        enum_name: "Fragment",
        file: &ast,
        owned: true,
        extra_variants: &quote! {},
        extra_attributes: &quote! {
            /// An owned fragment of the print view: this `enum` can represent any node in the AST.
            #[derive_group_for_ast]
        },
    })
    .to_file();
    ast.items.extend_from_slice(&fragment.items);
    write(&ast, "src/generic_printer/generated/print_view.rs");
}

/// Generate the `fragment.rs` file
fn generate_fragment(ast: &File) {
    let mut fragment = (generate_enum::FragmentEnumGenerator {
        enum_name: "Fragment",
        file: ast,
        owned: true,
        extra_variants: &quote! {
            Literal(Literal),
            /// Fallback node
            Unknown(String),
        },
        extra_attributes: &quote! {
            /// An owned fragment of the AST: this `enum` can represent any node in the AST.
            #[derive_group_for_ast]
        },
    })
    .to_file();
    let fragment_ref = (generate_enum::FragmentEnumGenerator {
        enum_name: "FragmentRef",
        file: ast,
        owned: false,
        extra_variants: &quote! {
            Literal(&'lt Literal),
        },
        extra_attributes: &quote! {
            /// An borrowed fragment of the AST: this `enum` can represent any node in the AST.
            #[derive_group_for_ast_base]
            #[derive(Copy)]
        },
    })
    .to_file();
    fragment.items.extend_from_slice(&fragment_ref.items);
    write(&fragment, "src/ast/generated/fragment.rs");
}

fn main() {
    // Move to the main directory of the rust engine
    std::env::set_current_dir("..").unwrap();

    let mut ast = read("src/ast.rs");
    // Generate `fragment.rs`, for the regular AST
    generate_fragment(&ast);

    // Now we can add the types for resugared AST fragments
    ast.items
        .extend_from_slice(&read("src/generic_printer/resugar.rs").items);

    KeepStructsEnumsTyAliases.visit_file_mut(&mut ast);

    // Drop file attributes (e.g. `//!` comments)
    ast.attrs = vec![];

    generate_print_view(ast.clone());
    generate_to_print_view(ast.clone());
}
