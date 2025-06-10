mod visitors;

use std::{fs, path::Path};

use proc_macro2::Span;
use quote::quote;
use syn::{parse_file, parse_quote, visit_mut::VisitMut, File};

use crate::visitors::{
    ast_with_contextes::transform_ast_with_contextes, generate_to_print_view::GenerateBridges,
    utils::KeepStructsEnumsTyAliases,
};

fn write(file: &File, path: &str) {
    let formatted = prettyplease::unparse(file);
    let out_path = Path::new(path);
    fs::write(&out_path, formatted).expect(&format!("Failed to write `{}`", path));
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
    let enum_item = generate_enum("Node", &ast, false, false);
    ast.items.extend_from_slice(&enum_item.items);
    write(&ast, "src/generic_printer/generated/print_view.rs");
}

/// Generate the `node.rs` file
fn generate_node(ast: &File) {
    let mut file = generate_enum("Node", ast, false, true);
    file.items
        .extend_from_slice(&generate_enum("NodeRef", ast, true, false).items);
    write(&file, "src/ast/generated/node.rs");
}

/// Given `file` that contains a list of datatypes `T1`...`TN`, this will produce
/// an enum named `name` with variants `T1(T1)`, `T2(T2)`, ..., `TN(TN)`.
/// Also generate `From` instances lifiting `T1`..`TN` to the generated enum `name`.
///
/// This takes into account lifetimes and type parameters of `T1`...`TN`.
///
/// If `reference` is true, then the variants will hold references, e.g. be of the shape `T1(&'lt T1)`.
///
/// If `add_variant_unknown`, an extra node `Unknown(String)` is added. This is handy for diagnostics.
///
/// When `reference` is true but `add_variant_unknown` is false, the enum is `Copy`.
fn generate_enum(name: &str, file: &File, reference: bool, add_variant_unknown: bool) -> syn::File {
    let name = syn::Ident::new(name, Span::call_site());
    let datatypes: Vec<(&syn::Ident, &syn::Generics)> = file
        .items
        .iter()
        .filter_map(|item| match item {
            syn::Item::Struct(s) => Some((&s.ident, &s.generics)),
            syn::Item::Enum(s) => Some((&s.ident, &s.generics)),
            _ => None,
        })
        .collect();

    // Produce token streams accoding to `reference` and `add_variant_unknown`
    let copy_bound = (reference && !add_variant_unknown).then_some(quote! {Copy});
    let derive_name = if reference && !add_variant_unknown {
        quote! {derive_AST_base}
    } else {
        quote! {derive_AST}
    };
    let reference_generics = reference.then_some(parse_quote! {<'lt>});
    let reference_lt = &reference.then_some(quote! {&'lt});
    let add_variant_unknown = add_variant_unknown.then_some(quote! {Unknown(String)});

    let merged_generics = datatypes
        .iter()
        .map(|(_, g)| *g)
        .cloned()
        .chain(reference_generics.into_iter())
        .reduce(visitors::utils::merge_generics)
        .unwrap_or(parse_quote! {});

    let variants: Vec<_> = datatypes
        .iter()
        .map(|(ident, generics)| quote! {#ident(#reference_lt #ident #generics)})
        .collect();
    let into_instances: Vec<_> = datatypes
        .iter()
        .map(|(ident, generics)| {
            quote! {
                impl #merged_generics From<#reference_lt #ident #generics> for #name #merged_generics {
                    fn from(item: #reference_lt #ident #generics) -> Self {
                        Self::#ident(item)
                    }
                }
            }
        })
        .collect();

    parse_quote! {
        #(#into_instances)*
        #[derive(#copy_bound)]
        #[macro_rules_attribute::apply(#derive_name)]
        pub enum #name #merged_generics {
            #(#variants,)*
            #add_variant_unknown
        }
    }
}

fn main() {
    // Move to the main directory of the rust engine
    std::env::set_current_dir("..").unwrap();

    let mut ast = read("src/ast.rs");
    // Generate `node.rs`, for the regular AST
    generate_node(&ast);

    // Now we can add reguar nodes
    ast.items
        .extend_from_slice(&read("src/generic_printer/resugar.rs").items);

    KeepStructsEnumsTyAliases.visit_file_mut(&mut ast);

    // Drop file attributes (e.g. `//!` comments)
    ast.attrs = vec![];

    generate_print_view(ast.clone());
    generate_to_print_view(ast.clone());
}
