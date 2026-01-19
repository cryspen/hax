//! This `build.rs` script:
//! 1. collects all the `*.rs` Rust module under `src`
//! 2. for each Rust module, we build a mod-level graph
//! 3. for each Rust module that has no parent
//!    (i.e. no `mod the_module` in any other Rust file),
//!    we add a `#[path="<path>"]mod <name>` to `src/generated.rs`.
//!
//! The file `src/generated.rs` is included in `lib.rs`.

use anyhow::{Context, Result};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use syn::{Attribute, Item, Lit, Meta};
use walkdir::WalkDir;

/// Builds a graph of parent-child module relationships from a directory of .rs files.
///
/// The graph is a HashMap where the key is the parent module's file path,
/// and the value is a vector of its direct children modules' file paths.
fn build_module_graph(root_dir: &Path) -> Result<HashMap<PathBuf, Vec<PathBuf>>> {
    let all_files: HashSet<PathBuf> = WalkDir::new(root_dir)
        .into_iter()
        .filter_map(Result::ok)
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "rs"))
        .filter_map(|e| e.path().canonicalize().ok())
        .collect();

    if all_files.is_empty() {
        println!("Warning: No '*.rs' files found in the specified directory.");
        return Ok(HashMap::new());
    }

    let mut module_graph: HashMap<PathBuf, Vec<PathBuf>> = HashMap::new();

    for parent_path in &all_files {
        let content = fs::read_to_string(parent_path)
            .with_context(|| format!("Failed to read file: {:?}", parent_path))?;

        let ast = syn::parse_file(&content)
            .with_context(|| format!("Failed to parse Rust code in: {:?}", parent_path))?;

        for item in &ast.items {
            if let Item::Mod(item_mod) = item {
                // We only care about `mod name;` declarations, not `mod name { ... }`
                if item_mod.content.is_none() {
                    let mod_name = item_mod.ident.to_string();
                    let maybe_child_path =
                        resolve_module_path(parent_path, mod_name, &item_mod.attrs, &all_files);

                    if let Some(child_path) = maybe_child_path {
                        // Add the parent-child relationship to the graph
                        module_graph
                            .entry(parent_path.clone())
                            .or_default()
                            .push(child_path);
                    }
                }
            }
        }
    }

    for file_path in &all_files {
        module_graph.entry(file_path.clone()).or_default();
    }

    Ok(module_graph)
}

/// Resolves the path to a submodule based on its declaration.
fn resolve_module_path(
    parent_path: &Path,
    mod_name: String,
    attrs: &[Attribute],
    all_files: &HashSet<PathBuf>,
) -> Option<PathBuf> {
    let parent_dir = parent_path.parent()?;

    // Check for `#[path = "..."]` attribute
    for attr in attrs {
        if !attr.path().is_ident("path") {
            continue;
        }

        if let Meta::NameValue(meta) = attr.meta.clone() {
            if let syn::Expr::Lit(expr_lit) = &meta.value {
                if let Lit::Str(lit_str) = &expr_lit.lit {
                    let explicit_path = parent_dir.join(lit_str.value());
                    if let Ok(canon_path) = explicit_path.canonicalize() {
                        if all_files.contains(&canon_path) {
                            return Some(canon_path);
                        }
                    }
                }
            }
        }

        // We found a #[path = ...] attribute but did not resolve a module file.
        return None;
    }

    // Default Rust module resolution rules if no `#[path]` is found
    // 1. Check for `mod_name.rs`
    let path1 = parent_dir.join(format!("{}.rs", mod_name));
    if let Ok(canon_path) = path1.canonicalize() {
        if all_files.contains(&canon_path) {
            return Some(canon_path);
        }
    }

    // 2. Check for `mod_name/mod.rs`
    let path2 = parent_dir.join(&mod_name).join("mod.rs");
    if let Ok(canon_path) = path2.canonicalize() {
        if all_files.contains(&canon_path) {
            return Some(canon_path);
        }
    }

    None
}

fn main() -> Result<()> {
    // return Ok(());
    println!("cargo:rerun-if-changed=src");
    println!("cargo:rerun-if-changed=build.rs");

    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR")?);
    let src_dir = manifest_dir
        .join("src")
        .canonicalize()
        .with_context(|| "Failed to canonicalize src directory".to_string())?;
    let generated_path = src_dir.join("generated.rs");
    fs::write(&generated_path, "")?;

    let graph = build_module_graph(&src_dir)?;

    let mut child_modules: HashSet<PathBuf> = HashSet::new();
    for children in graph.values() {
        for child in children {
            child_modules.insert(child.clone());
        }
    }

    let mut module_decls: Vec<(String, String)> = Vec::new();

    for module_path in graph.keys() {
        if child_modules.contains(module_path) {
            continue;
        }

        if !module_path.starts_with(&src_dir) {
            continue;
        }

        let relative = module_path
            .strip_prefix(&src_dir)
            .with_context(|| format!("Failed to derive relative path for {:?}", module_path))?;

        if relative.parent().is_none() {
            continue;
        }

        let relative_str = forward_slashes(relative);
        let ident = path_to_ident(relative);
        module_decls.push((relative_str, ident));
    }

    module_decls.sort();

    let mut output = String::new();
    for (relative, ident) in module_decls {
        if ident == "lib" || ident == "generated" {
            continue;
        }
        output.push_str(&format!("#[path = \"{}\"] mod {};\n", relative, ident));
    }

    fs::write(&generated_path, output)
        .with_context(|| format!("Failed to write generated modules to {:?}", generated_path))?;

    Ok(())
}

fn forward_slashes(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

fn path_to_ident(rel_path: &Path) -> String {
    rel_path
        .with_extension("")
        .to_string_lossy()
        .into_owned()
        .replace('\\', "/")
        .replace('/', "__")
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}
