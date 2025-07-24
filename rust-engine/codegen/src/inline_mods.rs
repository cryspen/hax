use std::{
    fs,
    path::{Path, PathBuf},
};
use syn::{
    File, ItemMod, parse_file,
    visit_mut::{self, VisitMut},
};

/// A visitor which replaces `mod name;` with `mod name { /* contents of file… */ }`.
pub struct ModuleInliner {
    /// Directory against which to resolve `mod name;`
    base_dir: PathBuf,
}

impl ModuleInliner {
    /// Create a new inliner rooted at `base_dir`.
    pub fn new(base_dir: impl Into<PathBuf>) -> Self {
        ModuleInliner {
            base_dir: base_dir.into(),
        }
    }

    /// Given a module declaration `mod foo;`, find and read the corresponding file.
    fn read_mod_file(&self, name: &str) -> Option<(PathBuf, String)> {
        // Try foo.rs
        let mut file: PathBuf = self.base_dir.join(format!("{}.rs", name));
        if file.is_file() {
            return fs::read_to_string(&file).ok().map(|src| (file, src));
        }
        // Try foo/mod.rs
        file = self.base_dir.join(name).join("mod.rs");
        if file.is_file() {
            return fs::read_to_string(&file).ok().map(|src| (file, src));
        }
        None
    }
}

impl VisitMut for ModuleInliner {
    fn visit_item_mod_mut(&mut self, node: &mut ItemMod) {
        // Only handle extern declarations: `mod foo;`
        let mod_name = node.ident.to_string();
        if node.content.is_none() {
            if let Some((mod_path, src)) = self.read_mod_file(&mod_name) {
                println!("Load module {:?}", mod_path);
                // Parse that module's file
                let mut module_file: File = parse_file(&src)
                    .unwrap_or_else(|e| panic!("failed to parse {}: {}", mod_path.display(), e));

                // Recurse into it with a new base_dir (its parent directory)
                let parent = mod_path.parent().unwrap_or(Path::new(".")).to_path_buf();
                let mut sub_inliner = ModuleInliner::new(parent);
                sub_inliner.visit_file_mut(&mut module_file);

                // Replace `mod foo;` with `mod foo { /*…items…*/ }`
                node.content = Some((syn::token::Brace::default(), module_file.items));
                node.semi = None;
            }
        }

        self.base_dir.push(node.ident.to_string());
        // Continue walking into any inlined content
        visit_mut::visit_item_mod_mut(self, node);
        self.base_dir.pop();
    }
}
