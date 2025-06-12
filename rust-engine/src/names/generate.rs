use std::iter;

use crate::ast::identifiers::global_id::DefId;
use crate::ast::Item;
use hax_frontend_exporter::{DefKind, DisambiguatedDefPathItem};

use serde::de::DeserializeOwned;
use serde_json::Value;
use std::collections::HashMap;

/// Visit items and collect all the `DefId`s
fn collect_def_ids(items: Vec<Item>) -> Vec<DefId> {
    /// Recursively traverses a JSON tree and tries to parse any subnodes as type `T`.
    fn find<T: DeserializeOwned>(value: &Value) -> Vec<T> {
        let subvalues: Vec<_> = match &value {
            Value::Array(arr) => arr.iter().collect(),
            Value::Object(map) => map.iter().map(|(_, value)| value).collect(),
            _ => vec![],
        };

        subvalues
            .into_iter()
            .flat_map(find)
            .chain(serde_json::from_value(value.clone()).into_iter())
            .collect()
    }

    // TODO: we don't have visitor yet. For now, we use a hack: we just browse
    // the JSON, trying to parse every possible node as a DefId.
    let mut def_ids = find(&serde_json::to_value(items).unwrap());

    def_ids.sort();
    def_ids.dedup();

    def_ids
}

/// Computes a string path for a `DefId`.
fn path_of_def_id(id: &DefId) -> Vec<String> {
    fn name_to_string(mut s: String) -> String {
        if s == "_" {
            s = "_anonymous".into();
        };
        if s.parse::<i32>().is_ok() {
            s = format!("_{s}");
        }
        s
    }
    iter::once(id.krate.to_string())
        .chain(id.path.iter().map(|item| {
            let data = match item.data.clone() {
                hax_frontend_exporter::DefPathItem::CrateRoot { name } => name,
                hax_frontend_exporter::DefPathItem::TypeNs(Some(s))
                | hax_frontend_exporter::DefPathItem::ValueNs(s)
                | hax_frontend_exporter::DefPathItem::MacroNs(s)
                | hax_frontend_exporter::DefPathItem::LifetimeNs(s) => s,
                data => format!("{:?}", data),
            };
            if item.disambiguator == 0 {
                data
            } else {
                format!("{data}__{}", item.disambiguator)
            }
        }))
        .chain(if matches!(&id.kind, DefKind::Ctor { .. }) {
            Some("ctor".to_string())
        } else {
            None
        })
        .map(|s| name_to_string(s))
        .collect()
}

/// Given a list of `DefId`, this will create a Rust code source that provides those names.
fn generate_names_hierachy(def_ids: Vec<DefId>) -> String {
    /// Helper struct: a graph of module and definitions
    #[derive(Debug, Default)]
    struct Module {
        submodules: HashMap<String, Module>,
        definitions: Vec<(String, DefId)>,
    }

    impl Module {
        fn new(def_ids: Vec<DefId>) -> Self {
            let mut node = Self::default();
            for def_id in def_ids {
                node.insert(def_id);
            }
            node
        }
        fn insert(&mut self, def_id: DefId) {
            let fullpath = path_of_def_id(&def_id);
            let [modpath @ .., def] = &fullpath[..] else {
                return;
            };

            let mut node = self;
            for chunk in modpath {
                node = node.submodules.entry(chunk.clone()).or_default();
            }

            node.definitions.push((def.clone(), def_id.clone()));
        }
        fn render(self, level: usize) -> String {
            let Self {
                submodules,
                definitions,
            } = self;
            let submodules = submodules.into_iter().map(|(name, contents)| {
                format!("pub mod {name} {{ {} }}", contents.render(level + 1))
            });
            let definitions = definitions.into_iter().map(|(name, def_id)| {
                let _ = 0;
                let DefId {
                    krate,
                    path,
                    parent,
                    kind,
                } = def_id;
                let data: (String, Vec<DisambiguatedDefPathItem>, DefKind) = (krate, path, kind);
                let data = serde_json::to_string(&data).unwrap();
                let parent = if let Some(parent) = parent {
                    let parent = path_of_def_id(&parent);
                    let root = if level > 0 { "root::" } else { "" };
                    format!("Some({root}{}())", parent.join("::"))
                } else {
                    "None".to_string()
                };
                format!(r###"mk!({name}, r##"{data}"##, {parent});"###)
            });
            iter::once("use super::root::{self, prelude::*};".to_string())
                .chain(submodules)
                .chain(definitions)
                .collect::<Vec<_>>()
                .join("\n")
        }
    }
    Module::new(def_ids).render(0)
}

pub fn export_def_ids_to_name_module(items: Vec<Item>, path: String) {
    let contents = generate_names_hierachy(collect_def_ids(items));

    let contents = format!(
        r#"
    #[allow(unused)]
    #[allow(non_snake_case)]
    pub mod root {{
        macro_rules! mk {{
            ($name: ident, $data: literal, $parent: expr) => {{
                pub fn $name() -> hax_rust_engine::ast::global_id::DefId {{
                    use hax_rust_engine::ast::global_id::DefId;
                    pub use std::sync::LazyLock;
                    static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {{
                        let data = $data;
                        let (krate, path, kind) = serde_json::from_str(data).unwrap();
                        DefId {{
                            parent: ($parent).map(Box::new),
                            krate,
                            path,
                            kind,
                        }}
                    }});
                    (&*DEF_ID).clone()
                }}
            }};
        }}
        pub(crate) use mk;
        {contents}
    }}
    "#
    );

    std::fs::write(path, contents).expect("Unable to write file");
}
