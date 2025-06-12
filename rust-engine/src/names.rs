//! This module provides a list of handy `DefId` for the engine.
//!
//! For example, to be able to resugar `std::ops::Add::add(x, y)` into `x + y`,
//! we need to:
//!  1. match on the expression `std::ops::Add::add(x, y)`, figure out it is the
//!     application of the function denoted by the global identifier
//!     `std::ops::Add::add` with arguments `x` and `y`.
//!  2. check that global identifier `id: GlobalId` `std::ops::Add::add` is
//!     indeed `std::ops::Add::add`.
//!
//! Point (2.) seems a bit totological, but we need to write a comparison like
//! `x == the_function_add`. This module basically provides such
//! `the_function_add` symbols.
pub(self) mod helpers {
    use hax_frontend_exporter::{DefKind, DefPathItem, DisambiguatedDefPathItem};

    use crate::ast::identifiers::global_id::DefId;
    type Repr = (String, Vec<(DefPathItem, u32)>, DefKind);
    type BorrowedRepr<'a> = (&'a String, Vec<(&'a DefPathItem, &'a u32)>, &'a DefKind);

    pub fn serialize(did: &DefId) -> String {
        let path = did
            .path
            .iter()
            .map(
                |DisambiguatedDefPathItem {
                     data,
                     disambiguator,
                 }| (data, disambiguator),
            )
            .collect::<Vec<_>>();
        let data: BorrowedRepr<'_> = (&did.krate, path, &did.kind);
        serde_json::to_string(&data).unwrap()
    }
    pub fn deserialize(s: &str, parent: Option<DefId>) -> DefId {
        let (krate, path, kind): Repr = serde_json::from_str(s).unwrap();
        DefId {
            parent: parent.map(Box::new),
            krate,
            path: path
                .into_iter()
                .map(|(data, disambiguator)| DisambiguatedDefPathItem {
                    data,
                    disambiguator,
                })
                .collect(),
            kind,
        }
    }
}

#[allow(unused)]
#[allow(non_snake_case)]
pub mod root {
    macro_rules! mk {
        ($name: ident, $data: literal, $parent: expr) => {
            pub fn $name() -> crate::ast::global_id::DefId {
                use crate::ast::global_id::DefId;
                pub use std::sync::LazyLock;
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = $data;
                    root::helpers::deserialize(data, $parent)
                });
                (&*DEF_ID).clone()
            }
        };
    }
    pub(self) use super::helpers;
    pub(self) use mk;
    include!("generated/names.rs");
}

/// Global identifiers are built around `DefId` that comes out of the hax
/// frontend. We use the Rust engine itself to produce the names: we run hax on
/// the `engine/names` crate, we extract identifiers from the resulting AST, and
/// we expose them back as Rust functions here.
pub mod codegen {
    use itertools::*;
    use std::iter;

    use crate::ast::Item;
    use crate::{ast::identifiers::global_id::DefId, names::helpers};
    use hax_frontend_exporter::DefKind;

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
                let submodules = submodules
                    .into_iter()
                    .sorted_by(|(a, _), (b, _)| a.cmp(b))
                    .map(|(name, contents)| {
                        format!("pub mod {name} {{ {} }}", contents.render(level + 1))
                    });
                let definitions = definitions
                    .into_iter()
                    .sorted_by(|(a, _), (b, _)| a.cmp(b))
                    .map(|(name, def_id)| {
                        let data = helpers::serialize(&def_id);
                        let parent = if let Some(parent) = def_id.parent {
                            let parent = path_of_def_id(&parent);
                            let root = if level > 0 { "root::" } else { "" };
                            format!(
                                "::core::option::Option::Some({root}{}())",
                                parent.join("::")
                            )
                        } else {
                            "::core::option::Option::None".to_string()
                        };
                        format!(r###"mk!({name}, r##"{data}"##, {parent});"###)
                    });
                iter::once("pub use super::root;".to_string())
                    .chain(submodules)
                    .chain(definitions)
                    .collect::<Vec<_>>()
                    .join("\n")
            }
        }
        Module::new(def_ids).render(0)
    }

    pub fn export_def_ids_to_mod(items: Vec<Item>) -> String {
        generate_names_hierachy(collect_def_ids(items))
    }
}
