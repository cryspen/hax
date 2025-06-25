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
//!
//! As an example, the names `std::option::Option::Some` and `None` will be provided by this module as:
//! ```rust
//! mod std {
//!     mod option {
//!         mod Option {
//!             fn Some() -> DefId { ... }
//!             fn None() -> DefId { ... }
//!         }
//!     }
//! }
//! ```

/// Helper module that provides serialization and deserialization of DefId to
/// compact representations. This is solely for conciseness purposes of the
/// generated code.
pub(self) mod serialization_helpers {
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

/// We allow:
///  - `unused`: we don't use all the names present in the `engine/names` crate.
///    Filtering which `DefId` should be exposed would be complicated, and
///    dependent library may use some names. (for instance, the backend for
///    ProVerif may use names from `hax_lib_protocol` that are not needed
///    anywhere else in the engine)
///  - `non_snake_case`: we produce faithful names with respect to their
///    original definitions in Rust. We generate for instance `fn Some() ->
///    DefID {...}` that provides the `DefId` for the
///    `std::option::Option::Some`. We want the function to be named `Some`
///    here, not `some`.
///  - `broken_intra_doc_links`: we produce documentation that link the function
///    providing the `DefId` of a item to the item itself. Sometimes, we refer
///    to private items, to re-exported items or to items that are not in the
///    dependency closure of the engine: in such cases, `rustdoc` cannot link
///    properly.
#[allow(unused, non_snake_case, rustdoc::broken_intra_doc_links, missing_docs)]
pub mod root {
    macro_rules! mk {
        ($name: ident, $doc: literal, $data: literal, $parent: expr) => {
            #[doc = $doc]
            pub fn $name() -> crate::ast::identifiers::global_id::DefId {
                use crate::ast::identifiers::global_id::DefId;
                use std::sync::LazyLock;
                static DEF_ID: LazyLock<DefId> = LazyLock::new(|| {
                    let data = $data;
                    root::serialization_helpers::deserialize(data, $parent)
                });
                (&*DEF_ID).clone()
            }
        };
    }
    pub(self) use super::serialization_helpers;
    pub(self) use mk;
    include!("names/generated.rs");
}
pub use root::*;

/// Global identifiers are built around `DefId` that comes out of the hax
/// frontend. We use the Rust engine itself to produce the names: we run hax on
/// the `engine/names` crate, we extract identifiers from the resulting AST, and
/// we expose them back as Rust functions here.
pub mod codegen {
    use itertools::*;
    use std::iter;

    use crate::ast::Item;
    use crate::{ast::identifiers::global_id::DefId, names::serialization_helpers};
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

    /// Crafts a docstring for a `DefId`, hopefully (rustdoc) linking it back to
    /// its origin.
    fn docstring(id: &DefId) -> String {
        let path = path_of_def_id(id);
        let (parent_path, def) = match &path[..] {
            [init @ .., last] => (init, last.clone()),
            _ => (&[] as &[_], id.krate.to_string()),
        };
        let parent_path_str = format!("::{}", parent_path.join("::"));
        let path_str = format!("::{}", path_of_def_id(id).join("::"));
        let subject = match &id.kind {
            DefKind::Mod => format!("module [`{}`]", path_str),
            DefKind::Struct => format!("struct [`{}`]", path_str),
            DefKind::Union => format!("union [`{}`]", path_str),
            DefKind::Enum => format!("enum [`{}`]", path_str),
            DefKind::Variant => format!("variant [`{}`]", path_str),
            DefKind::Trait => format!("trait [`{}`]", path_str),
            DefKind::TyAlias => format!("type alias [`{}`]", path_str),
            DefKind::ForeignTy => format!("foreign type [`{}`]", path_str),
            DefKind::TraitAlias => format!("trait alias [`{}`]", path_str),
            DefKind::AssocTy => format!("associated type [`{}`]", path_str),
            DefKind::TyParam => format!("type parameter from [`{}`]", parent_path_str),
            DefKind::Fn => format!("function [`{}`]", path_str),
            DefKind::Const => format!("const [`{}`]", path_str),
            DefKind::ConstParam => format!("const parameter from [`{}`]", parent_path_str),
            DefKind::Static { .. } => format!("static [`{}`]", path_str),
            DefKind::Ctor { .. } => format!("constructor for [`{}`]", parent_path_str),
            DefKind::AssocFn => format!("associated function [`{}`]", path_str),
            DefKind::AssocConst => format!("associated constant [`{}`]", path_str),
            DefKind::Macro { .. } => format!("macro [`{}`]", path_str),
            DefKind::ExternCrate => format!("extern crate [`{}`]", path_str),
            DefKind::Use => format!("use item [`{}`]", path_str),
            DefKind::ForeignMod => format!("foreign module [`{}`]", path_str),
            DefKind::AnonConst => return format!("This is an anonymous constant."),
            DefKind::PromotedConst | DefKind::InlineConst => {
                format!("This is an inline const from [`{}`]", parent_path_str)
            }
            DefKind::OpaqueTy => {
                return format!("This is an opaque type for [`{}`]", parent_path_str)
            }
            DefKind::Field => format!("field [`{}`] from {}", def, parent_path_str),
            DefKind::LifetimeParam => return format!("This is a lifetime parameter."),
            DefKind::GlobalAsm => return format!("This is a global ASM block."),
            DefKind::Impl { .. } => return format!("This is a impl block."),
            DefKind::Closure => return format!("This is a closure."),
            DefKind::SyntheticCoroutineBody => return format!("This is a coroutine body."),
        };
        format!("This is the {subject}.")
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
                    hax_frontend_exporter::DefPathItem::TypeNs(s)
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
    ///
    /// For example, given `krate::module::f` and `krate::g`, this will produce something like:
    /// ```rust,ignore
    /// mod krate {
    ///    mod module {
    ///       fn f() -> DefId {...}
    ///    }
    ///    fn g() -> DefId {...}
    /// }
    /// ```
    fn generate_names_hierachy(def_ids: Vec<DefId>) -> String {
        /// Helper struct: a graph of module and definitions.
        #[derive(Debug, Default)]
        struct Module {
            attached_def_id: Option<DefId>,
            submodules: HashMap<String, Module>,
            definitions: Vec<(String, DefId)>,
        }
        impl Module {
            fn new(def_ids: Vec<DefId>) -> Self {
                let mut node = Self::default();
                for def_id in &def_ids {
                    node.insert(def_id);
                }
                for def_id in def_ids {
                    let modpath = path_of_def_id(&def_id);
                    if let Some(module) = node.find_module(&modpath) {
                        module.attached_def_id = Some(def_id.clone());
                    }
                }
                node
            }
            /// Insert a `DefId` in our module tree
            fn insert(&mut self, def_id: &DefId) {
                let fullpath = path_of_def_id(def_id);
                let [modpath @ .., def] = &fullpath[..] else {
                    return;
                };

                let mut node = self;
                for chunk in modpath {
                    node = node.submodules.entry(chunk.clone()).or_default();
                }

                node.definitions.push((def.clone(), def_id.clone()));
            }
            /// Get a mutable borrow to the submodule denoted by `modpath`, if it exists
            fn find_module(&mut self, modpath: &Vec<String>) -> Option<&mut Self> {
                let mut node = self;
                for chunk in modpath {
                    node = node.submodules.get_mut(chunk)?;
                }
                Some(node)
            }
            /// Render the module tree as a string
            fn render(self, level: usize) -> String {
                let Self {
                    submodules,
                    definitions,
                    attached_def_id,
                } = self;
                let submodules = submodules
                    .into_iter()
                    .sorted_by(|(a, _), (b, _)| a.cmp(b))
                    .map(|(name, contents)| {
                        format!(r###"pub mod {name} {{ {} }}"###, contents.render(level + 1))
                    });
                let definitions = definitions
                    .into_iter()
                    .sorted_by(|(a, _), (b, _)| a.cmp(b))
                    .map(|(name, def_id)| {
                        let data = serialization_helpers::serialize(&def_id);
                        let docstring = docstring(&def_id);
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
                        format!(r###"mk!({name}, r##"{docstring}"##, r##"{data}"##, {parent});"###)
                    });
                let docstring = attached_def_id
                    .iter()
                    .map(docstring)
                    .map(|s| format!(r###"#![doc=r##"{s}"##]"###));
                docstring
                    .chain(iter::once("pub use super::root;".to_string()))
                    .chain(submodules)
                    .chain(definitions)
                    .collect::<Vec<_>>()
                    .join("\n")
            }
        }
        Module::new(def_ids).render(0)
    }

    /// Finds all `DefId`s in `items`, and produce a Rust module exposing them.
    pub fn export_def_ids_to_mod(items: Vec<Item>) -> String {
        generate_names_hierachy(collect_def_ids(items))
    }
}
