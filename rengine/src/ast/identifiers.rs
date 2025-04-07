//! This module contains all the identifiers used in hax

use crate::symbol::Symbol;

mod global_id {
    use hax_frontend_exporter::{DefId, DefPathItem};

    // TODO: this should be interned
    #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
    pub struct GlobalId {
        name: String,
        // rust_def_id: hax_frontend_exporter::DefIdContents,
        // moved_to_module: Option<FreshModule>,
        // overlay: Option<ConcreteSuffix>,
    }
    impl From<DefId> for GlobalId {
        fn from(rust_def_id: DefId) -> Self {
            use std::ops::Deref;
            let def_id = rust_def_id.deref();
            let mut chunks = vec![def_id.krate.as_str()];
            for chunk in &def_id.path {
                let chunk = match &chunk.data {
                    DefPathItem::TypeNs(s)
                    | DefPathItem::ValueNs(s)
                    | DefPathItem::MacroNs(s)
                    | DefPathItem::LifetimeNs(s) => s.as_str(),
                    _ => "<unk>",
                };
                chunks.push(chunk);
            }
            Self {
                name: chunks.join("::"),
            }
        }
    }

    impl GlobalId {
        // TODO: drop me
        fn from_string(name: &str) -> Self {
            Self {
                name: name.to_string(),
            }
        }
        // TODO: drop me
        pub fn to_string(&self) -> String {
            self.name.to_string()
        }
        pub fn name(&self) -> String {
            self.name.split("::").last().unwrap().to_string()
        }
    }

    // TODO: should be consts
    impl GlobalId {
        pub fn slice() -> Self {
            Self::from_string("Slice")
        }
        pub fn array() -> Self {
            Self::from_string("Array")
        }
    }

    // #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
    // pub enum ConcreteSuffix {
    //     Cast,
    //     Precondition,
    //     Postcondition,
    // }

    // /// TODO: implement
    // #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
    // struct FreshModule;
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct LocalIdent(pub Symbol);

impl ToString for LocalIdent {
    fn to_string(&self) -> String {
        self.0.to_string()
    }
}

impl From<&hax_frontend_exporter::LocalIdent> for LocalIdent {
    fn from(value: &hax_frontend_exporter::LocalIdent) -> Self {
        Self(Symbol::new(&value.name))
    }
}

pub use global_id::GlobalId;
