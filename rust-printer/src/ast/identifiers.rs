//! Identifier types used throughout the AST.
//!
//! This module defines:
//! - `GlobalId`: fully-qualified paths like `std::mem::drop`
//! - `LocalId`: local variable identifiers

use crate::symbol::Symbol;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::fmt;

mod global_id {
    use hax_frontend_exporter::{DefId, DefPathItem};
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};

    // TODO: this should be interned, so that it's copiable
    #[derive(
        Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
    )]
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
                    DefPathItem::TypeNs(Some(s))
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
        pub fn index() -> Self {
            Self::from_string("index")
        }
        pub fn tuple_field(field: usize) -> Self {
            Self::from_string(&format!("tuple_field_{field}"))
        }
        pub fn tuple_pat() -> Self {
            Self::from_string("tuple_pat")
        }
        pub fn box_new() -> Self {
            Self::from_string("Box::new")
        }
        pub fn bin_op(bin_op: &hax_frontend_exporter::BinOp) -> Self {
            Self::from_string(match bin_op {
                hax_frontend_exporter::BinOp::Add => "add",
                hax_frontend_exporter::BinOp::AddWithOverflow => "add_with_overflow",
                hax_frontend_exporter::BinOp::BitAnd => "bit_and",
                hax_frontend_exporter::BinOp::BitOr => "bit_or",
                hax_frontend_exporter::BinOp::BitXor => "bit_xor",
                hax_frontend_exporter::BinOp::Cmp => "cmp",
                hax_frontend_exporter::BinOp::Div => "div",
                hax_frontend_exporter::BinOp::Eq => "eq",
                hax_frontend_exporter::BinOp::Ge => "ge",
                hax_frontend_exporter::BinOp::Gt => "gt",
                hax_frontend_exporter::BinOp::Le => "le",
                hax_frontend_exporter::BinOp::Lt => "lt",
                hax_frontend_exporter::BinOp::Mul => "mul",
                hax_frontend_exporter::BinOp::MulWithOverflow => "mul_with_overflow",
                hax_frontend_exporter::BinOp::Ne => "ne",
                hax_frontend_exporter::BinOp::Offset => "offset",
                hax_frontend_exporter::BinOp::Rem => "rem",
                hax_frontend_exporter::BinOp::Shl => "shl",
                hax_frontend_exporter::BinOp::Shr => "shr",
                hax_frontend_exporter::BinOp::Sub => "sub",
                hax_frontend_exporter::BinOp::SubWithOverflow => "sub_with_overflow",
            })
        }
        pub fn un_op(un_op: &hax_frontend_exporter::UnOp) -> Self {
            Self::from_string(match un_op {
                hax_frontend_exporter::UnOp::Neg => "neg",
                hax_frontend_exporter::UnOp::Not => "not",
                _ => unimplemented!(),
            })
        }
        pub fn logical_op(logical_op: &hax_frontend_exporter::LogicalOp) -> Self {
            Self::from_string(match logical_op {
                hax_frontend_exporter::LogicalOp::And => "and",
                hax_frontend_exporter::LogicalOp::Or => "or",
            })
        }
        pub fn never_to_any() -> Self {
            Self::from_string("never_to_any")
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

#[derive(
    Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, JsonSchema, Serialize, Deserialize,
)]
pub struct LocalId(pub Symbol);

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
impl From<&hax_frontend_exporter::LocalIdent> for LocalId {
    fn from(value: &hax_frontend_exporter::LocalIdent) -> Self {
        Self(Symbol::new(&value.name))
    }
}
impl From<&str> for LocalId {
    fn from(name: &str) -> Self {
        Self(Symbol::new(name))
    }
}

pub use global_id::GlobalId;
