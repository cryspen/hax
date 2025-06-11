//! Identifier types used throughout the AST.
//!
//! This module defines:
//! - `GlobalId`: fully-qualified paths like `std::mem::drop`
//! - `LocalId`: local variable identifiers

// TODO: Revisit once we stop relying on the OCaml importer.

use crate::symbol::Symbol;
use hax_rust_engine_macros::*;
use std::fmt;

mod global_id {
    use hax_frontend_exporter::{DefKind, DisambiguatedDefPathItem};

    #[derive_group_for_ast]
    pub struct DefId {
        pub krate: String,
        pub path: Vec<DisambiguatedDefPathItem>,
        pub parent: Option<Box<DefId>>,
        /// The kind of definition this `DefId` points to.
        pub kind: DefKind,
    }

    use hax_rust_engine_macros::*;

    #[derive_group_for_ast]
    struct ExplicitDefId {
        is_constructor: bool,
        def_id: DefId,
    }

    #[derive_group_for_ast]
    struct FreshModule {
        id: usize,
        hints: Vec<ExplicitDefId>,
        label: String,
    }

    #[derive_group_for_ast]
    enum ReservedSuffix {
        Pre,
        Post,
        Cast,
    }
    #[derive_group_for_ast]
    pub struct ConcreteId {
        def_id: ExplicitDefId,
        moved: Option<FreshModule>,
        suffix: Option<ReservedSuffix>,
    }

    #[derive_group_for_ast]
    pub enum GlobalId {
        Concrete(ConcreteId),
        Projector(ConcreteId),
    }

    impl From<hax_frontend_exporter::DefId> for GlobalId {
        fn from(_rust_def_id: hax_frontend_exporter::DefId) -> Self {
            todo!()
        }
    }

    impl GlobalId {
        // TODO: drop me
        fn from_string(_name: &str) -> Self {
            todo!()
        }
        // TODO: drop me
        pub fn to_string(&self) -> String {
            todo!()
        }
        pub fn name(&self) -> String {
            todo!()
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
}

#[derive_group_for_ast]
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
