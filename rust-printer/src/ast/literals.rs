//! Literal and numeric type kinds used in constant expressions.

use super::derives::*;
use crate::symbol::Symbol;

#[apply(derive_AST)]
pub enum IntSize {
    S8,
    S16,
    S32,
    S64,
    S128,
    SSize,
}

use hax_frontend_exporter::{IntTy, UintTy};
impl From<IntTy> for IntSize {
    fn from(value: IntTy) -> Self {
        match value {
            IntTy::I128 => Self::S128,
            IntTy::I64 => Self::S64,
            IntTy::I32 => Self::S32,
            IntTy::I16 => Self::S16,
            IntTy::I8 => Self::S8,
            IntTy::Isize => Self::SSize,
        }
    }
}
impl From<UintTy> for IntSize {
    fn from(value: UintTy) -> Self {
        match value {
            UintTy::U128 => Self::S128,
            UintTy::U64 => Self::S64,
            UintTy::U32 => Self::S32,
            UintTy::U16 => Self::S16,
            UintTy::U8 => Self::S8,
            UintTy::Usize => Self::SSize,
        }
    }
}

#[apply(derive_AST)]
pub enum Signedness {
    Signed,
    Unsigned,
}

#[apply(derive_AST)]
pub struct IntKind {
    pub size: IntSize,
    pub signedness: Signedness,
}

#[apply(derive_AST)]
pub enum FloatKind {
    F16,
    F32,
    F64,
    F128,
}

#[apply(derive_AST)]
pub enum Literal {
    String(Symbol),
    Char(char),
    Bool(bool),
    Int {
        value: u128,
        negative: bool,
        kind: IntKind,
    },
    Float {
        value: Symbol,
        negative: bool,
        kind: FloatKind,
    },
}
