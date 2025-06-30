//! Literal and numeric type kinds used in constant expressions.

use crate::symbol::Symbol;
use hax_rust_engine_macros::*;

/// Size of an integer type
#[derive_group_for_ast]
pub enum IntSize {
    /// 8 bits integer type
    S8,
    /// 16 bits integer type
    S16,
    /// 32 bits integer type
    S32,
    /// 64 bits integer type
    S64,
    /// 128 bits integer type
    S128,
    /// Pointer-sized integer type
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

/// Signedness of a numeric type
#[derive_group_for_ast]
pub enum Signedness {
    /// Signed type (`i32`, `i64`, ...)
    Signed,
    /// Unsigned type (`u32`, `u64`, ...)
    Unsigned,
}

/// Describes a Rust integer type (`u64`, `i32`, ...)
#[derive_group_for_ast]
pub struct IntKind {
    /// Size of this integer type
    pub size: IntSize,
    /// Whether this integer type is signed or unsigned
    pub signedness: Signedness,
}

/// Float types
#[derive_group_for_ast]
pub enum FloatKind {
    /// 16 bits float
    F16,
    /// 32 bits float
    F32,
    /// 64 bits float
    F64,
    /// 128 bits float
    F128,
}

/// Rust literal
#[derive_group_for_ast]
pub enum Literal {
    /// String literal
    String(Symbol),
    /// Character literal
    Char(char),
    /// Boolean literal
    Bool(bool),
    /// Integer literal
    Int {
        /// Value as u128
        value: Symbol,
        /// True if `-`
        negative: bool,
        /// Rust int type description (size + signedness)
        kind: IntKind,
    },
    /// Float literal
    Float {
        /// Value as a string
        value: Symbol,
        /// True if `-`
        negative: bool,
        /// Size
        kind: FloatKind,
    },
}
