//! Copies of the types related to attributes.
//! Such types are mostly contained in the crate `rustc_hir::attrs`.

use crate::prelude::*;

/// Reflects [`rustc_hir::attrs::AttributeKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::attrs::AttributeKind, state: S as tcx)]
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum AttributeKind {
    Align {
        align: Align,
        span: Span,
    },
    AutomaticallyDerived(Span),
    Deprecation {
        deprecation: Deprecation,
        span: Span,
    },
    DocComment {
        style: AttrStyle,
        kind: CommentKind,
        span: Span,
        comment: Symbol,
    },
    Ignore {
        span: Span,
        reason: Option<Symbol>,
    },
    Marker(Span),
    MayDangle(Span),
    MustUse {
        span: Span,
        reason: Option<Symbol>,
    },
    Path(Symbol, Span),
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_hir::attrs::Deprecation`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_hir::attrs::Deprecation, state: S as _s)]
pub struct Deprecation {
    pub since: DeprecatedSince,
    pub note: Option<Symbol>,
    pub suggestion: Option<Symbol>,
}

/// Reflects [`rustc_hir::attrs::DeprecatedSince`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_hir::attrs::DeprecatedSince, state: S as _s)]
pub enum DeprecatedSince {
    RustcVersion(RustcVersion),
    Future,
    NonStandard(Symbol),
    Unspecified,
    Err,
}

/// Reflects [`rustc_hir::RustcVersion`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S>, from: rustc_hir::RustcVersion, state: S as _s)]
pub struct RustcVersion {
    pub major: u16,
    pub minor: u16,
    pub patch: u16,
}

/// Reflects [`rustc_hir::attrs::InlineAttr`]
#[derive_group(Serializers)]
#[derive(AdtInto, Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::attrs::InlineAttr, state: S as _s)]
pub enum InlineAttr {
    None,
    Hint,
    Always,
    Never,
    Force {
        attr_span: Span,
        reason: Option<Symbol>,
    },
}
