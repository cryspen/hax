use crate::prelude::*;

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantInt {
    Int(
        #[serde(with = "serialize_int::signed")]
        #[schemars(with = "String")]
        i128,
        IntTy,
    ),
    Uint(
        #[serde(with = "serialize_int::unsigned")]
        #[schemars(with = "String")]
        u128,
        UintTy,
    ),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantLiteral {
    Bool(bool),
    Char(char),
    Float(String, FloatTy),
    Int(ConstantInt),
    PtrNoProvenance(u128),
    Str(String),
    ByteStr(Vec<u8>),
}

/// The subset of [Expr] that corresponds to constants.
#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ConstantExprKind {
    Literal(ConstantLiteral),
    // Adts (structs, enums, unions) or closures.
    Adt {
        info: VariantInformations,
        fields: Vec<ConstantFieldExpr>,
    },
    Array {
        fields: Vec<ConstantExpr>,
    },
    Tuple {
        fields: Vec<ConstantExpr>,
    },
    /// A top-level constant or a constant appearing in an impl block.
    ///
    /// Remark: constants *can* have generic parameters.
    /// Example:
    /// ```text
    /// struct V<const N: usize, T> {
    ///   x: [T; N],
    /// }
    ///
    /// impl<const N: usize, T> V<N, T> {
    ///   const LEN: usize = N; // This has generics <N, T>
    /// }
    /// ```
    ///
    /// If `options.inline_anon_consts` is `false`, this is also used for inline const blocks and
    /// advanced const generics expressions.
    GlobalName(ItemRef),
    /// A trait constant
    ///
    /// Ex.:
    /// ```text
    /// impl Foo for Bar {
    ///   const C : usize = 32; // <-
    /// }
    /// ```
    TraitConst {
        impl_expr: ImplExpr,
        name: String,
    },
    /// A shared reference to a static variable.
    Borrow(ConstantExpr),
    /// A raw borrow (`*const` or `*mut`).
    RawBorrow {
        mutability: Mutability,
        arg: ConstantExpr,
    },
    /// A cast `<source> as <type>`, `<type>` is stored as the type of
    /// the current constant expression. Currently, this is only used
    /// to represent `lit as *mut T` or `lit as *const T`, where `lit`
    /// is a `usize` literal.
    Cast {
        source: ConstantExpr,
    },
    ConstRef {
        id: ParamConst,
    },
    FnPtr(ItemRef),
    /// A blob of memory containing the byte representation of the value. This can occur when
    /// evaluating MIR constants. Interpreting this back to a structured value is left as an
    /// exercice to the consumer.
    Memory(Vec<u8>),
    Todo(String),
}

#[derive_group(Serializers)]
#[derive(Clone, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct ConstantFieldExpr {
    pub field: DefId,
    pub value: ConstantExpr,
}

/// Rustc has different representation for constants: one for MIR
/// ([`rustc_middle::mir::Const`]), one for the type system
/// ([`rustc_middle::ty::ConstKind`]). For simplicity hax maps those
/// two construct to one same `ConstantExpr` type.
pub type ConstantExpr = Decorated<ConstantExprKind>;

// For ConstantKind we merge all the cases (Ty, Val, Unevaluated) into one
pub type ConstantKind = ConstantExpr;

#[cfg(feature = "rustc")]
impl From<ConstantFieldExpr> for FieldExpr {
    fn from(c: ConstantFieldExpr) -> FieldExpr {
        FieldExpr {
            value: c.value.into(),
            field: c.field,
        }
    }
}

#[cfg(feature = "rustc")]
impl From<ConstantExpr> for Expr {
    fn from(c: ConstantExpr) -> Expr {
        use ConstantExprKind::*;
        let kind = match *c.contents {
            Literal(lit) => {
                use ConstantLiteral::*;
                let mut neg = false;
                let node = match lit {
                    Bool(b) => LitKind::Bool(b),
                    Char(c) => LitKind::Char(c),
                    Int(i) => {
                        use LitIntType::*;
                        match i {
                            ConstantInt::Uint(v, t) => LitKind::Int(v, Unsigned(t)),
                            ConstantInt::Int(v, t) => {
                                neg = v.is_negative();
                                LitKind::Int(v.abs_diff(0), Signed(t))
                            }
                        }
                    }
                    Float(f, ty) => LitKind::Float(f, LitFloatType::Suffixed(ty)),
                    PtrNoProvenance(p) => LitKind::Int(p, LitIntType::Unsigned(UintTy::Usize)),
                    ByteStr(raw) => LitKind::ByteStr(raw, StrStyle::Cooked),
                    Str(raw) => LitKind::Str(raw, StrStyle::Cooked),
                };
                let span = c.span.clone();
                let lit = Spanned { span, node };
                ExprKind::Literal { lit, neg }
            }
            Adt { info, fields } => ExprKind::Adt(AdtExpr {
                info,
                fields: fields.into_iter().map(|field| field.into()).collect(),
                base: AdtExprBase::None,
                user_ty: None,
            }),
            GlobalName(item) => ExprKind::GlobalName {
                item,
                constructor: None,
            },
            Borrow(e) => ExprKind::Borrow {
                borrow_kind: BorrowKind::Shared,
                arg: e.into(),
            },
            RawBorrow { mutability, arg } => ExprKind::RawBorrow {
                mutability,
                arg: arg.into(),
            },
            ConstRef { id } => ExprKind::ConstRef { id },
            Array { fields } => ExprKind::Array {
                fields: fields.into_iter().map(|field| field.into()).collect(),
            },
            Tuple { fields } => ExprKind::Tuple {
                fields: fields.into_iter().map(|field| field.into()).collect(),
            },
            Cast { source } => ExprKind::Cast {
                source: source.into(),
            },
            kind @ (FnPtr { .. } | TraitConst { .. } | Memory { .. }) => {
                ExprKind::Todo(format!("Unsupported constant kind. kind={:#?}", kind))
            }
            Todo(msg) => ExprKind::Todo(msg),
        };
        Decorated {
            contents: Box::new(kind),
            ..c
        }
    }
}

#[cfg(feature = "rustc")]
pub use self::uneval::*;
#[cfg(feature = "rustc")]
mod uneval;
