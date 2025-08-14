use std::mem;

use super::*;
use crate::ast::{identifiers::*, literals::*, resugared::*, visitors::AstVisitorMut, *};
use crate::symbol::*;

pub struct Parens<P: Precedences> {
    precedence_level: PrecedenceLevel,
    printer: P,
}

impl<P: Precedences> Parens<P> {
    fn with_precedence<T>(
        &mut self,
        precedence_level: PrecedenceLevel,
        mut action: impl FnMut(&mut Self) -> T,
    ) -> T {
        let previous = self.precedence_level;
        self.precedence_level = precedence_level;
        let result = action(self);
        self.precedence_level = previous;
        result
    }
}

impl<P: Precedences> AstVisitorMut for Parens<P> {
    fn exit_expr(&mut self, e: &mut Expr) {
        if self.precedence_for_expr_kind(&e.kind) > self.precedence_level {
            *e.kind = ExprKind::Resugared(ResugaredExprKind::Delimiter(e.clone()));
        };
    }
    fn visit_expr_kind(&mut self, x: &mut ExprKind) {
        self.visit_expr_kind_with_precedence(x);
    }
}

macro_rules! mk {
    (enum $name:ident {
        $(
          $variant:ident
          $({
            $($rec_ident:ident : $rec_ty:ty),*
            $(,)?
          })?
          $((
            $($non_rec_ty:ty),*
            $(,)?
          ))?
        ),*
        $(,)?
    }) => {
        pub trait Precedences {
            $(
                mk!(@prec_method $name $variant; $($($rec_ident : $rec_ty),*)?);
            )*
        }
        mk!(@pre_macro_rule {$({$name $variant; $($($rec_ident : $rec_ty),*)?})*} {} {$($name $variant),*});

        impl<P: Precedences> Parens<P> {
            pastey::paste! {
                fn [< precedence_for_ $name:snake >](&self, x: &$name) -> PrecedenceLevel {
                    match x {
                        $(
                            $name::$variant {..} => self.printer.[< prec_ $name:snake _ $variant:snake >](x),
                        )*
                        _ => todo!(),
                    }
                }
                fn [< visit_ $name:snake _with_precedence >](&mut self, x: &mut $name) {
                    match x {
                        $(
                            $name::$variant {$($($rec_ident),*)?} => {
                                mk!(@parens_arm $name $variant self x; $($($rec_ident : $rec_ty),*)?);
                            },
                        )*
                        _ => todo!(),
                    }
                }
            }
        }
    };

    (@parens_arm $name:ident $variant:ident $self:ident $x:ident; $($field_name:tt : $field_ty:ty),*) => {
        pastey::paste! {
            $(
                $self.with_precedence(
                    $self.printer.[< prec_ $name:snake _ $variant:snake _ $field_name >]($field_name),
                    |this| this.visit($field_name),
                );
            )*
        }
    };

    (@prec_method $name:ident $variant:ident; $($field_name:tt : $field_ty:ty),*) => {
        pastey::paste! {
            fn [< prec_ $name:snake _ $variant:snake >](&self, [< $name:snake >]: &$name) -> PrecedenceLevel {
                let _ = [< $name:snake >];
                PrecedenceLevel::Inherit
            }
            $(
                fn [< prec_ $name:snake _ $variant:snake _ $field_name >](&self, $field_name: &$field_ty) -> PrecedenceLevel {
                    let _ = $field_name;
                    PrecedenceLevel::Inherit
                }
            )*
        }
    };

    (@pre_macro_rule
        {}
        {$($acc:tt)*}
        {$($just_variants:tt)*}
    ) => {
        mk!(@macro_rule {$($just_variants)*} $($acc)*);
    };
    (@pre_macro_rule
        {
            {$name:ident $variant:ident; $($field_name:tt : $field_ty:ty),*}
            $($rest:tt)*
        }
        {$($acc:tt)*}
        {$($just_variants:tt)*}
    ) => {
        mk!(@pre_macro_rule {$($rest)*} {$($name $variant $field_name $field_ty;)* $($acc)*} {$($just_variants)*});
    };
    (@macro_rule {$($vname:ident $vvariant:ident),*} $($name:ident $variant:ident $field_name:tt $field_ty:ty;)*) => {
        pastey::paste! {
            macro_rules! hello {
                $(
                    (@set $vname $vvariant = |$binder:pat_param| $prec_body:expr) => {
                        fn [< prec_ $vname:snake _ $vvariant:snake >](&self, $binder: &$vname) -> PrecedenceLevel {
                            $prec_body
                        }
                    };
                )*
                $(
                    (@set $name $variant $field_name = |$binder:pat_param| $prec_body:expr) => {
                        fn [< prec_ $name:snake _ $variant:snake _ $field_name >](&self, #[allow(unused)]$binder: &$field_ty) -> PrecedenceLevel {
                            $prec_body
                        }
                    };
                )*
            }
        }
    };
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PrecedenceLevel {
    Inherit,
    MinusInfinity,
    Value(isize),
}

impl PartialOrd for PrecedenceLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        todo!()
    }
}

macro_rules! set {
    {} => {};
    {{$($path:ident)*}$(,)?} => {};
    {{$($path:ident)*} {$($value:tt)*}} => {
        set!({$($path)*} $($value)*);
    };
    {{$($path:ident)*} $value:literal} => {
        hello!(@set $($path)* = |_| PrecedenceLevel::Value($value));
    };
    {{$($path:ident)*} Inherit} => {
        hello!(@set $($path)* = |_| PrecedenceLevel::Inherit);
    };
    {{$($path:ident)*} Never} => {
        hello!(@set $($path)* = |_| PrecedenceLevel::MinusInfinity);
    };
    {{$($path:ident)*} |$binder:pat_param| $value:expr} => {
        hello!(@set $($path)* = |$binder| $value);
    };
    {{$($path:ident)*} $value:expr} => {
        hello!(@set $($path)* = |_| $value);
    };
    {{$($path:ident)*} $($key:ident).+ : {$($value:tt)*}$(, $($rest:tt)*)?} => {
        set!({$($path)* $($key)*} $($value)*);
        set!({$($path)*} $($($rest)*)?);
    };
    {{$($path:ident)*} self : $value:expr$(, $($rest:tt)*)?} => {
        set!({$($path)*} $value);
        set!({$($path)*} $($($rest)*)?);
    };
    {{$($path:ident)*} $($key:ident).+ : $value:expr$(, $($rest:tt)*)?} => {
        set!({$($path)* $($key)*} $value);
        set!({$($path)*} $($($rest)*)?);
    };
    {{$($value:tt)+}} => {
        set!({} $($value)*);
    };
    {$($key:ident).+ : $($rest:tt)*} => {
        set!({} $($key).+ : $($rest)*);
    };
}

mk!(
    enum ExprKind {
        If {
            condition: Expr,
            then: Expr,
            else_: Option<Expr>,
        },
        App {
            head: Expr,
            args: Vec<Expr>,
            generic_args: Vec<GenericValue>,
            bounds_impls: Vec<ImplExpr>,
            trait_: Option<(ImplExpr, Vec<GenericValue>)>,
        },
        // Literal(Literal),
        // Array(Vec<Expr>),
        Construct {
            constructor: GlobalId,
            is_record: bool,
            is_struct: bool,
            fields: Vec<(GlobalId, Expr)>,
            base: Option<Expr>,
        },
        Match {
            scrutinee: Expr,
            arms: Vec<Arm>,
        },
        // Tuple(Vec<Expr>),
        Borrow {
            mutable: bool,
            inner: Expr,
        },
        AddressOf {
            mutable: bool,
            inner: Expr,
        },
        // Deref(Expr),
        Let {
            lhs: Pat,
            rhs: Expr,
            body: Expr,
        },
        // GlobalId(GlobalId),
        // LocalId(LocalId),
        Ascription {
            e: Expr,
            ty: Ty,
        },
        Assign {
            lhs: Lhs,
            value: Expr,
        },
        Loop {
            body: Expr,
            kind: LoopKind,
            state: Option<LoopState>,
            control_flow: Option<ControlFlowKind>,
            label: Option<Symbol>,
        },
        Break {
            value: Expr,
            label: Option<Symbol>,
        },
        Return {
            value: Expr,
        },
        Continue {
            label: Option<Symbol>,
        },
        Closure {
            params: Vec<Pat>,
            body: Expr,
            captures: Vec<Expr>,
        },
        Block {
            body: Expr,
            safety_mode: SafetyKind,
        },
        Quote {
            contents: Quote,
        },
        // Resugared(ResugaredExprKind),
        // Error(ErrorNode),
    }
);

struct Rust;

impl Precedences for Rust {
    set!(
        ExprKind: {
            Closure: {
                self: 10,
                params: 50
            },
        },
    );
}
