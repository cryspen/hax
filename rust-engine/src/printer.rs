//! This modules provides types and helper for the printers of hax.

mod allocator;
pub use allocator::Allocator;

use pretty::Pretty;

use crate::ast;
use crate::ast::span::Span;

/// A resugar is a mapper with a name.
pub trait Resugar: ast::visitors::Map {
    /// Get the name of the resugar.
    fn name(&self) -> String;
}

/// A printer defines a list of resugaring phases.
pub trait Printer: Sized {
    /// A list of resugaring phases.
    fn resugaring_phases() -> Vec<Box<dyn Resugar>>;
}

/// Placeholder type for sourcemaps.
pub struct SourceMap;

/// Helper trait to print AST fragments.
pub trait Print<T>: Printer {
    /// Print a fragment using a backend.
    fn print(self, fragment: &mut T) -> Option<(String, SourceMap)>;
}

macro_rules! derive_print {
    ($ty:ty, $method:ident) => {
        impl<P: Printer> Print<$ty> for P
        where
            for<'a, 'b> &'b $ty: Pretty<'a, Allocator<Self>, Span>,
        {
            fn print(self, fragment: &mut $ty) -> Option<(String, SourceMap)> {
                for mut reguaring_phase in Self::resugaring_phases() {
                    reguaring_phase.$method(fragment)
                }
                let allocator = Allocator::new(self);
                let doc = fragment.pretty(&allocator).into_doc();
                let mut mem = Vec::new();
                doc.render(80, &mut mem).ok()?;
                Some((str::from_utf8(&mem).ok()?.to_string(), SourceMap))
            }
        }
    };
}
derive_print!(ast::Expr, visit_expr);
derive_print!(ast::Item, visit_item);
derive_print!(ast::Pat, visit_pat);
derive_print!(ast::Ty, visit_ty);

/// Common resugars which makes sense to share among printers.
pub mod common_resugars {
    use super::*;

    mod unit_ty_resugar {
        use super::*;
        use ast::{resugared::*, visitors::map::*, *};

        /// Resugars the tuple type of arity zero as [`ResugaredTyKind::Unit`].
        pub struct UnitTyResugar;
        impl Resugar for UnitTyResugar {
            fn name(&self) -> String {
                "UnitTyResugar".into()
            }
        }
        impl Map for UnitTyResugar {
            fn visit_ty_kind(&mut self, v: &mut TyKind) -> () {
                if let TyKind::Tuple(args) = v {
                    if args.is_empty() {
                        *v = ResugaredTyKind::Unit.into();
                    }
                }
                visit_ty_kind(self, v);
            }
        }

        #[test]
        fn unit_ty_resugar_test() {
            let tuple0 = Ty(Box::new(TyKind::Tuple(vec![])));
            let mut ty = Ty(Box::new(TyKind::Tuple(vec![tuple0])));
            let expected = Ty(Box::new(TyKind::Tuple(vec![Ty(Box::new(
                TyKind::Resugared(ResugaredTyKind::Unit),
            ))])));
            UnitTyResugar.visit_ty(&mut ty);
            assert_eq!(ty, expected);
        }
    }
    pub use unit_ty_resugar::UnitTyResugar;
}
