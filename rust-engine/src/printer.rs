//! This modules provides types and helper for the printers of hax.

mod allocator;
pub use allocator::Allocator;

use bitstream_io::LittleEndian;
use pretty::{DocBuilder, Pretty};

use crate::ast;
use crate::ast::span::Span;

#[derive(Copy, Clone, PartialEq, Hash, Eq)]
struct PtrMarker {
    address: usize,
    type_id: TypeId,
}

impl PtrMarker {
    fn new<T: Any + ?Sized>(reference: &T) -> Self {
        let type_id = reference.type_id();
        let address = (&reference as *const _) as usize;
        Self { address, type_id }
    }
}

use std::{
    any::{Any, TypeId},
    collections::{HashMap, HashSet},
    io::BufWriter,
    thread::current,
};

trait AddressToPaths: 'static {
    fn path_to<'a, T: Any>(
        &'a self,
        current_path: impl bitstream_io::BitWrite,
        paths: &mut HashMap<PtrMarker, Vec<u8>>,
        targets: &mut HashSet<PtrMarker>,
    ) {
        let self_ptr_marker = PtrMarker::new(self);
        if targets.remove(&self_ptr_marker) {
            paths.insert(self_ptr_marker, vec![]);
        }
    }
}

#[test]
fn f() {
    let v = {
        use bitstream_io::BitWrite;
        let mut x: bitstream_io::BitWriter<Vec<u8>, LittleEndian> =
            bitstream_io::BitWriter::new(vec![]);
        x.write::<4, u8>(13).unwrap();
        x.write::<4, u8>(13).unwrap();
        x.write::<4, u8>(13).unwrap();
        x.write::<4, u8>(13).unwrap();
        x.write::<4, u8>(13).unwrap();
        x.pad(8);
        x.into_writer()
    };
    println!("Hello {:#?}", v);
}

pub enum SyntaxScope {
    None,
    Test,
}
pub struct Annotation {
    span: Option<Span>,
    scope: SyntaxScope,
}

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

pub type Doc<'a, P> = DocBuilder<'a, Allocator<P>, Annotation>;

pub trait Print<P: Printer> {
    fn print<'a, 'b>(&'a self, printer: &'b Allocator<P>) -> Doc<'b, P>;
}

macro_rules! derive_printer {
    ($($ty:ty $([$has_span:ident])? $({$syntax_scope:expr})?),*$(,)?) => {
        $(
            impl<P: Printer $(+ $has_span)?> Print<P> for $ty
            where
                for<'a, 'b> &'b $ty: Pretty<'a, Allocator<P>, Annotation>,
            {
                fn print<'a, 'b>(&'a self, printer: &'b Allocator<P>) -> Doc<'b, P> {

                    let doc = self.pretty(printer);
                    derive_printer!(@{self}{doc}{$($has_span)?}{$($syntax_scope)?});
                    doc
                }
            }
        )*
    };
    (@{$self:expr}{$doc:ident}{}{}) => {};
    (@{$self:expr}{$doc:ident}{HasSpan}{$syntax_scope:expr}) => {
        let $doc = $doc.annotate(Annotation{
            span: Some($self.span()),
            scope: SyntaxScope::$syntax_scope,
        });
    };
    (@{$self:expr}{$doc:ident}{HasSpan}{}) => {
        let $doc = $doc.annotate(Annotation{
            span: Some($self.span()),
            scope: SyntaxScope::None,
        });
    };
    (@{$self:expr}{$doc:ident}{}{$syntax_scope:expr}) => {
        let $doc = $doc.annotate(Annotation{
            span: None,
            scope: $syntax_scope,
        });
    };
}

use crate::ast::traits::HasSpan;
derive_printer!(
    ast::Expr[HasSpan],
    ast::ExprKind,
    ast::Pat,
    ast::PatKind,
    ast::Item,
    ast::ItemKind,
);

/// Helper trait to print AST fragments.
pub trait RenderFragment<T>: Printer {
    /// Print a fragment using a backend.
    fn render_fragment(self, fragment: &mut T) -> Option<(String, SourceMap)>;
}

macro_rules! derive_render_fragment {
    ($ty:ty, $method:ident) => {
        impl<P: Printer> RenderFragment<$ty> for P
        where
            for<'a, 'b> &'b $ty: Pretty<'a, Allocator<Self>, Span>,
        {
            fn render_fragment(self, fragment: &mut $ty) -> Option<(String, SourceMap)> {
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
derive_render_fragment!(ast::Expr, visit_expr);
derive_render_fragment!(ast::Item, visit_item);
derive_render_fragment!(ast::Pat, visit_pat);
derive_render_fragment!(ast::Ty, visit_ty);

/// Common resugars which makes sense to share among printers.
pub mod common_resugars {
    use super::*;

    mod unit_ty_resugar {

        use crate::ast::identifiers::{
            global_id::{ConcreteOrTupleId, TupleIdentifier},
            GlobalId,
        };

        use super::*;
        use ast::{resugared::*, visitors::map::*, *};

        fn destruct_type_as_tuple(ty: &Ty) -> Option<Vec<&Ty>> {
            let ty_kind::App { head, args } = ty.expect_App()?;
            let TyKind::App { head, args } = &*ty.0 else {
                None?
            };
            let GlobalId::Concrete(ConcreteOrTupleId::Tuple(TupleIdentifier::Type { length: _ })) =
                head
            else {
                None?
            };

            Some(
                args.iter()
                    .flat_map(|arg| match arg {
                        GenericValue::Ty(arg) => Some(arg),
                        _ => None,
                    })
                    .collect(),
            )
        }

        /// Resugars the tuple type of arity zero as [`ResugaredTyKind::Unit`].
        pub struct UnitTyResugar;
        impl Resugar for UnitTyResugar {
            fn name(&self) -> String {
                "UnitTyResugar".into()
            }
        }
        impl Map for UnitTyResugar {
            fn visit_ty(&mut self, v: &mut Ty) -> () {
                if let Some(types) = destruct_type_as_tuple(v) {
                    if types.is_empty() {
                        *v.0 = ResugaredTyKind::Unit.into();
                    }
                }
                visit_ty(self, v);
            }
        }

        // #[test]
        // fn unit_ty_resugar_test() {
        //     let tuple0 = Ty(Box::new(TyKind::Tuple(vec![])));
        //     let mut ty = Ty(Box::new(TyKind::Tuple(vec![tuple0])));
        //     let expected = Ty(Box::new(TyKind::Tuple(vec![Ty(Box::new(
        //         TyKind::Resugared(ResugaredTyKind::Unit),
        //     ))])));
        //     UnitTyResugar.visit_ty(&mut ty);
        //     assert_eq!(ty, expected);
        // }
    }
    pub use unit_ty_resugar::UnitTyResugar;
}
