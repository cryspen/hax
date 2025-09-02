//! Pretty-printing support for the hax AST.
//!
//! This module defines the trait [`PrettyAst`], which is the **primary trait a printer should
//! implement**. It also exposes a handful of ergonomic helper macros that wire the
//! [`pretty`](https://docs.rs/pretty/) crate's allocator into concise printing code, while
//! taking care of annotations/spans for you.
//!
//! # Quickstart
//! In most printers you:
//! 1. Implement [`Printer`] for your allocator/type,
//! 2. Implement [`PrettyAst`] for that allocator,
//! 3. Call `x.pretty(&allocator)` on AST values.
//!
//! See [`super::backends`] for backend and printer examples.
//!
//! # Lifetimes and Parameters
//! - `'a`: lifetime tied to the **document allocator** (from `pretty::DocAllocator`).
//! - `'b`: lifetime of the **borrowed AST** node(s) being printed.
//! - `A`: the **annotation** type carried in documents (e.g., spans for source maps).
//!   `PrettyAst` is generic over `A`.

use std::fmt::Display;

use super::*;
use crate::ast::*;
use pretty::{DocAllocator, DocBuilder};

use crate::symbol::Symbol;
use identifiers::*;
use literals::*;
use resugared::*;

/// This type is primarily useful inside printer implementations when you want a
/// low-friction way to inspect an AST fragment.
///
/// # What it does
/// - Appends a JSON representation of the wrapped value to
///   `"/tmp/hax-ast-debug.json"` (one JSON document per line).
/// - Implements [`std::fmt::Display`] to print a `just` invocation you can paste in a shell
///   to re-open that same JSON by line number:
///   `just debug-json <line-id>`
///
/// # Example
/// ```rust
/// # use hax_rust_engine::printer::pretty_ast::DebugJSON;
/// # #[derive(serde::Serialize)]
/// # struct Small { x: u32 }
/// let s = Small { x: 42 };
/// // Prints something like: `just debug-json 17`.
/// println!("{}", DebugJSON(&s));
/// // Running `just debug-json 17` will print `{"x":42}`
/// ```
///
/// # Notes
/// - This is a **debugging convenience** and intentionally has a side-effect (file write).
///   Avoid keeping it in user-facing output paths.
/// - The file grows over time; occasionally delete it if you no longer need historical entries.
pub struct DebugJSON<T: serde::Serialize>(pub T);

impl<T: serde::Serialize> Display for DebugJSON<T> {
    #[cfg(not(unix))]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<unknown, DebugJSON supported on unix plateforms only>")
    }
    #[cfg(unix)]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const PATH: &str = "/tmp/hax-ast-debug.json";
        /// Write a new JSON as a line at the end of `PATH`
        fn append_line_json(value: &serde_json::Value) -> std::io::Result<usize> {
            use std::io::{BufRead, BufReader, Write};
            cleanup();
            let file = std::fs::OpenOptions::new()
                .read(true)
                .append(true)
                .create(true)
                .open(PATH)?;
            let count = BufReader::new(&file).lines().count();
            writeln!(&file, "{value}")?;
            Ok(count)
        }

        /// Drop the file at `PATH` when we first write
        fn cleanup() {
            static DID_RUN: AtomicBool = AtomicBool::new(false);
            use std::sync::atomic::{AtomicBool, Ordering};
            if DID_RUN
                .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
                .is_ok()
            {
                let _ignored = std::fs::remove_file(PATH);
            }
        }

        if let Ok(id) = append_line_json(&serde_json::to_value(&self.0).unwrap()) {
            write!(f, "`just debug-json {id}`")
        } else {
            write!(f, "<DebugJSON failed>")
        }
    }
}

impl<'a, 'b, A: 'a + Clone, P: PrettyAst<'a, 'b, A>, T: 'b + serde::Serialize> Pretty<'a, P, A>
    for DebugJSON<T>
{
    fn pretty(self, allocator: &'a P) -> DocBuilder<'a, P, A> {
        allocator.as_string(format!("{self}"))
    }
}

#[macro_export]
/// Similar to [`std::todo`], but returns a document instead of panicking with a message.
macro_rules! todo_document {
    ($allocator:ident,) => {
        {return $allocator.todo_document(&format!("TODO_LINE_{}", std::line!()));}
    };
    ($allocator:ident, $($tt:tt)*) => {
        {
            let message = format!($($tt)*);
            return $allocator.todo_document(&message);
        }
    };
}
pub use todo_document;

#[macro_export]
/// Install pretty-printing helpers partially applied with a given local
/// allocator.
///
/// This macro declares a set of small, local macros that proxy to the
/// underlying [`pretty::DocAllocator`] methods and macro while capturing your
/// allocator value. It keeps printing code concise and avoids passing the
/// allocator around explicitly.
///
/// # Syntax
/// ```rust,ignore
/// install_pretty_helpers!(alloc_ident: AllocatorType)
/// ```
///
/// - `alloc_ident`: the in-scope variable that implements both
///   [`pretty::DocAllocator`] and [`Printer`].
/// - `AllocatorType`: the concrete type of that variable.
///
/// # What gets installed
/// - macro shorthands for common allocator methods:
///   [`pretty::DocAllocator::nil`], [`pretty::DocAllocator::fail`],
///   [`pretty::DocAllocator::hardline`], [`pretty::DocAllocator::space`],
///   [`pretty::DocAllocator::line`], [`pretty::DocAllocator::line_`],
///   [`pretty::DocAllocator::softline`], [`pretty::DocAllocator::softline_`],
///   [`pretty::DocAllocator::as_string`], [`pretty::DocAllocator::text`],
///   [`pretty::DocAllocator::concat`], [`pretty::DocAllocator::intersperse`],
///   [`pretty::DocAllocator::column`], [`pretty::DocAllocator::nesting`],
///   [`pretty::DocAllocator::reflow`].
/// - a partially applied version of [`pretty::docs!`].
/// - [`todo_document!`]: produce a placeholder document (that does not panic).
macro_rules! install_pretty_helpers {
    ($allocator:ident : $allocator_type:ty) => {
        $crate::printer::pretty_ast::install_pretty_helpers!(
            @$allocator,
            #[doc = ::std::concat!("Proxy macro for [`", stringify!($crate), "::printer::pretty_ast::todo_document`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            disambiguated_todo{$crate::printer::pretty_ast::todo_document!},
            #[doc = ::std::concat!("Proxy macro for [`pretty::docs`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            docs{pretty::docs!},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::nil`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            nil{<$allocator_type as ::pretty::DocAllocator<'_, _>>::nil},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::fail`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            fail{<$allocator_type as ::pretty::DocAllocator<'_, _>>::fail},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::hardline`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            hardline{<$allocator_type as ::pretty::DocAllocator<'_, _>>::hardline},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::space`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            space{<$allocator_type as ::pretty::DocAllocator<'_, _>>::space},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::line`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            disambiguated_line{<$allocator_type as ::pretty::DocAllocator<'_, _>>::line},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::line_`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            line_{<$allocator_type as ::pretty::DocAllocator<'_, _>>::line_},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::softline`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            softline{<$allocator_type as ::pretty::DocAllocator<'_, _>>::softline},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::softline_`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            softline_{<$allocator_type as ::pretty::DocAllocator<'_, _>>::softline_},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::as_string`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            as_string{<$allocator_type as ::pretty::DocAllocator<'_, _>>::as_string},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::text`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            text{<$allocator_type as ::pretty::DocAllocator<'_, _>>::text},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::concat`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            disambiguated_concat{<$allocator_type as ::pretty::DocAllocator<'_, _>>::concat},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::intersperse`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            intersperse{<$allocator_type as ::pretty::DocAllocator<'_, _>>::intersperse},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::column`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            column{<$allocator_type as ::pretty::DocAllocator<'_, _>>::column},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::nesting`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            nesting{<$allocator_type as ::pretty::DocAllocator<'_, _>>::nesting},
            #[doc = ::std::concat!("Proxy macro for [`pretty::DocAllocator::reflow`] that automatically uses `", stringify!($allocator),"` as allocator.")]
            reflow{<$allocator_type as ::pretty::DocAllocator<'_, _>>::reflow}
        );
    };
    (@$allocator:ident, $($(#[$($attrs:tt)*])*$name:ident{$($callable:tt)*}),*) => {
        $(
            #[hax_rust_engine_macros::partial_apply($($callable)*, $allocator,)]
            #[allow(unused)]
            $(#[$($attrs)*])*
            macro_rules! $name {}
        )*
    };
}
pub use install_pretty_helpers;

macro_rules! mk {
    ($($ty:ident),*) => {
        pastey::paste! {
            /// A trait that defines a print method per type in the AST.
            ///
            /// This is the main trait a printer should implement. It ties
            /// together:
            /// - the [`pretty::DocAllocator`] implementation that builds
            ///   documents,
            /// - the [`Printer`] behavior (syntax highlighting, punctuation
            ///   helpers, …),
            /// - and annotation plumbing (`A`) used for source maps.
            ///
            /// ## Lifetimes and Type Parameters
            /// - `'a`: the allocator/document lifetime.
            /// - `'b`: the lifetime of borrowed AST values being printed.
            /// - `A`: the annotation type carried by documents (must be
            ///   `Clone`).
            ///
            /// ## Implementing `PrettyAst`
            /// ```rust,ignore
            /// impl<'a, 'b, A: 'a + Clone> PrettyAst<'a, 'b, A> for MyPrinter { }
            /// ```
            ///
            /// You then implement the actual formatting logic in the generated
            /// per-type methods. These methods are intentionally marked
            /// `#[deprecated]` to discourage calling them directly; instead,
            /// call `node.pretty(self)` from the [`pretty::Pretty`] trait to
            /// ensure annotations and spans are applied correctly.
            ///
            /// Note that using `install_pretty_helpers!` will produce macro
            /// that implicitely use `self` as allocator. Take a look at a
            /// printer in the [`backends`] module for an example.
            pub trait PrettyAst<'a, 'b, A: 'a + Clone>: DocAllocator<'a, A> + Sized {
                /// Produce a non-panicking placeholder document. In general, prefer the use of the helper macro [`todo_document!`].
                fn todo_document(&'a self, message: &str) -> DocBuilder<'a, Self, A> {
                    self.as_string(message)
                }
                /// Produce a structured error document for an unimplemented
                /// method.
                ///
                /// Printers may override this for nicer diagnostics (e.g.,
                /// colored "unimplemented" banners or links back to source
                /// locations). The default produces a small, debuggable piece
                /// of text that includes the method name and a JSON handle for
                /// the AST fragment (via [`DebugJSON`]).
                fn unimplemented_method(&'a self, method: &str, ast: ast::fragment::FragmentRef<'_>) -> DocBuilder<'a, Self, A> {
                    self.text(format!("`{method}` unimpl, {}", DebugJSON(ast))).parens()
                }
                $(
                    #[doc = "Define how the printer formats a value of this AST type."]
                    #[doc = "Do not call this method directly. Use [`pretty::Pretty::pretty`] instead, so annotations/spans are preserved correctly."]
                    #[deprecated = "Do not call this method directly. Use [`pretty::Pretty::pretty`] instead, so annotations/spans are preserved correctly."]
                    fn [<$ty:snake>](&'a self, [<$ty:snake>]: &'b $ty) -> DocBuilder<'a, Self, A> {
                        mk!(@method_body $ty [<$ty:snake>] self [<$ty:snake>])
                    }
                )*
            }

            $(
                impl<'a, 'b, A: 'a + Clone, P: PrettyAst<'a, 'b, A>> Pretty<'a, P, A> for &'b $ty {
                    fn pretty(self, allocator: &'a P) -> DocBuilder<'a, P, A> {
                        // Note about deprecation:
                        //   Here is the only place where calling the deprecated methods from the trait `PrettyAst` is fine.
                        //   Here is the place we (will) take care of spans, etc.
                        #[allow(deprecated)]
                        let print = <P as PrettyAst<'_, '_, _>>::[<$ty:snake>];
                        print(allocator, self)
                    }
                }
            )*
        }
    };
    // Special default implementation for specific types
    (@method_body Symbol $meth:ident $self:ident $value:ident) => {
        $self.text($value.to_string())
    };
    (@method_body LocalId $meth:ident $self:ident $value:ident) => {
        ::pretty::docs![$self, &$value.0]
    };
    (@method_body $ty:ident $meth:ident $self:ident $value:ident) => {
        $self.unimplemented_method(stringify!($meth), ast::fragment::FragmentRef::from($meth))
    };
}

#[hax_rust_engine_macros::replace(AstNodes => include(VisitableAstNodes))]
mk!(GlobalId, AstNodes);
