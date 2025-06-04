//! This module provides a wrapper type `PrintContext<'a, T>` that adds
//! contextual informations to piece of information of type `T` present in the
//! AST.

use crate::ast::fragment::FragmentRef;
use std::{ops::Deref, rc::Rc};

/// The position of an information in the AST.
/// For example, in the function application `f x y z`, `y` is in the position "Second argument of the application `f x y z`".
///
/// TODO: this is currently a String, this should be a enumeration of all possible places in the AST.
type AstPosition = String;

/// A [`PrintContext<'a, T>`] contains a reference to `T` and a payload of type
/// [`PrintContextPayload`], holding contextual informations useful for printing.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct PrintContext<'a, T> {
    pub value: &'a T,
    pub payload: PrintContextPayload<'a>,
}

/// A [`ParentPrintContext`] is a [`PrintContext`] for any AST type.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ParentPrintContext<'a> {
    pub value: FragmentRef<'a>,
    pub payload: PrintContextPayload<'a>,
}

/// A [`PrintContextPayload`] contains useful contextual information for pretty
/// printing. This struct contains data that help locating an AST fragment
/// within a larger AST.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct PrintContextPayload<'a> {
    pub position: AstPosition,
    pub parent: Option<Rc<ParentPrintContext<'a>>>,
}

/// Lifts a [`PrintContext`] as a [`ParentPrintContext`].
impl<'a, T> From<PrintContext<'a, T>> for ParentPrintContext<'a>
where
    &'a T: Into<FragmentRef<'a>>,
{
    fn from(print_ctx: PrintContext<'a, T>) -> Self {
        Self {
            value: print_ctx.value.into(),
            payload: print_ctx.payload,
        }
    }
}

/// Open a context: get the value inside a [`PrintContext`].
pub trait OpenPrintContext<'a>: Sized {
    type Inner;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Inner;
}

impl<'a, T: OpenPrintContext<'a>> OpenPrintContext<'a> for Vec<T> {
    type Inner = Vec<T::Inner>;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Inner {
        ctx.value
            .iter()
            .enumerate()
            .map(|(i, value)| PrintContext {
                value,
                payload: PrintContextPayload {
                    position: format!("{}[{i}]", ctx.payload.position),
                    ..ctx.payload.clone()
                },
            })
            .map(|value| T::open(value))
            .collect()
    }
}
impl<'a, T: OpenPrintContext<'a>> OpenPrintContext<'a> for Box<T> {
    type Inner = Box<T::Inner>;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Inner {
        let value: &'a T = &*ctx.value;
        Box::new(
            PrintContext {
                value,
                payload: ctx.payload.clone(),
            }
            .open(),
        )
    }
}

impl<'a, T: OpenPrintContext<'a>> OpenPrintContext<'a> for Option<T> {
    type Inner = Option<T::Inner>;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Inner {
        ctx.value.as_ref().map(|value| {
            PrintContext {
                value,
                payload: ctx.payload.clone(),
            }
            .open()
        })
    }
}

impl<'a, T1: OpenPrintContext<'a>, T2: OpenPrintContext<'a>> OpenPrintContext<'a> for (T1, T2) {
    type Inner = (T1::Inner, T2::Inner);
    fn open(ctx: PrintContext<'a, Self>) -> Self::Inner {
        let (v1, v2) = ctx.value;
        (
            PrintContext {
                value: v1,
                payload: PrintContextPayload {
                    position: format!("{}._0", ctx.payload.position),
                    ..ctx.payload.clone()
                },
            }
            .open(),
            PrintContext {
                value: v2,
                payload: PrintContextPayload {
                    position: format!("{}._1", ctx.payload.position),
                    ..ctx.payload.clone()
                },
            }
            .open(),
        )
    }
}

impl<'a, T> PrintContext<'a, T>
where
    T: OpenPrintContext<'a>,
{
    /// Helper `open` method on contextes: this enables `c.open()` where `c` is an `PrintContext`.
    pub fn open(self) -> T::Inner {
        T::open(self)
    }
}

impl<'a, T> Deref for PrintContext<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.value
    }
}
