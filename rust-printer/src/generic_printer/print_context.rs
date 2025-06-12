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
    /// The inner value
    pub value: &'a T,
    /// The contextual information payload
    pub payload: PrintContextPayload<'a>,
}

/// A [`ParentPrintContext`] is a [`PrintContext`] for any AST type.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct ParentPrintContext<'a> {
    /// The inner value: a borrowed fragment of the AST.
    pub value: FragmentRef<'a>,
    /// The contextual information payload.
    pub payload: PrintContextPayload<'a>,
}

/// A [`PrintContextPayload`] contains useful contextual information for pretty
/// printing. This struct contains data that help locating an AST fragment
/// within a larger AST.
#[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct PrintContextPayload<'a> {
    /// The position of this fragment of AST: where it is located in its parent node.
    ///
    /// # Example:
    /// Consider the following:
    /// ```rust,ignore
    /// f x y z
    /// ```
    /// The position of `y` is "Second argument of a function application"
    pub position: AstPosition,
    /// Parent node
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

/// Open a print context. This pushes more in depth the context.
/// For example, this transforms a `PrintContext<'_, Vec<T>>` in `PrintContext<'_, Vec<T>>`.
pub trait OpenPrintContext<'a>: Sized {
    /// The type after opening.
    type Out;
    /// Opens a context.
    fn open(ctx: PrintContext<'a, Self>) -> Self::Out;
}

impl<'a, T: 'a> OpenPrintContext<'a> for Vec<T> {
    type Out = Vec<PrintContext<'a, T>>;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Out {
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
            .collect()
    }
}

impl<'a, T: 'a> OpenPrintContext<'a> for Box<T> {
    type Out = Box<PrintContext<'a, T>>;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Out {
        let value: &'a T = &*ctx.value;
        Box::new(PrintContext {
            value,
            payload: ctx.payload.clone(),
        })
    }
}

impl<'a, T: 'a> OpenPrintContext<'a> for Option<T> {
    type Out = Option<PrintContext<'a, T>>;
    fn open(ctx: PrintContext<'a, Self>) -> Self::Out {
        ctx.value.as_ref().map(|value| PrintContext {
            value,
            payload: ctx.payload.clone(),
        })
    }
}

impl<'a, T1: 'a, T2: 'a> OpenPrintContext<'a> for (T1, T2) {
    type Out = (PrintContext<'a, T1>, PrintContext<'a, T2>);
    fn open(ctx: PrintContext<'a, Self>) -> Self::Out {
        let (v1, v2) = ctx.value;
        (
            PrintContext {
                value: v1,
                payload: PrintContextPayload {
                    position: format!("{}._0", ctx.payload.position),
                    ..ctx.payload.clone()
                },
            },
            PrintContext {
                value: v2,
                payload: PrintContextPayload {
                    position: format!("{}._1", ctx.payload.position),
                    ..ctx.payload.clone()
                },
            },
        )
    }
}

impl<'a, T> PrintContext<'a, T>
where
    T: OpenPrintContext<'a>,
{
    /// Helper `open` method on contextes: this enables `c.open()` where `c` is an `PrintContext`.
    pub fn open(self) -> T::Out {
        T::open(self)
    }
}

impl<'a, T> Deref for PrintContext<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.value
    }
}
