extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::{Group, TokenStream as TokenStream2, TokenTree};
use syn::parse::{Parse, ParseStream, Result};
use syn::{Ident, Token, parse_macro_input};

fn replace_in_stream(
    stream: TokenStream2,
    target: &Ident,
    replacement: &TokenStream2,
) -> TokenStream2 {
    stream
        .into_iter()
        .flat_map(|tt| match tt {
            TokenTree::Ident(ident) if ident == *target => {
                replacement.clone().into_iter().collect()
            }
            TokenTree::Group(group) => {
                let new_stream = replace_in_stream(group.stream(), target, replacement);
                let mut new_group = Group::new(group.delimiter(), new_stream);
                new_group.set_span(group.span());
                vec![TokenTree::Group(new_group)]
            }
            other => vec![other],
        })
        .collect()
}

// The arguments that the `replace` proc-macro can take
struct AttributeArgs {
    target: Ident,
    replacement: TokenStream2,
}

impl Parse for AttributeArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let target: Ident = input.parse()?;
        input.parse::<Token![=>]>()?;
        Ok(AttributeArgs {
            target,
            replacement: input.parse::<TokenStream2>()?,
        })
    }
}

pub fn replace(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as AttributeArgs);
    let item_stream: TokenStream2 = item.into();
    replace_in_stream(item_stream, &args.target, &args.replacement).into()
}
