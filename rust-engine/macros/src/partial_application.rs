use proc_macro::TokenStream;
use quote::quote;
use syn::{ExprPath, Token, parse_macro_input};

struct PartialApplyArgs {
    ident: ExprPath,
    bang: Option<Token![!]>,
    prefix: proc_macro2::TokenStream,
}

impl syn::parse::Parse for PartialApplyArgs {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let ident = input.parse()?;
        let bang = input.parse()?;
        input.parse::<syn::Token![,]>()?;
        Ok(PartialApplyArgs {
            ident,
            bang,
            prefix: input.parse()?,
        })
    }
}

/// See [`super::partial_apply`].
pub(crate) fn partial_apply(attr: TokenStream, item: TokenStream) -> TokenStream {
    let PartialApplyArgs {
        ident,
        bang,
        prefix,
    } = parse_macro_input!(attr as PartialApplyArgs);
    let input_macro = parse_macro_input!(item as syn::ItemMacro);
    let macro_name = input_macro.ident;
    let attrs = input_macro.attrs;
    quote! {
        #(#attrs)*
        macro_rules! #macro_name {
            ($($rest:tt)*) => {
                #ident #bang(#prefix $($rest)*)
            };
        }
    }
    .into()
}
