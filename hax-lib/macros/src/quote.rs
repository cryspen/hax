//! This module provides the logic for the quotation macros, which
//! allow for quoting F*/Coq/... code directly from Rust.
//!
//! In a F*/Coq/... quote, one can write antiquotations, that is,
//! embedded Rust snippets. The syntax is `$<PREFIX><PAYLOAD>`. The
//! payload `<PAYLOAD>` should be a Rust path, or a group with
//! arbitrary contents `{...contents...}`.
//!
//! The `<PREFIX>` describes the kind of the antiquotation:
//!  - empty prefix, the antiquotation is an expression;
//!  - `?`, the antiquotation is a pattern;
//!  - `$`, the antiquotation is a constructor name;
//!  - `:`, the antiquotation is a type.

use crate::prelude::*;

/// Marker that indicates a place where a antiquotation will be inserted
const SPLIT_MARK: &str = "SPLIT_QUOTE";

/// The different kinds of antiquotations
enum AntiquoteKind {
    Expr,
    Constructor,
    Pat,
    Ty,
}

impl ToTokens for AntiquoteKind {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend([match self {
            Self::Expr => quote! {_expr},
            Self::Constructor => quote! {_constructor},
            Self::Pat => quote! {_pat},
            Self::Ty => quote! {_ty},
        }])
    }
}

/// An antiquotation
struct Antiquote {
    ts: pm::TokenStream,
    kind: AntiquoteKind,
}

impl ToTokens for Antiquote {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let ts = TokenStream::from(self.ts.clone());
        fn wrap_pattern(pat: TokenStream) -> TokenStream {
            quote! {{#[allow(unreachable_code)]
                 match None { Some(#pat) => (), _ => () }
            }}
        }
        let ts = match self.kind {
            AntiquoteKind::Expr => ts,
            AntiquoteKind::Constructor => wrap_pattern(quote! {#ts {..}}),
            AntiquoteKind::Pat => wrap_pattern(ts),
            AntiquoteKind::Ty => quote! {None::<#ts>},
        };
        tokens.extend([ts])
    }
}

/// Re-span every token of a token stream (recursively) to `span`.
///
/// Antiquotation snippets are parsed out of the *contents* of a string
/// literal with `syn::parse_str`, which spans every produced token at
/// `Span::call_site()`. When a quotation macro (e.g. `fstar!`) is invoked
/// via a `macro_rules!` wrapper, that call site is the wrapper's expansion
/// context, so identifiers cannot resolve to the user's locals (hygiene).
/// The string literal token itself, however, travels through wrappers
/// carrying the original span: re-spanning the antiquotation tokens onto
/// the literal's span makes them resolve at the place the user actually
/// wrote them. For direct invocations the literal's span belongs to the
/// same call-site context as before, so behavior is unchanged.
fn respan(ts: TokenStream, span: proc_macro2::Span) -> TokenStream {
    ts.into_iter()
        .map(|mut tt| {
            if let proc_macro2::TokenTree::Group(ref mut g) = tt {
                *g = proc_macro2::Group::new(g.delimiter(), respan(g.stream(), span));
            }
            tt.set_span(span);
            tt
        })
        .collect()
}

/// Extract antiquotations (`$[?][$][:]...`, `$[?][$][:]{...}`) and parses them.
fn process_string(
    s: &str,
    span: proc_macro2::Span,
) -> std::result::Result<(String, Vec<Antiquote>), String> {
    let mut chars = s.chars().peekable();
    let mut antiquotations = vec![];
    let mut output = String::new();
    while let Some(ch) = chars.next() {
        match ch {
            '$' => {
                let mut s = String::new();
                let mut kind = AntiquoteKind::Expr;
                if let Some(prefix) = chars.next_if(|ch| *ch == '?' || *ch == '$' || *ch == ':') {
                    kind = match prefix {
                        '?' => AntiquoteKind::Pat,
                        '$' => AntiquoteKind::Constructor,
                        ':' => AntiquoteKind::Ty,
                        _ => unreachable!(),
                    };
                }
                // If the first character is `{`, we parse the block
                if let Some('{') = chars.peek() {
                    chars.next(); // Consume `{`
                    let mut level = 0;
                    for ch in chars.by_ref() {
                        level += match ch {
                            '{' => 1,
                            '}' => -1,
                            _ => 0,
                        };
                        if level < 0 {
                            break;
                        }
                        s.push(ch);
                    }
                } else {
                    while let Some(ch) = chars.next_if(|ch| {
                        !matches!(ch, ' ' | '\t' | '\n' | '(' | '{' | ')' | ';' | '!' | '?')
                    }) {
                        s.push(ch)
                    }
                }
                if s.is_empty() {
                    return Err(format!(
                        "Empty antiquotation just before `{}`",
                        chars.collect::<String>()
                    ));
                }
                output += SPLIT_MARK;
                // See https://github.com/rust-lang/rust/issues/58736
                let ts: std::result::Result<TokenStream, _> = syn::parse_str(&s)
                    .map_err(|err| format!("Could not parse antiquotation `{s}`: got error {err}"));
                if let Err(message) = &ts {
                    // If we don't panic, the error won't show up,
                    // this is because `parse_str` is not only
                    // panicking, but also makes rustc to exit earlier.
                    panic!("{message}");
                }
                let ts: pm::TokenStream = respan(ts?, span).into();
                antiquotations.push(Antiquote { ts, kind })
            }
            _ => output.push(ch),
        }
    }
    Ok((output, antiquotations))
}

pub(super) fn item(
    kind: ItemQuote,
    attribute_to_inject: TokenStream,
    payload: pm::TokenStream,
    item: pm::TokenStream,
) -> pm::TokenStream {
    let expr = TokenStream::from(expression(InlineExprType::Unit, payload));
    let item = TokenStream::from(item);
    let uid = ItemUid::fresh();
    let uid_attr = AttrPayload::Uid(uid.clone());
    let assoc_attr = AttrPayload::AssociatedItem {
        role: AssociationRole::ItemQuote,
        item: uid,
    };
    let kind_attr = AttrPayload::ItemQuote(kind);
    let status_attr = AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
    use AttrPayload::NeverErased;
    quote! {
        #assoc_attr
        #item
        #attribute_to_inject
        #status_attr
        const _: () = {
            #NeverErased
            #uid_attr
            #kind_attr
            fn quote_contents() {
                #expr
            }
        };
    }
    .into()
}

pub(super) fn detect_future_node_in_expression(e: &syn::Expr) -> bool {
    struct Visitor(bool);
    use syn::visit::*;
    impl<'a> Visit<'a> for Visitor {
        fn visit_expr(&mut self, e: &'a Expr) {
            if let Some(Ok(_)) = crate::utils::expect_future_expr(e) {
                self.0 = true;
            }
        }
    }
    let mut visitor = Visitor(false);
    visitor.visit_expr(e);
    visitor.0
}

pub(super) enum InlineExprType {
    Unit,
    Prop,
    Anything,
}

pub(super) fn expression(typ: InlineExprType, payload: pm::TokenStream) -> pm::TokenStream {
    let (mut backend_code, antiquotes) = {
        let payload_lit = parse_macro_input!(payload as LitStr);
        let payload_span = payload_lit.span();
        let payload = payload_lit.value();
        if payload.contains(SPLIT_MARK) {
            return quote! {std::compile_error!(std::concat!($SPLIT_MARK, " is reserved"))}.into();
        }
        let (string, antiquotes) = match process_string(&payload, payload_span) {
            Ok(x) => x,
            Err(message) => return quote! {std::compile_error!(#message)}.into(),
        };
        let string = proc_macro2::Literal::string(&string);
        let string: TokenStream = [proc_macro2::TokenTree::Literal(string)]
            .into_iter()
            .collect();
        (quote! {#string}, antiquotes)
    };
    for user in antiquotes.iter().rev() {
        if !matches!(typ, InlineExprType::Unit)
            && syn::parse(user.ts.clone())
                .as_ref()
                .map(detect_future_node_in_expression)
                .unwrap_or(false)
        {
            let ts: proc_macro2::TokenStream = user.ts.clone().into();
            return quote! {
                ::std::compile_error!(concat!("The `future` operator cannot be used within a quote. Hint: move `", stringify!(#ts), "` to a let binding and use the binding name instead."))
            }.into();
        }
        let kind = &user.kind;
        backend_code = quote! {
            let #kind = #user;
            #backend_code
        };
    }

    let function = match typ {
        InlineExprType::Unit => quote! {inline},
        InlineExprType::Prop => quote! {inline_unsafe::<::hax_lib::Prop>},
        InlineExprType::Anything => quote! {inline_unsafe},
    };

    quote! {
        // `unused_qualifications` (and lint friends) used to be silenced
        // implicitly because antiquotation tokens carried macro-expansion
        // spans; now that they carry the payload literal's span (see
        // `respan`), suppress them explicitly.
        ::hax_lib::#function(#[allow(unused_variables, unused_qualifications, unreachable_code, deprecated)]{#backend_code})
    }
    .into()
}
