use nom::{
    branch::alt,
    bytes::complete::{tag, take_until, take_while1},
    combinator::{map, map_res},
    multi::many0,
    sequence::{delimited, preceded},
    IResult,
};
use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::visit_mut::{self, VisitMut};
use syn::{parse_macro_input, Expr, Item, LitChar, LitStr};

struct PrettyConfig {
    sigil: char,
}

/// Input parser for `pretty_s!` (sigil + template)
struct PrettyInput {
    config: PrettyConfig,
    template: String,
}

impl Parse for PrettyInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.peek(LitChar) {
            // Custom sigil provided
            let litc: LitChar = input.parse()?;
            let sigil = litc.value();
            let _comma: syn::token::Comma = input.parse()?;
            let lits: LitStr = input.parse()?;
            Ok(PrettyInput {
                config: PrettyConfig { sigil },
                template: lits.value(),
            })
        } else {
            // Default to '$'
            let lits: LitStr = input.parse()?;
            Ok(PrettyInput {
                config: PrettyConfig { sigil: '$' },
                template: lits.value(),
            })
        }
    }
}

/// Function-like macro: `pretty_s!(sigil, template)`
// #[proc_macro]
pub fn pretty_s(input: TokenStream) -> TokenStream {
    let PrettyInput { config, template } = parse_macro_input!(input as PrettyInput);
    match config.parse_template(&template) {
        Ok((_, frags)) => {
            eprintln!("{:#?}", frags);
            let doc_tokens = config.gen_doc(&frags);
            TokenStream::from(quote! { #doc_tokens })
        }
        Err(e) => {
            let error = format!("pretty_s!: parse error: {:?}", e);
            TokenStream::from(quote! {
                compile_error!(#error);
            })
        }
    }
}

/// Attribute macro: `#[pretty_tmpl('x')]` rewrites raw strings to `pretty_s!`
// #[proc_macro_attribute]
pub fn pretty_tmpl(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Parse sigil char
    let sig = parse_macro_input!(attr as LitChar).value();
    // Parse the input item AST
    let mut ast: Item = syn::parse(item.clone()).expect("Failed to parse item for pretty_tmpl");
    // Rewrite raw strings
    SigilRewriter { sig }.visit_item_mut(&mut ast);
    TokenStream::from(quote! { #ast })
}

/// AST-folder that replaces raw `r"..."` or `r#"..."#` (single hash) with `pretty_s!(sig, raw)`
struct SigilRewriter {
    sig: char,
}

impl VisitMut for SigilRewriter {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if let Expr::Lit(lit_expr) = expr {
            if let syn::Lit::Str(ref litstr) = lit_expr.lit {
                // Original literal token (including r#...#)
                let orig = litstr.token().to_string();
                let is_raw = orig.starts_with("r\"")
                    || (orig.starts_with("r#\"") && !orig.starts_with("r##\""));
                if is_raw {
                    // Replace with pretty_s!(sig, raw_literal)
                    let sig_lit = syn::LitChar::new(self.sig, litstr.span());
                    *expr = syn::parse_quote! { pretty_s!(#sig_lit, #litstr) };
                    return;
                }
            }
        }
        visit_mut::visit_expr_mut(self, expr)
    }
}

#[derive(Debug)]
/// Fragments in the parsed template
enum Frag {
    Text(String),
    Space,
    SoftLine,
    FlatLine,
    HardLine,
    Interpolation(String),
    Group(Vec<Frag>),
    Nest(usize, Vec<Frag>),
    Join(Option<Vec<Frag>>, String),
}

use nom::Parser;

impl<'a: 'b, 'b> PrettyConfig {
    /// Parse the entire template into fragments
    fn parse_template(&'a self, input: &'b str) -> IResult<&'b str, Vec<Frag>> {
        many0(|i| self.parse_frag(i)).parse(input)
    }

    /// Parse a single fragment
    fn parse_frag(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        alt((
            |i| self.parse_nest(i),
            |i| self.parse_join_sep(i),
            |i| self.parse_join(i),
            |i| self.parse_group(i),
            |i| self.parse_interpolation(i),
            |i| self.parse_escape(i),
            |i| self.parse_text(i),
        ))
        .parse(input)
    }

    /// Parse group: `{sigil}{{ ... }}`
    fn parse_group(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        let open = format!("{}{{{{", self.sigil);
        let (input, inner) =
            delimited(tag(&*open), |i| self.parse_template(i), tag("}}")).parse(input)?;
        Ok((input, Frag::Group(inner)))
    }

    /// Parse nest: `{sigil}nest[N]{{ ... }}`
    fn parse_nest(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        let prefix = format!("{}nest[", self.sigil);
        let (input, (_, num, _)) = (
            tag(&*prefix),
            take_while1(|c: char| c.is_digit(10)),
            tag("]{"),
        )
            .parse(input)?;
        let indent: usize = num.parse().unwrap();
        let (input, inner) = map_res(take_until("}"), |s: &str| {
            self.parse_template(s).map(|(_, frags)| frags)
        })
        .parse(input)?;
        let (input, _) = tag("}")(input)?;
        Ok((input, Frag::Nest(indent, inner)))
    }

    /// Parse join with separator: `{sigil}join[sep]{{iter}}`
    fn parse_join_sep(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        let prefix = format!("{}join[", self.sigil);
        let (input, _) = tag(&*prefix).parse(input)?;
        let (input, sep_frags) = map_res(take_until("]{"), |s: &str| {
            self.parse_template(s).map(|(_, frags)| frags)
        })
        .parse(input)?;
        let (input, _) = tag("]{")(input)?;
        let (input, iter_expr) = take_while1(|c| c != '}')(input)?;
        let (input, _) = tag("}")(input)?;
        Ok((input, Frag::Join(Some(sep_frags), iter_expr.to_string())))
    }

    /// Parse join without separator: `{sigil}join{{iter}}`
    fn parse_join(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        let open = format!("{}join{{", self.sigil);
        let (input, _) = tag(&*open).parse(input)?;
        let (input, iter_expr) = take_while1(|c| c != '}')(input)?;
        let (input, _) = tag("}")(input)?;
        Ok((input, Frag::Join(None, iter_expr.to_string())))
    }

    /// Parse interpolation: `$x` or `${x}`
    fn parse_interpolation(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        let dollar = self.sigil.to_string();
        alt((
            map(
                delimited(
                    tag(format!("{}{{", self.sigil).as_str()),
                    take_while1(|c: char| c.is_alphanumeric() || c == '_'),
                    tag("}"),
                ),
                |s: &str| Frag::Interpolation(s.to_string()),
            ),
            map(
                preceded(
                    tag(dollar.as_str()),
                    take_while1(|c: char| c.is_alphanumeric() || c == '_'),
                ),
                |s: &str| Frag::Interpolation(s.to_string()),
            ),
        ))
        .parse(input)
    }

    /// Parse escapes: `\s`, `\l`, `\L`, `\n`, `\\`
    fn parse_escape(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        let (input, _) = tag("\\")(input)?;
        let (input, c) = take_while1(|c| matches!(c, 's' | 'l' | 'L' | 'n' | '\\'))(input)?;
        let frag = match c {
            "s" => Frag::Space,
            "l" => Frag::SoftLine,
            "L" => Frag::FlatLine,
            "n" => Frag::HardLine,
            "\\" => Frag::Text("\\".to_string()),
            _ => unreachable!(),
        };
        Ok((input, frag))
    }

    /// Parse plain text until next sigil or backslash
    fn parse_text(&'a self, input: &'b str) -> IResult<&'b str, Frag> {
        map(take_while1(|c| c != '$' && c != '\\'), |s: &str| {
            Frag::Text(s.to_string())
        })
        .parse(input)
    }

    /// Generate Rust tokens building up the final `RcDoc` from fragments
    fn gen_doc(&'a self, frags: &[Frag]) -> proc_macro2::TokenStream {
        // Start with an empty document
        let mut expr = quote! { ::pretty::RcDoc::nil() };
        for frag in frags {
            let part_ts = match frag {
                Frag::Text(s) => quote! { ::pretty::RcDoc::text(#s) },
                Frag::Space => quote! { ::pretty::RcDoc::text(" ") },
                Frag::SoftLine => quote! { ::pretty::Doc::line() },
                Frag::FlatLine => quote! { ::pretty::Doc::line_() },
                Frag::HardLine => quote! { ::pretty::Doc::hardline() },
                Frag::Interpolation(var) => {
                    let ident = syn::Ident::new(var, proc_macro2::Span::call_site());
                    quote! { (#ident).to_doc(self) }
                }
                Frag::Group(inner) => {
                    let tokens = self.gen_doc(inner);
                    quote! {{ let d = #tokens; d.group() }}
                }
                Frag::Nest(i, inner) => {
                    let tokens = self.gen_doc(inner);
                    quote! {{ let d = #tokens; d.nest(#i) }}
                }
                Frag::Join(Some(sep), iter) => {
                    let sep_ts = self.gen_doc(sep);
                    let iter_ts: proc_macro2::TokenStream = iter.parse().unwrap();
                    quote! {{
                        let sep = #sep_ts;
                        ::pretty::RcDoc::intersperse((#iter_ts).into_iter().map(|i| i.to_doc(self)), sep)
                    }}
                }
                Frag::Join(None, iter) => {
                    let iter_ts: proc_macro2::TokenStream = iter.parse().unwrap();
                    quote! {{
                        ::pretty::RcDoc::intersperse((#iter_ts).into_iter().map(|i| i.to_doc(self)), ::pretty::RcDoc::nil())
                    }}
                }
            };
            // Hoist previous expression and the part into a new binding
            expr = quote! {
                {
                    let prev = #expr;
                    let part = #part_ts;
                    prev.append(part)
                }
            };
        }
        expr
    }
}
