// SPDX-License-Identifier: Apache-2.0 OR MIT

use proc_macro::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};

pub(crate) fn pin_data(args: TokenStream, input: TokenStream) -> TokenStream {
    // This proc-macro only does some pre-parsing and then delegates the actual parsing to
    // `kernel::_pin_data!`.
    //
    // In here we only collect the generics, since parsing them in declarative macros is very
    // elaborate. We also do not need to analyse their structure, we only need to collect them.

    // `impl_generics`, the declared generics with their bounds.
    let mut impl_generics = vec![];
    // Only the names of the generics, without any bounds.
    let mut ty_generics = vec![];
    // Tokens not related to the generics e.g. the `impl` token.
    let mut rest = vec![];
    // The current level of `<`.
    let mut nesting = 0;
    let mut toks = input.into_iter();
    // if we are at the beginning of a generic parameter
    let mut at_start = true;
    for tt in &mut toks {
        match tt.clone() {
            TokenTree::Punct(p) if p.as_char() == '<' => {
                if nesting >= 1 {
                    impl_generics.push(tt);
                }
                nesting += 1;
            }
            TokenTree::Punct(p) if p.as_char() == '>' => {
                if nesting == 0 {
                    break;
                } else {
                    nesting -= 1;
                    if nesting >= 1 {
                        impl_generics.push(tt);
                    }
                    if nesting == 0 {
                        break;
                    }
                }
            }
            tt => {
                if nesting == 1 {
                    match &tt {
                        TokenTree::Ident(i) if i.to_string() == "const" => {}
                        TokenTree::Ident(_) if at_start => {
                            ty_generics.push(tt.clone());
                            ty_generics.push(TokenTree::Punct(Punct::new(',', Spacing::Alone)));
                            at_start = false;
                        }
                        TokenTree::Punct(p) if p.as_char() == ',' => at_start = true,
                        TokenTree::Punct(p) if p.as_char() == '\'' && at_start => {
                            ty_generics.push(tt.clone());
                        }
                        _ => {}
                    }
                }
                if nesting >= 1 {
                    impl_generics.push(tt);
                } else if nesting == 0 {
                    rest.push(tt);
                }
            }
        }
    }
    rest.extend(toks);
    // This should be the body of the struct `{...}`.
    let last = rest.pop();
    let mut ret = vec![];
    ret.extend("::kernel::__pin_data!".parse::<TokenStream>().unwrap());
    ret.push(TokenTree::Group(Group::new(
        Delimiter::Brace,
        TokenStream::from_iter(vec![
            TokenTree::Ident(Ident::new("parse_input", Span::call_site())),
            TokenTree::Punct(Punct::new(':', Spacing::Alone)),
            TokenTree::Punct(Punct::new('@', Spacing::Alone)),
            TokenTree::Ident(Ident::new("args", Span::call_site())),
            TokenTree::Group(Group::new(
                Delimiter::Parenthesis,
                TokenStream::from_iter(args),
            )),
            TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            TokenTree::Punct(Punct::new('@', Spacing::Alone)),
            TokenTree::Ident(Ident::new("sig", Span::call_site())),
            TokenTree::Group(Group::new(
                Delimiter::Parenthesis,
                TokenStream::from_iter(rest),
            )),
            TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            TokenTree::Punct(Punct::new('@', Spacing::Alone)),
            TokenTree::Ident(Ident::new("impl_generics", Span::call_site())),
            TokenTree::Group(Group::new(
                Delimiter::Parenthesis,
                TokenStream::from_iter(impl_generics),
            )),
            TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            TokenTree::Punct(Punct::new('@', Spacing::Alone)),
            TokenTree::Ident(Ident::new("ty_generics", Span::call_site())),
            TokenTree::Group(Group::new(
                Delimiter::Parenthesis,
                TokenStream::from_iter(ty_generics),
            )),
            TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            TokenTree::Punct(Punct::new('@', Spacing::Alone)),
            TokenTree::Ident(Ident::new("body", Span::call_site())),
            TokenTree::Group(Group::new(
                Delimiter::Parenthesis,
                TokenStream::from_iter(last),
            )),
            TokenTree::Punct(Punct::new(',', Spacing::Alone)),
        ]),
    )));
    TokenStream::from_iter(ret)
}
