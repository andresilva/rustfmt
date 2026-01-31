use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_ast::ast;
use rustc_ast::token::{Delimiter, TokenKind};
use rustc_ast::tokenstream::TokenStream;
use rustc_parse::exp;
use rustc_parse::parser::ForceCollect;
use rustc_span::{Span, symbol::kw};

use crate::parse::macros::build_stream_parser;
use crate::parse::session::ParseSess;
use crate::rewrite::RewriteContext;

pub(crate) fn parse_cfg_if<'a>(
    psess: &'a ParseSess,
    mac: &'a ast::MacCall,
) -> Result<Vec<ast::Item>, &'static str> {
    match catch_unwind(AssertUnwindSafe(|| parse_cfg_if_inner(psess, mac))) {
        Ok(Ok(items)) => Ok(items),
        Ok(err @ Err(_)) => err,
        Err(..) => Err("failed to parse cfg_if!"),
    }
}

fn parse_cfg_if_inner<'a>(
    psess: &'a ParseSess,
    mac: &'a ast::MacCall,
) -> Result<Vec<ast::Item>, &'static str> {
    let ts = mac.args.tokens.clone();
    let mut parser = build_stream_parser(psess.inner(), ts);

    let mut items = vec![];
    let mut process_if_cfg = true;

    while parser.token.kind != TokenKind::Eof {
        if process_if_cfg {
            if !parser.eat_keyword(exp!(If)) {
                return Err("Expected `if`");
            }

            if !matches!(parser.token.kind, TokenKind::Pound) {
                return Err("Failed to parse attributes");
            }

            // Inner attributes are not actually syntactically permitted here, but we don't
            // care about inner vs outer attributes in this position. Our purpose with this
            // special case parsing of cfg_if macros is to ensure we can correctly resolve
            // imported modules that may have a custom `path` defined.
            //
            // As such, we just need to advance the parser past the attribute and up to
            // to the opening brace.
            // See also https://github.com/rust-lang/rust/pull/79433
            parser
                .parse_attribute(rustc_parse::parser::attr::InnerAttrPolicy::Permitted)
                .map_err(|e| {
                    e.cancel();
                    "Failed to parse attributes"
                })?;
        }

        if !parser.eat(exp!(OpenBrace)) {
            return Err("Expected an opening brace");
        }

        while parser.token != TokenKind::CloseDelim(Delimiter::Brace)
            && parser.token.kind != TokenKind::Eof
        {
            let before_span = parser.token.span;
            let item = match parser.parse_item(ForceCollect::No) {
                Ok(Some(item_ptr)) => item_ptr.into_inner(),
                Ok(None) => {
                    // Guard against infinite loop: if parse_item returned None without
                    // consuming any tokens, manually bump to make progress.
                    if parser.token.span == before_span {
                        parser.bump();
                    }
                    continue;
                }
                Err(err) => {
                    err.cancel();
                    parser.psess.dcx().reset_err_count();
                    return Err(
                        "Expected item inside cfg_if block, but failed to parse it as an item",
                    );
                }
            };
            if let ast::ItemKind::Mod(..) = item.kind {
                items.push(item);
            }
        }

        if !parser.eat(exp!(CloseBrace)) {
            return Err("Expected a closing brace");
        }

        if parser.eat(exp!(Eof)) {
            break;
        }

        if !parser.eat_keyword(exp!(Else)) {
            return Err("Expected `else`");
        }

        process_if_cfg = parser.token.is_keyword(kw::If);
    }

    Ok(items)
}

/// The kind of branch in a cfg_if! macro.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CfgIfBranchKind {
    If,
    ElseIf,
    Else,
}

/// A branch in a `cfg_if!` macro for formatting purposes.
pub(crate) struct CfgIfBranch {
    /// The kind of branch (if, else if, else).
    pub kind: CfgIfBranchKind,
    /// The `#[cfg(...)]` attribute, if present (None for final `else`).
    pub cfg_attr: Option<ast::Attribute>,
    /// Span of the `else` keyword (for detecting comments around it).
    pub else_span: Option<Span>,
    /// Span of the `if` keyword (for detecting comments before it).
    pub if_span: Option<Span>,
    /// Span of the opening `{` token.
    pub open_brace_span: Span,
    /// Span of the closing `}` token.
    pub close_brace_span: Span,
}

/// Parse `cfg_if!` macro for formatting purposes.
/// Returns the list of branches with their conditions and items.
pub(crate) fn parse_cfg_if_for_format(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<Vec<CfgIfBranch>> {
    match catch_unwind(AssertUnwindSafe(|| {
        parse_cfg_if_for_format_inner(context, ts)
    })) {
        Ok(result) => result,
        Err(..) => None,
    }
}

fn parse_cfg_if_for_format_inner(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<Vec<CfgIfBranch>> {
    let mut parser = super::build_parser(context, ts);
    let mut branches = Vec::new();
    let mut is_first = true;
    let mut pending_else_span: Option<Span> = None;

    while parser.token.kind != TokenKind::Eof {
        let (kind, cfg_attr, else_span, if_span) = if parser.token.is_keyword(kw::If) || is_first {
            // `if` or `else if` branch
            if !parser.eat_keyword(exp!(If)) {
                return None;
            }
            let if_span = parser.prev_token.span;

            if !matches!(parser.token.kind, TokenKind::Pound) {
                return None;
            }

            let attr = match parser
                .parse_attribute(rustc_parse::parser::attr::InnerAttrPolicy::Permitted)
            {
                Ok(attr) => attr,
                Err(err) => {
                    err.cancel();
                    parser.psess.dcx().reset_err_count();
                    return None;
                }
            };

            let kind = if is_first {
                CfgIfBranchKind::If
            } else {
                CfgIfBranchKind::ElseIf
            };
            (kind, Some(attr), pending_else_span.take(), Some(if_span))
        } else {
            // Final `else` branch (no condition)
            (CfgIfBranchKind::Else, None, pending_else_span.take(), None)
        };

        is_first = false;

        // Expect `{`
        if !parser.eat(exp!(OpenBrace)) {
            return None;
        }
        let open_brace_span = parser.prev_token.span;

        // Skip over the body content by matching braces
        let mut brace_depth = 1;
        while brace_depth > 0 && parser.token.kind != TokenKind::Eof {
            match parser.token.kind {
                TokenKind::OpenDelim(Delimiter::Brace) => brace_depth += 1,
                TokenKind::CloseDelim(Delimiter::Brace) => brace_depth -= 1,
                _ => {}
            }
            if brace_depth > 0 {
                parser.bump();
            }
        }

        // Expect `}`
        if !parser.eat(exp!(CloseBrace)) {
            return None;
        }
        let close_brace_span = parser.prev_token.span;

        branches.push(CfgIfBranch {
            kind,
            cfg_attr,
            else_span,
            if_span,
            open_brace_span,
            close_brace_span,
        });

        // Check for end or `else`
        if parser.token.kind == TokenKind::Eof {
            break;
        }

        if !parser.eat_keyword(exp!(Else)) {
            return None;
        }
        // Capture else span for the next branch
        pending_else_span = Some(parser.prev_token.span);
    }

    Some(branches)
}
