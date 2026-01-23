//! Parser for `select!` and `select_biased!` (futures crate) and `select_loop!`
//! (commonware-macros).

use rustc_ast::token::{self, TokenKind};
use rustc_ast::tokenstream::TokenStream;
use rustc_ast::{ast, ptr};
use rustc_parse::exp;
use rustc_parse::parser::Parser;
use rustc_span::Span;

use crate::rewrite::RewriteContext;

/// Try to parse an expression, returning `None` on error and resetting error state.
fn try_parse_expr(parser: &mut Parser<'_>) -> Option<ptr::P<ast::Expr>> {
    match parser.parse_expr() {
        Ok(expr) if parser.psess.dcx().has_errors().is_none() => Some(expr),
        Ok(_) => {
            parser.psess.dcx().reset_err_count();
            None
        }
        Err(err) => {
            err.cancel();
            parser.psess.dcx().reset_err_count();
            None
        }
    }
}

/// Try to parse a pattern, returning `None` on error and resetting error state.
fn try_parse_pat(parser: &mut Parser<'_>) -> Option<ptr::P<ast::Pat>> {
    match parser.parse_pat_no_top_alt(None, None) {
        Ok(pat) if parser.psess.dcx().has_errors().is_none() => Some(pat),
        Ok(_) => {
            parser.psess.dcx().reset_err_count();
            None
        }
        Err(err) => {
            err.cancel();
            parser.psess.dcx().reset_err_count();
            None
        }
    }
}

fn is_ident(parser: &Parser<'_>, name: &str) -> bool {
    matches!(parser.token.kind, TokenKind::Ident(sym, _) if sym.as_str() == name)
}

/// Result of trying to parse a keyword arm.
enum KeywordArmResult {
    /// Not a keyword arm (keyword not present or not followed by `=>`).
    /// No tokens consumed.
    NotKeyword,
    /// Successfully parsed `keyword => body [,]`.
    /// Contains the span from keyword to end of body (including optional comma) and the body expr.
    Parsed { span: Span, body: ptr::P<ast::Expr> },
    /// Matched `keyword =>` but failed to parse body.
    /// Tokens were consumed; caller should fail the whole macro parse.
    BodyFailed,
}

/// Try to parse `keyword => expr [,]`.
/// Non-destructive if keyword is not followed by `=>`.
/// If keyword is followed by `=>`, tokens are consumed and body is parsed.
fn try_parse_keyword_arm(parser: &mut Parser<'_>, keyword: &str) -> KeywordArmResult {
    // Only match if keyword is followed by `=>`
    if !is_ident(parser, keyword) {
        return KeywordArmResult::NotKeyword;
    }
    if !parser.look_ahead(1, |t| *t == TokenKind::FatArrow) {
        return KeywordArmResult::NotKeyword;
    }
    // Committed to parsing keyword arm
    let lo = parser.token.span.lo();
    parser.bump(); // keyword
    parser.bump(); // =>
    match try_parse_expr(parser) {
        Some(body) => {
            let body_hi = parser.prev_token.span.hi();
            let _ = parser.eat(exp!(Comma));
            let span = Span::new(lo, body_hi, body.span.ctxt(), None);
            KeywordArmResult::Parsed { span, body }
        }
        None => KeywordArmResult::BodyFailed,
    }
}

/// A pattern branch: `pattern = future_expr [else diverge] => body`.
pub(crate) struct SelectBranch {
    /// Span from pattern start to body end (excluding trailing comma).
    pub span: Span,
    pub pattern: ptr::P<ast::Pat>,
    pub future_expr: ptr::P<ast::Expr>,
    /// Optional diverging expression for let-else patterns (e.g., `else break`).
    pub else_diverge: Option<ptr::P<ast::Expr>>,
    pub body: ptr::P<ast::Expr>,
}

/// An item in a `select!` macro.
pub(crate) enum SelectItem {
    /// `pattern = future_expr [else diverge] => body`
    Branch(SelectBranch),
    /// `default => body` or `complete => body`
    Keyword {
        span: Span,
        keyword: &'static str,
        body: ptr::P<ast::Expr>,
    },
}

impl SelectItem {
    pub(crate) fn span(&self) -> Span {
        match self {
            SelectItem::Branch(branch) => branch.span,
            SelectItem::Keyword { span, .. } => *span,
        }
    }
}

/// Parse `pattern = future_expr [else diverge] => body [,]`.
/// Returns `None` if `=` is missing (only keyword arms can omit `=`).
fn parse_branch(parser: &mut Parser<'_>) -> Option<SelectBranch> {
    let lo = parser.token.span.lo();
    let pattern = try_parse_pat(parser)?;

    // Require `=` for regular branches (only keyword arms can omit it)
    if !parser.eat(exp!(Eq)) {
        return None;
    }
    let future_expr = try_parse_expr(parser)?;

    // Optional `else diverge` for let-else patterns
    let else_diverge = if parser.eat_keyword(exp!(Else)) {
        Some(try_parse_expr(parser)?)
    } else {
        None
    };

    if !parser.eat(exp!(FatArrow)) {
        return None;
    }

    let body = try_parse_expr(parser)?;
    let body_hi = parser.prev_token.span.hi();
    let _ = parser.eat(exp!(Comma));

    Some(SelectBranch {
        span: Span::new(lo, body_hi, body.span.ctxt(), None),
        pattern,
        future_expr,
        else_diverge,
        body,
    })
}

/// Parse the contents of a select! or select_biased! macro.
pub(crate) fn parse_select(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<Vec<SelectItem>> {
    let mut result = vec![];
    let mut parser = super::build_parser(context, ts);

    while parser.token.kind != token::Eof {
        // Check for keyword arms: `default => body` or `complete => body`
        match try_parse_keyword_arm(&mut parser, "default") {
            KeywordArmResult::Parsed { span, body } => {
                result.push(SelectItem::Keyword {
                    span,
                    keyword: "default",
                    body,
                });
                continue;
            }
            KeywordArmResult::BodyFailed => return None,
            KeywordArmResult::NotKeyword => {}
        }
        match try_parse_keyword_arm(&mut parser, "complete") {
            KeywordArmResult::Parsed { span, body } => {
                result.push(SelectItem::Keyword {
                    span,
                    keyword: "complete",
                    body,
                });
                continue;
            }
            KeywordArmResult::BodyFailed => return None,
            KeywordArmResult::NotKeyword => {}
        }

        result.push(SelectItem::Branch(parse_branch(&mut parser)?));
    }

    Some(result)
}

/// An item in `select_loop!`: either a keyword arm or a regular branch.
pub(crate) enum SelectLoopItem {
    OnStart { span: Span, body: ptr::P<ast::Expr> },
    OnStopped { span: Span, body: ptr::P<ast::Expr> },
    Branch(SelectBranch),
    OnEnd { span: Span, body: ptr::P<ast::Expr> },
}

impl SelectLoopItem {
    pub(crate) fn span(&self) -> Span {
        match self {
            SelectLoopItem::OnStart { span, .. } => *span,
            SelectLoopItem::OnStopped { span, .. } => *span,
            SelectLoopItem::Branch(branch) => branch.span,
            SelectLoopItem::OnEnd { span, .. } => *span,
        }
    }
}

/// Parsed `select_loop!` macro: `context_expr, items...`
pub(crate) struct SelectLoop {
    pub context_expr: ptr::P<ast::Expr>,
    /// Span of the context expression (for comment extraction).
    pub context_span: Span,
    pub items: Vec<SelectLoopItem>,
}

/// Parse `select_loop!` contents. Returns `None` if `on_stopped` is missing or
/// any keyword is duplicated.
pub(crate) fn parse_select_loop(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<SelectLoop> {
    let mut parser = super::build_parser(context, ts);

    let context_expr = try_parse_expr(&mut parser)?;
    let context_span = context_expr.span;
    if !parser.eat(exp!(Comma)) {
        return None;
    }

    let mut items = vec![];
    let mut has_on_start = false;
    let mut has_on_stopped = false;
    let mut has_on_end = false;

    while parser.token.kind != token::Eof {
        match try_parse_keyword_arm(&mut parser, "on_start") {
            KeywordArmResult::Parsed { span, body } => {
                if has_on_start {
                    return None;
                }
                items.push(SelectLoopItem::OnStart { span, body });
                has_on_start = true;
                continue;
            }
            KeywordArmResult::BodyFailed => return None,
            KeywordArmResult::NotKeyword => {}
        }

        match try_parse_keyword_arm(&mut parser, "on_stopped") {
            KeywordArmResult::Parsed { span, body } => {
                if has_on_stopped {
                    return None;
                }
                items.push(SelectLoopItem::OnStopped { span, body });
                has_on_stopped = true;
                continue;
            }
            KeywordArmResult::BodyFailed => return None,
            KeywordArmResult::NotKeyword => {}
        }

        match try_parse_keyword_arm(&mut parser, "on_end") {
            KeywordArmResult::Parsed { span, body } => {
                if has_on_end {
                    return None;
                }
                items.push(SelectLoopItem::OnEnd { span, body });
                has_on_end = true;
                continue;
            }
            KeywordArmResult::BodyFailed => return None,
            KeywordArmResult::NotKeyword => {}
        }

        items.push(SelectLoopItem::Branch(parse_branch(&mut parser)?));
    }

    if !has_on_stopped {
        return None;
    }

    Some(SelectLoop {
        context_expr,
        context_span,
        items,
    })
}
