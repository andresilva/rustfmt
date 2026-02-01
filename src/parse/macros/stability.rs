use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_ast::ast;
use rustc_ast::token::{Delimiter, TokenKind};
use rustc_ast::tokenstream::TokenStream;
use rustc_parse::exp;
use rustc_parse::parser::ForceCollect;
use rustc_span::Span;

use crate::parse::macros::build_stream_parser;
use crate::parse::session::ParseSess;
use crate::rewrite::RewriteContext;

/// Parse `stability_mod!` macro for module resolution.
///
/// Expected syntax: `stability_mod!(LEVEL, pub mod name);`
///
/// Returns the module item if found.
pub(crate) fn parse_stability_mod<'a>(
    psess: &'a ParseSess,
    mac: &'a ast::MacCall,
) -> Result<Vec<ast::Item>, &'static str> {
    match catch_unwind(AssertUnwindSafe(|| parse_stability_mod_inner(psess, mac))) {
        Ok(Ok(items)) => Ok(items),
        Ok(err @ Err(_)) => err,
        Err(..) => Err("failed to parse stability_mod!"),
    }
}

fn parse_stability_mod_inner<'a>(
    psess: &'a ParseSess,
    mac: &'a ast::MacCall,
) -> Result<Vec<ast::Item>, &'static str> {
    let ts = mac.args.tokens.clone();
    let mut parser = build_stream_parser(psess.inner(), ts);

    // Skip tokens until we find a top-level comma (LEVEL, ...)
    // Track delimiter depth to avoid matching commas inside nested delimiters
    let mut depth: u32 = 0;
    while parser.token.kind != TokenKind::Eof {
        match parser.token.kind {
            TokenKind::OpenDelim(_) => depth += 1,
            TokenKind::CloseDelim(_) => depth = depth.saturating_sub(1),
            TokenKind::Comma if depth == 0 => break,
            _ => {}
        }
        parser.bump();
    }

    if !parser.eat(exp!(Comma)) {
        return Err("Expected comma after stability level");
    }

    // Guard: must have at least one token for the item
    if parser.token.kind == TokenKind::Eof {
        return Err("Expected item after comma in stability_mod!");
    }

    // Parse the item after the comma
    let mut items = vec![];
    let before_span = parser.token.span;
    let had_errors_before = parser.psess.dcx().has_errors().is_some();
    match parser.parse_item(ForceCollect::No) {
        Ok(Some(item_ptr)) => {
            // Reset error count if we introduced new errors during parsing (recovery case)
            if !had_errors_before && parser.psess.dcx().has_errors().is_some() {
                parser.psess.dcx().reset_err_count();
            }
            let item = item_ptr.into_inner();
            if let ast::ItemKind::Mod(..) = item.kind {
                items.push(item);
            }
        }
        Ok(None) => {
            // Reset error count only if we introduced new errors during parsing
            if !had_errors_before && parser.psess.dcx().has_errors().is_some() {
                parser.psess.dcx().reset_err_count();
            }
            if parser.token.span == before_span {
                return Err("Failed to parse item in stability_mod!");
            }
        }
        Err(err) => {
            err.cancel();
            // Reset error count only if we introduced new errors during parsing
            if !had_errors_before && parser.psess.dcx().has_errors().is_some() {
                parser.psess.dcx().reset_err_count();
            }
            return Err("Failed to parse item in stability_mod!");
        }
    }

    Ok(items)
}

/// Parse `stability_scope!` macro for module resolution.
///
/// Expected syntax:
/// - `stability_scope!(LEVEL { items });`
/// - `stability_scope!(LEVEL, cfg(predicate) { items });`
///
/// Returns all module items found inside the block.
pub(crate) fn parse_stability_scope<'a>(
    psess: &'a ParseSess,
    mac: &'a ast::MacCall,
) -> Result<Vec<ast::Item>, &'static str> {
    match catch_unwind(AssertUnwindSafe(|| parse_stability_scope_inner(psess, mac))) {
        Ok(Ok(items)) => Ok(items),
        Ok(err @ Err(_)) => err,
        Err(..) => Err("failed to parse stability_scope!"),
    }
}

fn parse_stability_scope_inner<'a>(
    psess: &'a ParseSess,
    mac: &'a ast::MacCall,
) -> Result<Vec<ast::Item>, &'static str> {
    let ts = mac.args.tokens.clone();
    let mut parser = build_stream_parser(psess.inner(), ts);

    // Skip tokens until we find a top-level opening brace (LEVEL { or LEVEL, cfg(...) {)
    // Track delimiter depth to find the correct top-level brace
    let mut depth: u32 = 0;
    while parser.token.kind != TokenKind::Eof {
        match parser.token.kind {
            TokenKind::OpenDelim(Delimiter::Brace) if depth == 0 => break,
            TokenKind::OpenDelim(_) => depth += 1,
            TokenKind::CloseDelim(_) => depth = depth.saturating_sub(1),
            _ => {}
        }
        parser.bump();
    }

    if !parser.eat(exp!(OpenBrace)) {
        return Err("Expected opening brace in stability_scope!");
    }

    let mut items = vec![];

    // Parse items inside the block
    while parser.token.kind != TokenKind::CloseDelim(Delimiter::Brace)
        && parser.token.kind != TokenKind::Eof
    {
        let before_span = parser.token.span;
        let had_errors_before = parser.psess.dcx().has_errors().is_some();
        let item = match parser.parse_item(ForceCollect::No) {
            Ok(Some(item_ptr)) => {
                // Reset error count if we introduced new errors during parsing (recovery case)
                if !had_errors_before && parser.psess.dcx().has_errors().is_some() {
                    parser.psess.dcx().reset_err_count();
                }
                item_ptr.into_inner()
            }
            Ok(None) => {
                // Reset error count only if we introduced new errors during parsing
                if !had_errors_before && parser.psess.dcx().has_errors().is_some() {
                    parser.psess.dcx().reset_err_count();
                }
                // Guard against infinite loop
                if parser.token.span == before_span {
                    parser.bump();
                }
                continue;
            }
            Err(err) => {
                err.cancel();
                // Reset error count only if we introduced new errors during parsing
                if !had_errors_before && parser.psess.dcx().has_errors().is_some() {
                    parser.psess.dcx().reset_err_count();
                }
                return Err("Expected item inside stability_scope block");
            }
        };
        if let ast::ItemKind::Mod(..) = item.kind {
            items.push(item);
        }
    }

    if !parser.eat(exp!(CloseBrace)) {
        return Err("Expected closing brace in stability_scope!");
    }

    Ok(items)
}

/// Parsed structure for formatting `stability_mod!` macro.
pub(crate) struct StabilityModFmt {
    /// Span of the stability level (e.g., ALPHA, BETA).
    pub level_span: Span,
    /// Span of the item (e.g., `pub mod name`).
    pub item_span: Span,
}

/// Parsed structure for formatting `stability_scope!` macro.
pub(crate) struct StabilityScopeFmt {
    /// Span of the stability level (e.g., ALPHA, BETA).
    pub level_span: Span,
    /// Span of the optional cfg predicate (e.g., `cfg(not(target_arch = "wasm32"))`).
    /// None if no cfg predicate is present.
    pub cfg_span: Option<Span>,
    /// Span of the opening `{` token.
    pub open_brace_span: Span,
    /// Span of the closing `}` token.
    pub close_brace_span: Span,
}

/// Parse `stability_mod!` macro for formatting purposes.
/// Returns the structure with spans needed for formatting.
pub(crate) fn parse_stability_mod_for_format(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<StabilityModFmt> {
    match catch_unwind(AssertUnwindSafe(|| {
        parse_stability_mod_for_format_inner(context, ts)
    })) {
        Ok(result) => result,
        Err(..) => None,
    }
}

fn parse_stability_mod_for_format_inner(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<StabilityModFmt> {
    let mut parser = super::build_parser(context, ts);

    // Record the start position for the level
    let level_start = parser.token.span;

    // Skip tokens until we find a top-level comma
    // Track delimiter depth to avoid matching commas inside nested delimiters
    let mut depth: u32 = 0;
    let mut found_tokens = false;
    while parser.token.kind != TokenKind::Eof {
        match parser.token.kind {
            TokenKind::OpenDelim(_) => depth += 1,
            TokenKind::CloseDelim(_) => depth = depth.saturating_sub(1),
            TokenKind::Comma if depth == 0 => break,
            _ => {}
        }
        found_tokens = true;
        parser.bump();
    }

    // Guard: must have found at least one token before comma
    if !found_tokens {
        return None;
    }

    // The level ends at the previous token (before the comma)
    let level_end = parser.prev_token.span;

    // Expect `,`
    if !parser.eat(exp!(Comma)) {
        return None;
    }

    // Record the start of the item
    let item_start = parser.token.span;

    // Guard: must have at least one token for the item (not immediately EOF)
    if parser.token.kind == TokenKind::Eof {
        return None;
    }

    // Skip to the end to find the item span
    while parser.token.kind != TokenKind::Eof {
        parser.bump();
    }
    let item_end = parser.prev_token.span;

    Some(StabilityModFmt {
        level_span: level_start.to(level_end),
        item_span: item_start.to(item_end),
    })
}

/// Parse `stability_scope!` macro for formatting purposes.
/// Returns the structure with spans needed for formatting.
pub(crate) fn parse_stability_scope_for_format(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<StabilityScopeFmt> {
    match catch_unwind(AssertUnwindSafe(|| {
        parse_stability_scope_for_format_inner(context, ts)
    })) {
        Ok(result) => result,
        Err(..) => None,
    }
}

fn parse_stability_scope_for_format_inner(
    context: &RewriteContext<'_>,
    ts: TokenStream,
) -> Option<StabilityScopeFmt> {
    let mut parser = super::build_parser(context, ts);

    // Record the start position for the level
    let level_start = parser.token.span;

    // First, scan for a top-level comma (which separates LEVEL from cfg(...))
    // Track delimiter depth to find the correct comma
    let mut depth: u32 = 0;
    let mut comma_found = false;
    let mut found_level_tokens = false;
    let mut level_end = parser.token.span;

    while parser.token.kind != TokenKind::Eof {
        match parser.token.kind {
            TokenKind::OpenDelim(Delimiter::Brace) if depth == 0 => break,
            TokenKind::OpenDelim(_) => depth += 1,
            TokenKind::CloseDelim(_) => depth = depth.saturating_sub(1),
            TokenKind::Comma if depth == 0 => {
                level_end = parser.prev_token.span;
                comma_found = true;
                parser.bump(); // consume the comma
                break;
            }
            _ => {}
        }
        level_end = parser.token.span;
        found_level_tokens = true;
        parser.bump();
    }

    // Guard: must have found at least one token for the level
    if !found_level_tokens {
        return None;
    }

    // If we found a comma, look for cfg(...) and then the brace
    let cfg_span = if comma_found {
        let cfg_start = parser.token.span;

        // Guard: if immediately followed by `{`, there's no cfg predicate (malformed input)
        if parser.token.kind == TokenKind::OpenDelim(Delimiter::Brace) {
            return None;
        }

        // Scan to the opening brace, tracking depth
        let mut found_cfg_tokens = false;
        depth = 0;
        while parser.token.kind != TokenKind::Eof {
            match parser.token.kind {
                TokenKind::OpenDelim(Delimiter::Brace) if depth == 0 => break,
                TokenKind::OpenDelim(_) => depth += 1,
                TokenKind::CloseDelim(_) => depth = depth.saturating_sub(1),
                _ => {}
            }
            found_cfg_tokens = true;
            parser.bump();
        }

        // Guard: must have found at least one token for the cfg
        if !found_cfg_tokens {
            return None;
        }

        let cfg_end = parser.prev_token.span;
        Some(cfg_start.to(cfg_end))
    } else {
        // No comma found, we already scanned to the brace
        None
    };

    // Compute level_span
    let level_span = if comma_found {
        level_start.to(level_end)
    } else {
        level_start.to(parser.prev_token.span)
    };

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

    Some(StabilityScopeFmt {
        level_span,
        cfg_span,
        open_brace_span,
        close_brace_span,
    })
}
