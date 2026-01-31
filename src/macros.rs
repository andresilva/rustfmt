// Format list-like macro invocations. These are invocations whose token trees
// can be interpreted as expressions and separated by commas.
// Note that these token trees do not actually have to be interpreted as
// expressions by the compiler. An example of an invocation we would reformat is
// foo!( x, y, z ). The token x may represent an identifier in the code, but we
// interpreted as an expression.
// Macro uses which are not-list like, such as bar!(key => val), will not be
// reformatted.
// List-like invocations with parentheses will be formatted as function calls,
// and those with brackets will be formatted as array literals.

use std::collections::HashMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_ast::token::{Delimiter, Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenStreamIter, TokenTree};
use rustc_ast::{ast, ptr};
use rustc_ast_pretty::pprust;
use rustc_span::{BytePos, DUMMY_SP, Ident, Span, Symbol};
use tracing::debug;

use crate::comment::{
    CharClasses, FindUncommented, FullCodeCharKind, LineClasses, contains_comment,
};
use crate::config::lists::*;
use crate::config::{ControlBraceStyle, StyleEdition};
use crate::expr::{
    ExprType, RhsAssignKind, RhsTactics, format_expr, prefer_next_line, rewrite_array,
    rewrite_assign_rhs,
};
use crate::lists::{ListFormatting, itemize_list, write_list};
use crate::matches::{flatten_arm_body_for_select, nop_block_collapse};
use crate::overflow;
use crate::parse::macros::cfg_if::{CfgIfBranch, CfgIfBranchKind, parse_cfg_if_for_format};
use crate::parse::macros::lazy_static::parse_lazy_static;
use crate::parse::macros::select::{
    SelectBranch, SelectItem, SelectLoopItem, parse_select, parse_select_loop,
};
use crate::parse::macros::{ParsedMacroArgs, parse_expr, parse_macro_args};
use crate::rewrite::{
    MacroErrorKind, Rewrite, RewriteContext, RewriteError, RewriteErrorExt, RewriteResult,
};
use crate::shape::{Indent, Shape};
use crate::source_map::SpanUtils;
use crate::spanned::Spanned;
use crate::utils::{
    NodeIdExt, extra_offset, filtered_str_fits, first_line_width, format_visibility,
    indent_next_line, is_empty_line, mk_sp, remove_trailing_white_spaces, rewrite_ident,
    trim_left_preserve_layout,
};
use crate::visitor::FmtVisitor;

const FORCED_BRACKET_MACROS: &[&str] = &["vec!"];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MacroPosition {
    Item,
    Statement,
    Expression,
    Pat,
}

#[derive(Debug)]
pub(crate) enum MacroArg {
    Expr(ptr::P<ast::Expr>),
    Ty(ptr::P<ast::Ty>),
    Pat(ptr::P<ast::Pat>),
    Item(ptr::P<ast::Item>),
    Keyword(Ident, Span),
}

impl MacroArg {
    pub(crate) fn is_item(&self) -> bool {
        match self {
            MacroArg::Item(..) => true,
            _ => false,
        }
    }
}

impl Rewrite for ast::Item {
    fn rewrite(&self, context: &RewriteContext<'_>, shape: Shape) -> Option<String> {
        self.rewrite_result(context, shape).ok()
    }

    fn rewrite_result(&self, context: &RewriteContext<'_>, shape: Shape) -> RewriteResult {
        let mut visitor = crate::visitor::FmtVisitor::from_context(context);
        visitor.block_indent = shape.indent;
        visitor.last_pos = self.span().lo();
        visitor.visit_item(self);
        Ok(visitor.buffer.to_owned())
    }
}

impl Rewrite for MacroArg {
    fn rewrite(&self, context: &RewriteContext<'_>, shape: Shape) -> Option<String> {
        self.rewrite_result(context, shape).ok()
    }

    fn rewrite_result(&self, context: &RewriteContext<'_>, shape: Shape) -> RewriteResult {
        match *self {
            MacroArg::Expr(ref expr) => expr.rewrite_result(context, shape),
            MacroArg::Ty(ref ty) => ty.rewrite_result(context, shape),
            MacroArg::Pat(ref pat) => pat.rewrite_result(context, shape),
            MacroArg::Item(ref item) => item.rewrite_result(context, shape),
            MacroArg::Keyword(ident, _) => Ok(ident.name.to_string()),
        }
    }
}

/// Rewrite macro name without using pretty-printer if possible.
fn rewrite_macro_name(context: &RewriteContext<'_>, path: &ast::Path) -> String {
    if path.segments.len() == 1 {
        // Avoid using pretty-printer in the common case.
        format!("{}!", rewrite_ident(context, path.segments[0].ident))
    } else {
        format!("{}!", pprust::path_to_string(path))
    }
}

// Use this on failing to format the macro call.
// TODO(ding-young) We should also report macro parse failure to tell users why given snippet
// is left unformatted. One possible improvement is appending formatting error to context.report
fn return_macro_parse_failure_fallback(
    context: &RewriteContext<'_>,
    indent: Indent,
    position: MacroPosition,
    span: Span,
) -> RewriteResult {
    // Mark this as a failure however we format it
    context.macro_rewrite_failure.replace(true);

    // Heuristically determine whether the last line of the macro uses "Block" style
    // rather than using "Visual" style, or another indentation style.
    let is_like_block_indent_style = context
        .snippet(span)
        .lines()
        .last()
        .map(|closing_line| {
            closing_line
                .trim()
                .chars()
                .all(|ch| matches!(ch, '}' | ')' | ']'))
        })
        .unwrap_or(false);
    if is_like_block_indent_style {
        return trim_left_preserve_layout(context.snippet(span), indent, context.config)
            .macro_error(MacroErrorKind::Unknown, span);
    }

    context.skipped_range.borrow_mut().push((
        context.psess.line_of_byte_pos(span.lo()),
        context.psess.line_of_byte_pos(span.hi()),
    ));

    // Return the snippet unmodified if the macro is not block-like
    let mut snippet = context.snippet(span).to_owned();
    if position == MacroPosition::Item {
        snippet.push(';');
    }
    Ok(snippet)
}

pub(crate) fn rewrite_macro(
    mac: &ast::MacCall,
    context: &RewriteContext<'_>,
    shape: Shape,
    position: MacroPosition,
) -> RewriteResult {
    let should_skip = context
        .skip_context
        .macros
        .skip(context.snippet(mac.path.span));
    if should_skip {
        Err(RewriteError::SkipFormatting)
    } else {
        let guard = context.enter_macro();
        let result = catch_unwind(AssertUnwindSafe(|| {
            rewrite_macro_inner(mac, context, shape, position, guard.is_nested())
        }));
        match result {
            Err(..) => {
                context.macro_rewrite_failure.replace(true);
                Err(RewriteError::MacroFailure {
                    kind: MacroErrorKind::Unknown,
                    span: mac.span(),
                })
            }
            Ok(Err(e)) => {
                context.macro_rewrite_failure.replace(true);
                Err(e)
            }
            Ok(rw) => rw,
        }
    }
}

fn rewrite_macro_inner(
    mac: &ast::MacCall,
    context: &RewriteContext<'_>,
    shape: Shape,
    position: MacroPosition,
    is_nested_macro: bool,
) -> RewriteResult {
    if context.config.use_try_shorthand() {
        if let Some(expr) = convert_try_mac(mac, context) {
            context.leave_macro();
            return expr.rewrite_result(context, shape);
        }
    }

    let original_style = macro_style(mac, context);

    let macro_name = rewrite_macro_name(context, &mac.path);
    let is_forced_bracket = FORCED_BRACKET_MACROS.contains(&&macro_name[..]);

    let style = if is_forced_bracket && !is_nested_macro {
        Delimiter::Bracket
    } else {
        original_style
    };

    let ts = mac.args.tokens.clone();
    let has_comment = contains_comment(context.snippet(mac.span()));
    if ts.is_empty() && !has_comment {
        return match style {
            Delimiter::Parenthesis if position == MacroPosition::Item => {
                Ok(format!("{macro_name}();"))
            }
            Delimiter::Bracket if position == MacroPosition::Item => Ok(format!("{macro_name}[];")),
            Delimiter::Parenthesis => Ok(format!("{macro_name}()")),
            Delimiter::Bracket => Ok(format!("{macro_name}[]")),
            Delimiter::Brace => Ok(format!("{macro_name} {{}}")),
            _ => unreachable!(),
        };
    }
    // Format well-known macros which cannot be parsed as a valid AST.
    if (macro_name == "lazy_static!"
        || (context.config.style_edition() >= StyleEdition::Edition2027
            && macro_name == "lazy_static::lazy_static!"))
        && !has_comment
    {
        match format_lazy_static(context, shape, ts.clone(), mac.span(), &macro_name) {
            Ok(rw) => return Ok(rw),
            Err(err) => match err {
                // We will move on to parsing macro args just like other macros
                // if we could not parse lazy_static! with known syntax
                RewriteError::MacroFailure { kind, span: _ }
                    if kind == MacroErrorKind::ParseFailure => {}
                // If formatting fails even though parsing succeeds, return the err early
                _ => return Err(err),
            },
        }
    }

    // Format select!, select_biased! macros from futures crate
    if matches!(
        macro_name.as_str(),
        "select!"
            | "select_biased!"
            | "futures::select!"
            | "futures::select_biased!"
            | "futures_util::select!"
            | "futures_util::select_biased!"
    ) && original_style == Delimiter::Brace
    {
        match format_select_macro(context, shape, ts.clone(), mac.span(), &macro_name) {
            Ok(rw) => return Ok(rw),
            Err(err) => match err {
                RewriteError::MacroFailure { kind, span: _ }
                    if kind == MacroErrorKind::ParseFailure => {}
                _ => return Err(err),
            },
        }
    }

    // Format select_loop! macro (has different syntax with context and special blocks)
    if matches!(
        macro_name.as_str(),
        "select_loop!" | "commonware_macros::select_loop!"
    ) && original_style == Delimiter::Brace
    {
        match format_select_loop_macro(context, shape, ts.clone(), mac.span(), &macro_name) {
            Ok(rw) => return Ok(rw),
            Err(err) => match err {
                RewriteError::MacroFailure { kind, span: _ }
                    if kind == MacroErrorKind::ParseFailure => {}
                _ => return Err(err),
            },
        }
    }

    // Format cfg_if! macro (in item or statement position with brace delimiters)
    if matches!(macro_name.as_str(), "cfg_if!" | "cfg_if::cfg_if!")
        && original_style == Delimiter::Brace
        && matches!(position, MacroPosition::Item | MacroPosition::Statement)
    {
        match format_cfg_if_macro(context, shape, ts.clone(), mac.span(), &macro_name) {
            Ok(rw) => return Ok(rw),
            Err(err) => match err {
                RewriteError::MacroFailure { kind, span: _ }
                    if kind == MacroErrorKind::ParseFailure => {}
                _ => return Err(err),
            },
        }
    }

    let ParsedMacroArgs {
        args: arg_vec,
        vec_with_semi,
        trailing_comma,
    } = match parse_macro_args(context, ts, style, is_forced_bracket) {
        Some(args) => args,
        None => {
            return return_macro_parse_failure_fallback(
                context,
                shape.indent,
                position,
                mac.span(),
            );
        }
    };

    if !arg_vec.is_empty() && arg_vec.iter().all(MacroArg::is_item) {
        return rewrite_macro_with_items(
            context,
            &arg_vec,
            &macro_name,
            shape,
            style,
            original_style,
            position,
            mac.span(),
        );
    }

    match style {
        Delimiter::Parenthesis => {
            // Handle special case: `vec!(expr; expr)`
            if vec_with_semi {
                handle_vec_semi(context, shape, arg_vec, macro_name, style, mac.span())
            } else {
                // Format macro invocation as function call, preserve the trailing
                // comma because not all macros support them.
                overflow::rewrite_with_parens(
                    context,
                    &macro_name,
                    arg_vec.iter(),
                    shape,
                    mac.span(),
                    context.config.fn_call_width(),
                    if trailing_comma {
                        Some(SeparatorTactic::Always)
                    } else {
                        Some(SeparatorTactic::Never)
                    },
                )
                .map(|rw| match position {
                    MacroPosition::Item => format!("{};", rw),
                    _ => rw,
                })
            }
        }
        Delimiter::Bracket => {
            // Handle special case: `vec![expr; expr]`
            if vec_with_semi {
                handle_vec_semi(context, shape, arg_vec, macro_name, style, mac.span())
            } else {
                // If we are rewriting `vec!` macro or other special macros,
                // then we can rewrite this as a usual array literal.
                // Otherwise, we must preserve the original existence of trailing comma.
                let mut force_trailing_comma = if trailing_comma {
                    Some(SeparatorTactic::Always)
                } else {
                    Some(SeparatorTactic::Never)
                };
                if is_forced_bracket && !is_nested_macro {
                    context.leave_macro();
                    if context.use_block_indent() {
                        force_trailing_comma = Some(SeparatorTactic::Vertical);
                    };
                }
                let rewrite = rewrite_array(
                    &macro_name,
                    arg_vec.iter(),
                    mac.span(),
                    context,
                    shape,
                    force_trailing_comma,
                    Some(original_style),
                )?;
                let comma = match position {
                    MacroPosition::Item => ";",
                    _ => "",
                };

                Ok(format!("{rewrite}{comma}"))
            }
        }
        Delimiter::Brace => {
            // For macro invocations with braces, always put a space between
            // the `macro_name!` and `{ /* macro_body */ }` but skip modifying
            // anything in between the braces (for now).
            let snippet = context.snippet(mac.span()).trim_start_matches(|c| c != '{');
            match trim_left_preserve_layout(snippet, shape.indent, context.config) {
                Some(macro_body) => Ok(format!("{macro_name} {macro_body}")),
                None => Ok(format!("{macro_name} {snippet}")),
            }
        }
        _ => unreachable!(),
    }
}

fn handle_vec_semi(
    context: &RewriteContext<'_>,
    shape: Shape,
    arg_vec: Vec<MacroArg>,
    macro_name: String,
    delim_token: Delimiter,
    span: Span,
) -> RewriteResult {
    let (left, right) = match delim_token {
        Delimiter::Parenthesis => ("(", ")"),
        Delimiter::Bracket => ("[", "]"),
        _ => unreachable!(),
    };

    // Should we return MaxWidthError, Or Macro failure
    let mac_shape = shape.offset_left(macro_name.len(), span)?;
    // 8 = `vec![]` + `; ` or `vec!()` + `; `
    let total_overhead = 8;
    let nested_shape = mac_shape.block_indent(context.config.tab_spaces());
    let lhs = arg_vec[0].rewrite_result(context, nested_shape)?;
    let rhs = arg_vec[1].rewrite_result(context, nested_shape)?;
    if !lhs.contains('\n')
        && !rhs.contains('\n')
        && lhs.len() + rhs.len() + total_overhead <= shape.width
    {
        // macro_name(lhs; rhs) or macro_name[lhs; rhs]
        Ok(format!("{macro_name}{left}{lhs}; {rhs}{right}"))
    } else {
        // macro_name(\nlhs;\nrhs\n) or macro_name[\nlhs;\nrhs\n]
        Ok(format!(
            "{}{}{}{};{}{}{}{}",
            macro_name,
            left,
            nested_shape.indent.to_string_with_newline(context.config),
            lhs,
            nested_shape.indent.to_string_with_newline(context.config),
            rhs,
            shape.indent.to_string_with_newline(context.config),
            right
        ))
    }
}

fn rewrite_empty_macro_def_body(
    context: &RewriteContext<'_>,
    span: Span,
    shape: Shape,
) -> RewriteResult {
    // Create an empty, dummy `ast::Block` representing an empty macro body
    let block = ast::Block {
        stmts: vec![].into(),
        id: rustc_ast::node_id::DUMMY_NODE_ID,
        rules: ast::BlockCheckMode::Default,
        span,
        tokens: None,
    };
    block.rewrite_result(context, shape)
}

pub(crate) fn rewrite_macro_def(
    context: &RewriteContext<'_>,
    shape: Shape,
    indent: Indent,
    def: &ast::MacroDef,
    ident: Ident,
    vis: &ast::Visibility,
    span: Span,
) -> RewriteResult {
    let snippet = Ok(remove_trailing_white_spaces(context.snippet(span)));
    if snippet.as_ref().map_or(true, |s| s.ends_with(';')) {
        return snippet;
    }

    let ts = def.body.tokens.clone();
    let mut parser = MacroParser::new(ts.iter());
    let parsed_def = match parser.parse() {
        Some(def) => def,
        None => return snippet,
    };

    let mut result = if def.macro_rules {
        String::from("macro_rules!")
    } else {
        format!("{}macro", format_visibility(context, vis))
    };

    result += " ";
    result += rewrite_ident(context, ident);

    let multi_branch_style = def.macro_rules || parsed_def.branches.len() != 1;

    let arm_shape = if multi_branch_style {
        shape
            .block_indent(context.config.tab_spaces())
            .with_max_width(context.config)
    } else {
        shape
    };

    if parsed_def.branches.len() == 0 {
        let lo = context.snippet_provider.span_before(span, "{");
        result += " ";
        result += &rewrite_empty_macro_def_body(context, span.with_lo(lo), shape)?;
        return Ok(result);
    }

    let branch_items = itemize_list(
        context.snippet_provider,
        parsed_def.branches.iter(),
        "}",
        ";",
        |branch| branch.span.lo(),
        |branch| branch.span.hi(),
        |branch| match branch.rewrite(context, arm_shape, multi_branch_style) {
            Ok(v) => Ok(v),
            // if the rewrite returned None because a macro could not be rewritten, then return the
            // original body
            // TODO(ding-young) report rewrite error even if we return Ok with original snippet
            Err(_) if context.macro_rewrite_failure.get() => {
                Ok(context.snippet(branch.body).trim().to_string())
            }
            Err(e) => Err(e),
        },
        context.snippet_provider.span_after(span, "{"),
        span.hi(),
        false,
    )
    .collect::<Vec<_>>();

    let fmt = ListFormatting::new(arm_shape, context.config)
        .separator(if def.macro_rules { ";" } else { "" })
        .trailing_separator(SeparatorTactic::Always)
        .preserve_newline(true);

    if multi_branch_style {
        result += " {";
        result += &arm_shape.indent.to_string_with_newline(context.config);
    }

    match write_list(&branch_items, &fmt) {
        Ok(ref s) => result += s,
        Err(_) => return snippet,
    }

    if multi_branch_style {
        result += &indent.to_string_with_newline(context.config);
        result += "}";
    }

    Ok(result)
}

fn register_metavariable(
    map: &mut HashMap<String, String>,
    result: &mut String,
    name: &str,
    dollar_count: usize,
) {
    let mut new_name = "$".repeat(dollar_count - 1);
    let mut old_name = "$".repeat(dollar_count);

    new_name.push('z');
    new_name.push_str(name);
    old_name.push_str(name);

    result.push_str(&new_name);
    map.insert(old_name, new_name);
}

// Replaces `$foo` with `zfoo`. We must check for name overlap to ensure we
// aren't causing problems.
// This should also work for escaped `$` variables, where we leave earlier `$`s.
fn replace_names(input: &str) -> Option<(String, HashMap<String, String>)> {
    // Each substitution will require five or six extra bytes.
    let mut result = String::with_capacity(input.len() + 64);
    let mut substs = HashMap::new();
    let mut dollar_count = 0;
    let mut cur_name = String::new();

    for (kind, c) in CharClasses::new(input.chars()) {
        if kind != FullCodeCharKind::Normal {
            result.push(c);
        } else if c == '$' {
            dollar_count += 1;
        } else if dollar_count == 0 {
            result.push(c);
        } else if !c.is_alphanumeric() && !cur_name.is_empty() {
            // Terminates a name following one or more dollars.
            register_metavariable(&mut substs, &mut result, &cur_name, dollar_count);

            result.push(c);
            dollar_count = 0;
            cur_name.clear();
        } else if c == '(' && cur_name.is_empty() {
            // FIXME: Support macro def with repeat.
            return None;
        } else if c.is_alphanumeric() || c == '_' {
            cur_name.push(c);
        }
    }

    if !cur_name.is_empty() {
        register_metavariable(&mut substs, &mut result, &cur_name, dollar_count);
    }

    debug!("replace_names `{}` {:?}", result, substs);

    Some((result, substs))
}

#[derive(Debug, Clone)]
enum MacroArgKind {
    /// e.g., `$x: expr`.
    MetaVariable(Symbol, String),
    /// e.g., `$($foo: expr),*`
    Repeat(
        /// `()`, `[]` or `{}`.
        Delimiter,
        /// Inner arguments inside delimiters.
        Vec<ParsedMacroArg>,
        /// Something after the closing delimiter and the repeat token, if available.
        Option<Box<ParsedMacroArg>>,
        /// The repeat token. This could be one of `*`, `+` or `?`.
        Token,
    ),
    /// e.g., `[derive(Debug)]`
    Delimited(Delimiter, Vec<ParsedMacroArg>),
    /// A possible separator. e.g., `,` or `;`.
    Separator(String, String),
    /// Other random stuff that does not fit to other kinds.
    /// e.g., `== foo` in `($x: expr == foo)`.
    Other(String, String),
}

fn delim_token_to_str(
    context: &RewriteContext<'_>,
    delim_token: Delimiter,
    shape: Shape,
    use_multiple_lines: bool,
    inner_is_empty: bool,
) -> (String, String) {
    let (lhs, rhs) = match delim_token {
        Delimiter::Parenthesis => ("(", ")"),
        Delimiter::Bracket => ("[", "]"),
        Delimiter::Brace => {
            if inner_is_empty || use_multiple_lines {
                ("{", "}")
            } else {
                ("{ ", " }")
            }
        }
        Delimiter::Invisible(_) => unreachable!(),
    };
    if use_multiple_lines {
        let indent_str = shape.indent.to_string_with_newline(context.config);
        let nested_indent_str = shape
            .indent
            .block_indent(context.config)
            .to_string_with_newline(context.config);
        (
            format!("{lhs}{nested_indent_str}"),
            format!("{indent_str}{rhs}"),
        )
    } else {
        (lhs.to_owned(), rhs.to_owned())
    }
}

impl MacroArgKind {
    fn starts_with_brace(&self) -> bool {
        matches!(
            *self,
            MacroArgKind::Repeat(Delimiter::Brace, _, _, _)
                | MacroArgKind::Delimited(Delimiter::Brace, _)
        )
    }

    fn starts_with_dollar(&self) -> bool {
        matches!(
            *self,
            MacroArgKind::Repeat(..) | MacroArgKind::MetaVariable(..)
        )
    }

    fn ends_with_space(&self) -> bool {
        matches!(*self, MacroArgKind::Separator(..))
    }

    fn has_meta_var(&self) -> bool {
        match *self {
            MacroArgKind::MetaVariable(..) => true,
            MacroArgKind::Repeat(_, ref args, _, _) => args.iter().any(|a| a.kind.has_meta_var()),
            _ => false,
        }
    }

    fn rewrite(
        &self,
        context: &RewriteContext<'_>,
        shape: Shape,
        use_multiple_lines: bool,
    ) -> RewriteResult {
        type DelimitedArgsRewrite = Result<(String, String, String), RewriteError>;
        let rewrite_delimited_inner = |delim_tok, args| -> DelimitedArgsRewrite {
            let inner = wrap_macro_args(context, args, shape)?;
            let (lhs, rhs) = delim_token_to_str(context, delim_tok, shape, false, inner.is_empty());
            if lhs.len() + inner.len() + rhs.len() <= shape.width {
                return Ok((lhs, inner, rhs));
            }

            let (lhs, rhs) = delim_token_to_str(context, delim_tok, shape, true, false);
            let nested_shape = shape
                .block_indent(context.config.tab_spaces())
                .with_max_width(context.config);
            let inner = wrap_macro_args(context, args, nested_shape)?;
            Ok((lhs, inner, rhs))
        };

        match *self {
            MacroArgKind::MetaVariable(ty, ref name) => Ok(format!("${name}:{ty}")),
            MacroArgKind::Repeat(delim_tok, ref args, ref another, ref tok) => {
                let (lhs, inner, rhs) = rewrite_delimited_inner(delim_tok, args)?;
                let another = another
                    .as_ref()
                    .and_then(|a| a.rewrite(context, shape, use_multiple_lines).ok())
                    .unwrap_or_else(|| "".to_owned());
                let repeat_tok = pprust::token_to_string(tok);

                Ok(format!("${lhs}{inner}{rhs}{another}{repeat_tok}"))
            }
            MacroArgKind::Delimited(delim_tok, ref args) => {
                rewrite_delimited_inner(delim_tok, args)
                    .map(|(lhs, inner, rhs)| format!("{}{}{}", lhs, inner, rhs))
            }
            MacroArgKind::Separator(ref sep, ref prefix) => Ok(format!("{prefix}{sep} ")),
            MacroArgKind::Other(ref inner, ref prefix) => Ok(format!("{prefix}{inner}")),
        }
    }
}

#[derive(Debug, Clone)]
struct ParsedMacroArg {
    kind: MacroArgKind,
}

impl ParsedMacroArg {
    fn rewrite(
        &self,
        context: &RewriteContext<'_>,
        shape: Shape,
        use_multiple_lines: bool,
    ) -> RewriteResult {
        self.kind.rewrite(context, shape, use_multiple_lines)
    }
}

/// Parses macro arguments on macro def.
struct MacroArgParser {
    /// Either a name of the next metavariable, a separator, or junk.
    buf: String,
    /// The first token of the current buffer.
    start_tok: Token,
    /// `true` if we are parsing a metavariable or a repeat.
    is_meta_var: bool,
    /// The last token parsed.
    last_tok: Token,
    /// Holds the parsed arguments.
    result: Vec<ParsedMacroArg>,
}

fn last_tok(tt: &TokenTree) -> Token {
    match *tt {
        TokenTree::Token(ref t, _) => t.clone(),
        TokenTree::Delimited(delim_span, _, delim, _) => Token {
            kind: TokenKind::CloseDelim(delim),
            span: delim_span.close,
        },
    }
}

impl MacroArgParser {
    fn new() -> MacroArgParser {
        MacroArgParser {
            buf: String::new(),
            is_meta_var: false,
            last_tok: Token {
                kind: TokenKind::Eof,
                span: DUMMY_SP,
            },
            start_tok: Token {
                kind: TokenKind::Eof,
                span: DUMMY_SP,
            },
            result: vec![],
        }
    }

    fn set_last_tok(&mut self, tok: &TokenTree) {
        self.last_tok = last_tok(tok);
    }

    fn add_separator(&mut self) {
        let prefix = if self.need_space_prefix() {
            " ".to_owned()
        } else {
            "".to_owned()
        };
        self.result.push(ParsedMacroArg {
            kind: MacroArgKind::Separator(self.buf.clone(), prefix),
        });
        self.buf.clear();
    }

    fn add_other(&mut self) {
        let prefix = if self.need_space_prefix() {
            " ".to_owned()
        } else {
            "".to_owned()
        };
        self.result.push(ParsedMacroArg {
            kind: MacroArgKind::Other(self.buf.clone(), prefix),
        });
        self.buf.clear();
    }

    fn add_meta_variable(&mut self, iter: &mut TokenStreamIter<'_>) -> Option<()> {
        match iter.next() {
            Some(&TokenTree::Token(
                Token {
                    kind: TokenKind::Ident(name, _),
                    ..
                },
                _,
            )) => {
                self.result.push(ParsedMacroArg {
                    kind: MacroArgKind::MetaVariable(name, self.buf.clone()),
                });

                self.buf.clear();
                self.is_meta_var = false;
                Some(())
            }
            _ => None,
        }
    }

    fn add_delimited(&mut self, inner: Vec<ParsedMacroArg>, delim: Delimiter) {
        self.result.push(ParsedMacroArg {
            kind: MacroArgKind::Delimited(delim, inner),
        });
    }

    // $($foo: expr),?
    fn add_repeat(
        &mut self,
        inner: Vec<ParsedMacroArg>,
        delim: Delimiter,
        iter: &mut TokenStreamIter<'_>,
    ) -> Option<()> {
        let mut buffer = String::new();
        let mut first = true;

        // Parse '*', '+' or '?.
        for tok in iter {
            self.set_last_tok(&tok);
            if first {
                first = false;
            }

            match tok {
                TokenTree::Token(
                    Token {
                        kind: TokenKind::Plus,
                        ..
                    },
                    _,
                )
                | TokenTree::Token(
                    Token {
                        kind: TokenKind::Question,
                        ..
                    },
                    _,
                )
                | TokenTree::Token(
                    Token {
                        kind: TokenKind::Star,
                        ..
                    },
                    _,
                ) => {
                    break;
                }
                TokenTree::Token(ref t, _) => {
                    buffer.push_str(&pprust::token_to_string(t));
                }
                _ => return None,
            }
        }

        // There could be some random stuff between ')' and '*', '+' or '?'.
        let another = if buffer.trim().is_empty() {
            None
        } else {
            Some(Box::new(ParsedMacroArg {
                kind: MacroArgKind::Other(buffer, "".to_owned()),
            }))
        };

        self.result.push(ParsedMacroArg {
            kind: MacroArgKind::Repeat(delim, inner, another, self.last_tok.clone()),
        });
        Some(())
    }

    fn update_buffer(&mut self, t: &Token) {
        if self.buf.is_empty() {
            self.start_tok = t.clone();
        } else {
            let needs_space = match next_space(&self.last_tok.kind) {
                SpaceState::Ident => ident_like(t),
                SpaceState::Punctuation => !ident_like(t),
                SpaceState::Always => true,
                SpaceState::Never => false,
            };
            if force_space_before(&t.kind) || needs_space {
                self.buf.push(' ');
            }
        }

        self.buf.push_str(&pprust::token_to_string(t));
    }

    fn need_space_prefix(&self) -> bool {
        if self.result.is_empty() {
            return false;
        }

        let last_arg = self.result.last().unwrap();
        if let MacroArgKind::MetaVariable(..) = last_arg.kind {
            if ident_like(&self.start_tok) {
                return true;
            }
            if self.start_tok.kind == TokenKind::Colon {
                return true;
            }
        }

        if force_space_before(&self.start_tok.kind) {
            return true;
        }

        false
    }

    /// Returns a collection of parsed macro def's arguments.
    fn parse(mut self, tokens: TokenStream) -> Option<Vec<ParsedMacroArg>> {
        let mut iter = tokens.iter();

        while let Some(tok) = iter.next() {
            match tok {
                &TokenTree::Token(
                    Token {
                        kind: TokenKind::Dollar,
                        span,
                    },
                    _,
                ) => {
                    // We always want to add a separator before meta variables.
                    if !self.buf.is_empty() {
                        self.add_separator();
                    }

                    // Start keeping the name of this metavariable in the buffer.
                    self.is_meta_var = true;
                    self.start_tok = Token {
                        kind: TokenKind::Dollar,
                        span,
                    };
                }
                TokenTree::Token(
                    Token {
                        kind: TokenKind::Colon,
                        ..
                    },
                    _,
                ) if self.is_meta_var => {
                    self.add_meta_variable(&mut iter)?;
                }
                TokenTree::Token(ref t, _) => self.update_buffer(t),
                &TokenTree::Delimited(_dspan, _spacing, delimited, ref tts) => {
                    if !self.buf.is_empty() {
                        if next_space(&self.last_tok.kind) == SpaceState::Always {
                            self.add_separator();
                        } else {
                            self.add_other();
                        }
                    }

                    // Parse the stuff inside delimiters.
                    let parser = MacroArgParser::new();
                    let delimited_arg = parser.parse(tts.clone())?;

                    if self.is_meta_var {
                        self.add_repeat(delimited_arg, delimited, &mut iter)?;
                        self.is_meta_var = false;
                    } else {
                        self.add_delimited(delimited_arg, delimited);
                    }
                }
            }

            self.set_last_tok(&tok);
        }

        // We are left with some stuff in the buffer. Since there is nothing
        // left to separate, add this as `Other`.
        if !self.buf.is_empty() {
            self.add_other();
        }

        Some(self.result)
    }
}

fn wrap_macro_args(
    context: &RewriteContext<'_>,
    args: &[ParsedMacroArg],
    shape: Shape,
) -> RewriteResult {
    wrap_macro_args_inner(context, args, shape, false)
        .or_else(|_| wrap_macro_args_inner(context, args, shape, true))
}

fn wrap_macro_args_inner(
    context: &RewriteContext<'_>,
    args: &[ParsedMacroArg],
    shape: Shape,
    use_multiple_lines: bool,
) -> RewriteResult {
    let mut result = String::with_capacity(128);
    let mut iter = args.iter().peekable();
    let indent_str = shape.indent.to_string_with_newline(context.config);

    while let Some(arg) = iter.next() {
        result.push_str(&arg.rewrite(context, shape, use_multiple_lines)?);

        if use_multiple_lines
            && (arg.kind.ends_with_space() || iter.peek().map_or(false, |a| a.kind.has_meta_var()))
        {
            if arg.kind.ends_with_space() {
                result.pop();
            }
            result.push_str(&indent_str);
        } else if let Some(next_arg) = iter.peek() {
            let space_before_dollar =
                !arg.kind.ends_with_space() && next_arg.kind.starts_with_dollar();
            let space_before_brace = next_arg.kind.starts_with_brace();
            if space_before_dollar || space_before_brace {
                result.push(' ');
            }
        }
    }

    if !use_multiple_lines && result.len() >= shape.width {
        Err(RewriteError::Unknown)
    } else {
        Ok(result)
    }
}

// This is a bit sketchy. The token rules probably need tweaking, but it works
// for some common cases. I hope the basic logic is sufficient. Note that the
// meaning of some tokens is a bit different here from usual Rust, e.g., `*`
// and `(`/`)` have special meaning.
fn format_macro_args(
    context: &RewriteContext<'_>,
    token_stream: TokenStream,
    shape: Shape,
) -> RewriteResult {
    let span = span_for_token_stream(&token_stream);
    if !context.config.format_macro_matchers() {
        return Ok(match span {
            Some(span) => context.snippet(span).to_owned(),
            None => String::new(),
        });
    }
    let parsed_args = MacroArgParser::new()
        .parse(token_stream)
        .macro_error(MacroErrorKind::ParseFailure, span.unwrap())?;
    wrap_macro_args(context, &parsed_args, shape)
}

fn span_for_token_stream(token_stream: &TokenStream) -> Option<Span> {
    token_stream.iter().next().map(|tt| tt.span())
}

// We should insert a space if the next token is a:
#[derive(Copy, Clone, PartialEq)]
enum SpaceState {
    Never,
    Punctuation,
    Ident, // Or ident/literal-like thing.
    Always,
}

fn force_space_before(tok: &TokenKind) -> bool {
    debug!("tok: force_space_before {:?}", tok);

    match tok {
        TokenKind::Eq
        | TokenKind::Lt
        | TokenKind::Le
        | TokenKind::EqEq
        | TokenKind::Ne
        | TokenKind::Ge
        | TokenKind::Gt
        | TokenKind::AndAnd
        | TokenKind::OrOr
        | TokenKind::Bang
        | TokenKind::Tilde
        | TokenKind::PlusEq
        | TokenKind::MinusEq
        | TokenKind::StarEq
        | TokenKind::SlashEq
        | TokenKind::PercentEq
        | TokenKind::CaretEq
        | TokenKind::AndEq
        | TokenKind::OrEq
        | TokenKind::ShlEq
        | TokenKind::ShrEq
        | TokenKind::At
        | TokenKind::RArrow
        | TokenKind::LArrow
        | TokenKind::FatArrow
        | TokenKind::Plus
        | TokenKind::Minus
        | TokenKind::Star
        | TokenKind::Slash
        | TokenKind::Percent
        | TokenKind::Caret
        | TokenKind::And
        | TokenKind::Or
        | TokenKind::Shl
        | TokenKind::Shr
        | TokenKind::Pound
        | TokenKind::Dollar => true,
        _ => false,
    }
}

fn ident_like(tok: &Token) -> bool {
    matches!(
        tok.kind,
        TokenKind::Ident(..) | TokenKind::Literal(..) | TokenKind::Lifetime(..)
    )
}

fn next_space(tok: &TokenKind) -> SpaceState {
    debug!("next_space: {:?}", tok);

    match tok {
        TokenKind::Bang
        | TokenKind::And
        | TokenKind::Tilde
        | TokenKind::At
        | TokenKind::Comma
        | TokenKind::Dot
        | TokenKind::DotDot
        | TokenKind::DotDotDot
        | TokenKind::DotDotEq
        | TokenKind::Question => SpaceState::Punctuation,

        TokenKind::PathSep
        | TokenKind::Pound
        | TokenKind::Dollar
        | TokenKind::OpenDelim(_)
        | TokenKind::CloseDelim(_) => SpaceState::Never,

        TokenKind::Literal(..) | TokenKind::Ident(..) | TokenKind::Lifetime(..) => {
            SpaceState::Ident
        }

        _ => SpaceState::Always,
    }
}

/// Tries to convert a macro use into a short hand try expression. Returns `None`
/// when the macro is not an instance of `try!` (or parsing the inner expression
/// failed).
pub(crate) fn convert_try_mac(
    mac: &ast::MacCall,
    context: &RewriteContext<'_>,
) -> Option<ast::Expr> {
    let path = &pprust::path_to_string(&mac.path);
    if path == "try" || path == "r#try" {
        let ts = mac.args.tokens.clone();

        Some(ast::Expr {
            id: ast::NodeId::root(), // dummy value
            kind: ast::ExprKind::Try(parse_expr(context, ts)?),
            span: mac.span(), // incorrect span, but shouldn't matter too much
            attrs: ast::AttrVec::new(),
            tokens: None,
        })
    } else {
        None
    }
}

pub(crate) fn macro_style(mac: &ast::MacCall, context: &RewriteContext<'_>) -> Delimiter {
    let snippet = context.snippet(mac.span());
    let paren_pos = snippet.find_uncommented("(").unwrap_or(usize::MAX);
    let bracket_pos = snippet.find_uncommented("[").unwrap_or(usize::MAX);
    let brace_pos = snippet.find_uncommented("{").unwrap_or(usize::MAX);

    if paren_pos < bracket_pos && paren_pos < brace_pos {
        Delimiter::Parenthesis
    } else if bracket_pos < brace_pos {
        Delimiter::Bracket
    } else {
        Delimiter::Brace
    }
}

// A very simple parser that just parses a macros 2.0 definition into its branches.
// Currently we do not attempt to parse any further than that.
struct MacroParser<'a> {
    iter: TokenStreamIter<'a>,
}

impl<'a> MacroParser<'a> {
    const fn new(iter: TokenStreamIter<'a>) -> Self {
        Self { iter }
    }

    // (`(` ... `)` `=>` `{` ... `}`)*
    fn parse(&mut self) -> Option<Macro> {
        let mut branches = vec![];
        while self.iter.peek().is_some() {
            branches.push(self.parse_branch()?);
        }

        Some(Macro { branches })
    }

    // `(` ... `)` `=>` `{` ... `}`
    fn parse_branch(&mut self) -> Option<MacroBranch> {
        let tok = self.iter.next()?;
        let (lo, args_paren_kind) = match tok {
            TokenTree::Token(..) => return None,
            &TokenTree::Delimited(delimited_span, _, d, _) => (delimited_span.open.lo(), d),
        };
        let args = TokenStream::new(vec![tok.clone()]);
        match self.iter.next()? {
            TokenTree::Token(
                Token {
                    kind: TokenKind::FatArrow,
                    ..
                },
                _,
            ) => {}
            _ => return None,
        }
        let (mut hi, body, whole_body) = match self.iter.next()? {
            TokenTree::Token(..) => return None,
            TokenTree::Delimited(delimited_span, ..) => {
                let data = delimited_span.entire().data();
                (
                    data.hi,
                    Span::new(
                        data.lo + BytePos(1),
                        data.hi - BytePos(1),
                        data.ctxt,
                        data.parent,
                    ),
                    delimited_span.entire(),
                )
            }
        };
        if let Some(TokenTree::Token(
            Token {
                kind: TokenKind::Semi,
                span,
            },
            _,
        )) = self.iter.peek()
        {
            hi = span.hi();
            self.iter.next();
        }
        Some(MacroBranch {
            span: mk_sp(lo, hi),
            args_paren_kind,
            args,
            body,
            whole_body,
        })
    }
}

// A parsed macros 2.0 macro definition.
struct Macro {
    branches: Vec<MacroBranch>,
}

// FIXME: it would be more efficient to use references to the token streams
// rather than clone them, if we can make the borrowing work out.
struct MacroBranch {
    span: Span,
    args_paren_kind: Delimiter,
    args: TokenStream,
    body: Span,
    whole_body: Span,
}

impl MacroBranch {
    fn rewrite(
        &self,
        context: &RewriteContext<'_>,
        shape: Shape,
        multi_branch_style: bool,
    ) -> RewriteResult {
        // Only attempt to format function-like macros.
        if self.args_paren_kind != Delimiter::Parenthesis {
            // FIXME(#1539): implement for non-sugared macros.
            return Err(RewriteError::MacroFailure {
                kind: MacroErrorKind::Unknown,
                span: self.span,
            });
        }

        let old_body = context.snippet(self.body).trim();
        let has_block_body = old_body.starts_with('{');
        let mut prefix_width = 5; // 5 = " => {"
        if context.config.style_edition() >= StyleEdition::Edition2024 {
            if has_block_body {
                prefix_width = 6; // 6 = " => {{"
            }
        }
        let mut result = format_macro_args(
            context,
            self.args.clone(),
            shape.sub_width(prefix_width, self.span)?,
        )?;

        if multi_branch_style {
            result += " =>";
        }

        if !context.config.format_macro_bodies() {
            result += " ";
            result += context.snippet(self.whole_body);
            return Ok(result);
        }

        // The macro body is the most interesting part. It might end up as various
        // AST nodes, but also has special variables (e.g, `$foo`) which can't be
        // parsed as regular Rust code (and note that these can be escaped using
        // `$$`). We'll try and format like an AST node, but we'll substitute
        // variables for new names with the same length first.

        let (body_str, substs) =
            replace_names(old_body).macro_error(MacroErrorKind::ReplaceMacroVariable, self.span)?;

        let mut config = context.config.clone();
        config.set().show_parse_errors(false);

        result += " {";

        let body_indent = if has_block_body {
            shape.indent
        } else {
            shape.indent.block_indent(&config)
        };
        let new_width = config.max_width() - body_indent.width();
        config.set().max_width(new_width);

        // First try to format as items, then as statements.
        let new_body_snippet = match crate::format_snippet(&body_str, &config, true) {
            Some(new_body) => new_body,
            None => {
                let new_width = new_width + config.tab_spaces();
                config.set().max_width(new_width);
                match crate::format_code_block(&body_str, &config, true) {
                    Some(new_body) => new_body,
                    None => {
                        return Err(RewriteError::MacroFailure {
                            kind: MacroErrorKind::Unknown,
                            span: self.span,
                        });
                    }
                }
            }
        };

        if !filtered_str_fits(&new_body_snippet.snippet, config.max_width(), shape) {
            return Err(RewriteError::ExceedsMaxWidth {
                configured_width: shape.width,
                span: self.span,
            });
        }

        // Indent the body since it is in a block.
        let indent_str = body_indent.to_string(&config);
        let mut new_body = LineClasses::new(new_body_snippet.snippet.trim_end())
            .enumerate()
            .fold(
                (String::new(), true),
                |(mut s, need_indent), (i, (kind, ref l))| {
                    if !is_empty_line(l)
                        && need_indent
                        && !new_body_snippet.is_line_non_formatted(i + 1)
                    {
                        s += &indent_str;
                    }
                    (s + l + "\n", indent_next_line(kind, l, &config))
                },
            )
            .0;

        // Undo our replacement of macro variables.
        // FIXME: this could be *much* more efficient.
        for (old, new) in &substs {
            if old_body.contains(new) {
                debug!("rewrite_macro_def: bailing matching variable: `{}`", new);
                return Err(RewriteError::MacroFailure {
                    kind: MacroErrorKind::ReplaceMacroVariable,
                    span: self.span,
                });
            }
            new_body = new_body.replace(new, old);
        }

        if has_block_body {
            result += new_body.trim();
        } else if !new_body.is_empty() {
            result += "\n";
            result += &new_body;
            result += &shape.indent.to_string(&config);
        }

        result += "}";

        Ok(result)
    }
}

/// Format `lazy_static!` and `lazy_static::lazy_static!`
/// from <https://crates.io/crates/lazy_static>.
///
/// # Expected syntax
///
/// ```text
/// lazy_static! {
///     [pub] static ref NAME_1: TYPE_1 = EXPR_1;
///     [pub] static ref NAME_2: TYPE_2 = EXPR_2;
///     ...
///     [pub] static ref NAME_N: TYPE_N = EXPR_N;
/// }
///
/// lazy_static::lazy_static! {
///     [pub] static ref NAME_1: TYPE_1 = EXPR_1;
///     [pub] static ref NAME_2: TYPE_2 = EXPR_2;
///     ...
///     [pub] static ref NAME_N: TYPE_N = EXPR_N;
/// }
/// ```
fn format_lazy_static(
    context: &RewriteContext<'_>,
    shape: Shape,
    ts: TokenStream,
    span: Span,
    macro_name: &str,
) -> RewriteResult {
    let mut result = String::with_capacity(1024);
    let nested_shape = shape
        .block_indent(context.config.tab_spaces())
        .with_max_width(context.config);

    result.push_str(macro_name);
    result.push_str(" {");
    result.push_str(&nested_shape.indent.to_string_with_newline(context.config));

    let parsed_elems =
        parse_lazy_static(context, ts).macro_error(MacroErrorKind::ParseFailure, span)?;
    let last = parsed_elems.len() - 1;
    for (i, (vis, id, ty, expr)) in parsed_elems.iter().enumerate() {
        // Rewrite as a static item.
        let vis = crate::utils::format_visibility(context, vis);
        let mut stmt = String::with_capacity(128);
        stmt.push_str(&format!(
            "{}static ref {}: {} =",
            vis,
            id,
            ty.rewrite_result(context, nested_shape)?
        ));
        result.push_str(&rewrite_assign_rhs(
            context,
            stmt,
            &*expr,
            &RhsAssignKind::Expr(&expr.kind, expr.span),
            nested_shape.sub_width(1, expr.span)?,
        )?);
        result.push(';');
        if i != last {
            result.push_str(&nested_shape.indent.to_string_with_newline(context.config));
        }
    }

    result.push_str(&shape.indent.to_string_with_newline(context.config));
    result.push('}');

    Ok(result)
}

/// Format `prefix => body,` with proper line wrapping.
/// Mirrors match arm formatting logic from src/matches.rs.
fn format_arm(
    context: &RewriteContext<'_>,
    prefix: &str,
    body: &ast::Expr,
    shape: Shape,
) -> RewriteResult {
    // Use extra_offset to avoid double-counting indentation for multiline prefixes
    let body_shape = shape
        .offset_left_opt(extra_offset(prefix, shape) + 4) // 4 = " => "
        .and_then(|s| s.sub_width_opt(1)); // 1 = ","

    // extend=false means prefer next line (e.g., force_multiline_blocks was set)
    let (extend, flattened) = flatten_arm_body_for_select(context, body, body_shape);
    let is_block = matches!(flattened.kind, ast::ExprKind::Block(..));

    // Honor control_brace_style for blocks (like match arms do)
    let force_next_line_brace =
        is_block && context.config.control_brace_style() == ControlBraceStyle::AlwaysNextLine;

    // For blocks with AlwaysNextLine, format at current indent level (like match arms)
    if force_next_line_brace {
        let block_sep = shape.indent.to_string_with_newline(context.config);
        let body_str = format_expr(flattened, ExprType::Statement, context, shape)?;
        return Ok(format!("{} =>{}{},", prefix, block_sep, body_str));
    }

    // Helper closures for combining prefix with body
    let combine_same_line = |body_str: &str| format!("{} => {},", prefix, body_str);
    let combine_next_line_block = |body_str: &str| {
        // For blocks, just put on next line
        let next_line_indent = shape
            .block_indent(context.config.tab_spaces())
            .indent
            .to_string_with_newline(context.config);
        format!("{} =>{}{},", prefix, next_line_indent, body_str)
    };
    let combine_next_line_nonblock = |body_str: &str| {
        // For non-blocks, wrap in { } if match_arm_blocks is true (like match arms do)
        if context.config.match_arm_blocks() {
            let indent_str = shape.indent.to_string_with_newline(context.config);
            let nested_indent_str = shape
                .block_indent(context.config.tab_spaces())
                .indent
                .to_string_with_newline(context.config);
            let block_trailing_comma = if context.config.match_block_trailing_comma() {
                ","
            } else {
                ""
            };
            format!(
                "{} => {{{}{}{}}}{},",
                prefix, nested_indent_str, body_str, indent_str, block_trailing_comma
            )
        } else {
            let next_line_indent = shape
                .block_indent(context.config.tab_spaces())
                .indent
                .to_string_with_newline(context.config);
            format!("{} =>{}{},", prefix, next_line_indent, body_str)
        }
    };

    // Try same-line formatting (mirroring matches.rs lines 552-557)
    // Wrap with nop_block_collapse to collapse empty blocks to {}
    let orig_body = body_shape
        .map(|bs| {
            nop_block_collapse(
                format_expr(flattened, ExprType::Statement, context, bs),
                bs.width,
            )
        })
        .unwrap_or(Err(RewriteError::Unknown));

    // Early return for blocks or simple expressions that fit on one line
    if let Ok(ref body_str) = orig_body {
        if let Some(bs) = body_shape {
            if is_block || (!body_str.contains('\n') && first_line_width(body_str) <= bs.width) {
                return Ok(combine_same_line(body_str));
            }
        }
    }

    // Try next-line formatting
    let next_line_shape = shape.block_indent(context.config.tab_spaces());
    let next_line_body = nop_block_collapse(
        format_expr(flattened, ExprType::Statement, context, next_line_shape),
        next_line_shape.width,
    );

    // Helper to choose the right next-line combiner based on whether body is a block
    let combine_next_line = |body_str: &str| {
        if is_block {
            combine_next_line_block(body_str)
        } else {
            combine_next_line_nonblock(body_str)
        }
    };

    // Choose between same-line and next-line using prefer_next_line heuristic
    // (mirroring matches.rs lines 572-589)
    match (&orig_body, &next_line_body) {
        (Ok(orig_str), Ok(next_line_str))
            if prefer_next_line(orig_str, next_line_str, RhsTactics::Default) =>
        {
            Ok(combine_next_line(next_line_str))
        }
        (Ok(orig_str), _)
            if extend && body_shape.is_some_and(|bs| first_line_width(orig_str) <= bs.width) =>
        {
            Ok(combine_same_line(orig_str))
        }
        (Ok(orig_str), Ok(next_line_str)) if orig_str.contains('\n') => {
            Ok(combine_next_line(next_line_str))
        }
        (Err(_), Ok(next_line_str)) => Ok(combine_next_line(next_line_str)),
        (Err(_), Err(e)) => Err(e.clone()),
        (Ok(orig_str), _) => Ok(combine_same_line(orig_str)),
    }
}

/// Format a select branch: `pattern = future_expr [else diverge] => body,`
fn format_select_branch(
    context: &RewriteContext<'_>,
    branch: &SelectBranch,
    shape: Shape,
) -> RewriteResult {
    let pat_str = branch.pattern.rewrite_result(context, shape)?;
    let expr_shape = shape
        .offset_left_opt(extra_offset(&pat_str, shape) + 3) // 3 = " = "
        .unwrap_or(shape);
    let expr_str = branch.future_expr.rewrite_result(context, expr_shape)?;

    let prefix = if let Some(ref else_diverge) = branch.else_diverge {
        // Format: `pattern = future_expr else diverge`
        // 6 = " else "
        let else_shape = shape
            .offset_left_opt(extra_offset(&pat_str, shape) + 3 + extra_offset(&expr_str, shape) + 6)
            .unwrap_or(shape);
        let else_str = else_diverge.rewrite_result(context, else_shape)?;
        format!("{} = {} else {}", pat_str, expr_str, else_str)
    } else {
        format!("{} = {}", pat_str, expr_str)
    };
    format_arm(context, &prefix, &branch.body, shape)
}

/// Format `select!` and `select_biased!` macros.
///
/// Supports `pattern = future [else diverge] => body`, `default => body`, and `complete => body`.
/// Falls back to default formatting for unsupported syntax (e.g., tokio guards).
fn format_select_macro(
    context: &RewriteContext<'_>,
    shape: Shape,
    ts: TokenStream,
    span: Span,
    macro_name: &str,
) -> RewriteResult {
    let items = parse_select(context, ts).macro_error(MacroErrorKind::ParseFailure, span)?;

    if items.is_empty() {
        return Ok(format!("{} {{}}", macro_name));
    }

    let nested_shape = shape
        .block_indent(context.config.tab_spaces())
        .with_max_width(context.config);

    // Use itemize_list to preserve comments between items
    let open_brace_pos = context.snippet_provider.span_after(span, "{");
    let item_list = itemize_list(
        context.snippet_provider,
        items.iter(),
        "}",
        ",",
        |item| item.span().lo(),
        |item| item.span().hi(),
        |item| match item {
            SelectItem::Branch(branch) => format_select_branch(context, branch, nested_shape),
            SelectItem::Keyword { body, keyword, .. } => {
                format_arm(context, keyword, body, nested_shape)
            }
        },
        open_brace_pos,
        span.hi(),
        false,
    )
    .collect::<Vec<_>>();

    let fmt = ListFormatting::new(nested_shape, context.config)
        .separator("")
        .preserve_newline(true);

    let items_str = write_list(&item_list, &fmt)?;

    let mut result = String::with_capacity(256);
    result.push_str(macro_name);
    result.push_str(" {");
    result.push_str(&nested_shape.indent.to_string_with_newline(context.config));
    result.push_str(&items_str);
    result.push_str(&shape.indent.to_string_with_newline(context.config));
    result.push('}');

    Ok(result)
}

/// Format `select_loop!` macro.
///
/// Items are output in the order they appear in source, preserving the user's layout.
fn format_select_loop_macro(
    context: &RewriteContext<'_>,
    shape: Shape,
    ts: TokenStream,
    span: Span,
    macro_name: &str,
) -> RewriteResult {
    let select_loop =
        parse_select_loop(context, ts).macro_error(MacroErrorKind::ParseFailure, span)?;

    let nested_shape = shape
        .block_indent(context.config.tab_spaces())
        .with_max_width(context.config);

    let mut result = String::with_capacity(512);
    result.push_str(macro_name);
    result.push_str(" {");

    // Format context expression
    result.push_str(&nested_shape.indent.to_string_with_newline(context.config));
    let context_str = select_loop
        .context_expr
        .rewrite_result(context, nested_shape)?;
    result.push_str(&context_str);
    result.push(',');

    if select_loop.items.is_empty() {
        result.push_str(&shape.indent.to_string_with_newline(context.config));
        result.push('}');
        return Ok(result);
    }

    // Use itemize_list to preserve comments between items
    // The prev_span_end starts after the comma following the context expression
    // This ensures comments between the comma and first item are captured
    let after_context_comma = context.snippet_provider.span_after(
        Span::new(select_loop.context_span.hi(), span.hi(), span.ctxt(), None),
        ",",
    );
    let item_list = itemize_list(
        context.snippet_provider,
        select_loop.items.iter(),
        "}",
        ",",
        |item| item.span().lo(),
        |item| item.span().hi(),
        |item| match item {
            SelectLoopItem::OnStart { body, .. } => {
                format_arm(context, "on_start", body, nested_shape)
            }
            SelectLoopItem::OnStopped { body, .. } => {
                format_arm(context, "on_stopped", body, nested_shape)
            }
            SelectLoopItem::OnEnd { body, .. } => format_arm(context, "on_end", body, nested_shape),
            SelectLoopItem::Branch(branch) => format_select_branch(context, branch, nested_shape),
        },
        after_context_comma,
        span.hi(),
        false,
    )
    .collect::<Vec<_>>();

    let fmt = ListFormatting::new(nested_shape, context.config)
        .separator("")
        .preserve_newline(true);

    let items_str = write_list(&item_list, &fmt)?;

    result.push_str(&nested_shape.indent.to_string_with_newline(context.config));
    result.push_str(&items_str);
    result.push_str(&shape.indent.to_string_with_newline(context.config));
    result.push('}');

    Ok(result)
}

/// Format `cfg_if!` macro.
///
/// # Expected syntax
///
/// ```text
/// cfg_if! {
///     if #[cfg(condition1)] { // optional trailing comment
///         // items
///     } else if #[cfg(condition2)] {
///         // items
///     } else { // optional trailing comment
///         // items
///     }
/// }
/// ```
fn format_cfg_if_macro(
    context: &RewriteContext<'_>,
    shape: Shape,
    ts: TokenStream,
    span: Span,
    macro_name: &str,
) -> RewriteResult {
    let branches =
        parse_cfg_if_for_format(context, ts).macro_error(MacroErrorKind::ParseFailure, span)?;

    if branches.is_empty() {
        return Ok(format!("{} {{}}", macro_name));
    }

    // Check for comments at branch seams that would be lost during formatting.
    // If found, bail out and let the default macro formatter handle it.
    if has_comments_at_branch_seams(context, &branches) {
        return Err(RewriteError::MacroFailure {
            kind: MacroErrorKind::ParseFailure,
            span,
        });
    }

    let nested_shape = shape
        .block_indent(context.config.tab_spaces())
        .with_max_width(context.config);
    let body_shape = nested_shape
        .block_indent(context.config.tab_spaces())
        .with_max_width(context.config);

    let mut result = String::with_capacity(1024);
    result.push_str(macro_name);
    result.push_str(" {");

    for (i, branch) in branches.iter().enumerate() {
        result.push_str(&nested_shape.indent.to_string_with_newline(context.config));

        // Format branch header
        match branch.kind {
            CfgIfBranchKind::If => {
                result.push_str("if ");
            }
            CfgIfBranchKind::ElseIf => {
                result.push_str("} else if ");
            }
            CfgIfBranchKind::Else => {
                result.push_str("} else ");
            }
        }

        // Format the #[cfg(...)] attribute if present
        if let Some(ref attr) = branch.cfg_attr {
            let attr_str = attr
                .rewrite_result(context, nested_shape)
                .unwrap_or_else(|_| pprust::attribute_to_string(attr));
            result.push_str(&attr_str);
            result.push(' ');
        }

        result.push('{');

        // Extract trailing comment on the header line (after `{`)
        let trailing_comment =
            extract_trailing_comment(context, branch.open_brace_span, branch.close_brace_span);
        if let Some(ref comment) = trailing_comment {
            result.push(' ');
            result.push_str(comment);
        }

        // Format the branch body
        let body_span = mk_sp(branch.open_brace_span.hi(), branch.close_brace_span.lo());
        let body_snippet = context.snippet(body_span);

        // Skip trailing comment on first line if present
        let body_after_comment = if trailing_comment.is_some() {
            body_snippet
                .find('\n')
                .map(|i| &body_snippet[i + 1..])
                .unwrap_or("")
        } else {
            body_snippet
        };

        // Strip common leading indentation from all lines, but preserve string content
        // Use LineClasses to be string-aware (like trim_left_preserve_layout)
        let lines_with_kind: Vec<_> = LineClasses::new(body_after_comment).collect();

        // Helper to check if a line is inside string content (should not be modified)
        let is_string_content = |kind: &FullCodeCharKind| {
            matches!(
                kind,
                FullCodeCharKind::InString
                    | FullCodeCharKind::InStringCommented
                    | FullCodeCharKind::EndString
                    | FullCodeCharKind::EndStringCommented
            )
        };

        // Find minimum indent, excluding lines inside strings
        let min_indent = lines_with_kind
            .iter()
            .filter_map(|(kind, line)| {
                if line.trim().is_empty() || is_string_content(kind) {
                    return None;
                }
                Some(line.len() - line.trim_start().len())
            })
            .min()
            .unwrap_or(0);

        // Strip indent from code lines, but preserve string content lines exactly
        let body_str: String = lines_with_kind
            .iter()
            .map(|(kind, line)| {
                if is_string_content(kind) {
                    // Lines inside strings should be preserved exactly
                    line.to_owned()
                } else if line.trim().is_empty() {
                    "".to_owned()
                } else if line.len() > min_indent {
                    line[min_indent..].to_owned()
                } else {
                    line.trim_start().to_owned()
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let body_str = body_str.trim();

        if !body_str.is_empty() {
            // Set up config for formatting body. Reduce max_width by the body
            // indentation so formatted lines fit after indenting.
            let mut config = context.config.clone();
            config.set().show_parse_errors(false);
            let body_indent_width = body_shape.indent.width();
            let adjusted_max_width = context.config.max_width().saturating_sub(body_indent_width);
            config.set().max_width(adjusted_max_width);

            // First try to format as items, then as statements (like MacroBranch::rewrite)
            let new_body_snippet = match crate::format_snippet(body_str, &config, false) {
                Some(new_body) => Some(new_body),
                None => crate::format_code_block(body_str, &config, false),
            };
            if let Some(formatted) = new_body_snippet {
                // Indent the body since it is in a block (same approach as MacroBranch::rewrite)
                let indent_str = body_shape.indent.to_string(context.config);
                let new_body = LineClasses::new(formatted.snippet.trim_end())
                    .enumerate()
                    .fold(
                        (String::new(), true),
                        |(mut s, need_indent), (i, (kind, ref line))| {
                            if !is_empty_line(line)
                                && need_indent
                                && !formatted.is_line_non_formatted(i + 1)
                            {
                                s += "\n";
                                s += &indent_str;
                            } else if !s.is_empty() {
                                s += "\n";
                            }
                            (s + line, indent_next_line(kind, line, context.config))
                        },
                    )
                    .0;
                result.push_str(&new_body);
            } else {
                // Fallback: preserve original with proper indentation
                // body_str already has common indentation stripped
                for line in body_str.lines() {
                    if line.trim().is_empty() {
                        result.push('\n');
                    } else {
                        result.push_str(&body_shape.indent.to_string_with_newline(context.config));
                        result.push_str(line);
                    }
                }
            }
        }

        // Only close the last branch with a separate `}`
        if i == branches.len() - 1 {
            result.push_str(&nested_shape.indent.to_string_with_newline(context.config));
            result.push('}');
        }
    }

    result.push_str(&shape.indent.to_string_with_newline(context.config));
    result.push('}');

    Ok(result)
}

/// Check if there are comments at branch seams (between `}` and `else`, between `else` and `if`,
/// between `if` and `#[cfg(...)]`, or between `#[cfg(...)]` and `{`) that would be lost.
fn has_comments_at_branch_seams(context: &RewriteContext<'_>, branches: &[CfgIfBranch]) -> bool {
    for (i, branch) in branches.iter().enumerate() {
        // Check for comments between `if` and `#[cfg(...)]`
        if let (Some(if_span), Some(ref attr)) = (branch.if_span, &branch.cfg_attr) {
            let between = context.snippet(mk_sp(if_span.hi(), attr.span.lo()));
            if contains_comment(between) {
                return true;
            }
        }

        // Check for comments between `#[cfg(...)]` and `{`
        if let Some(ref attr) = branch.cfg_attr {
            let between = context.snippet(mk_sp(attr.span.hi(), branch.open_brace_span.lo()));
            if contains_comment(between) {
                return true;
            }
        }

        // Check for comments between previous branch's `}` and `else`
        if let Some(else_span) = branch.else_span {
            let prev_close = branches[i - 1].close_brace_span;
            let between = context.snippet(mk_sp(prev_close.hi(), else_span.lo()));
            if contains_comment(between) {
                return true;
            }
        }

        // Check for comments between `else` and `if` (for else-if branches)
        if let (Some(else_span), Some(if_span)) = (branch.else_span, branch.if_span) {
            let between = context.snippet(mk_sp(else_span.hi(), if_span.lo()));
            if contains_comment(between) {
                return true;
            }
        }

        // Check for comments between `else` and `{` (for final else branch)
        if branch.kind == CfgIfBranchKind::Else {
            if let Some(else_span) = branch.else_span {
                let between = context.snippet(mk_sp(else_span.hi(), branch.open_brace_span.lo()));
                if contains_comment(between) {
                    return true;
                }
            }
        }
    }
    false
}

/// Extract a trailing comment on the same line after an opening brace.
/// Returns Some(comment) if found, None otherwise.
fn extract_trailing_comment(
    context: &RewriteContext<'_>,
    open_brace_span: Span,
    close_brace_span: Span,
) -> Option<String> {
    let snippet = context.snippet(mk_sp(open_brace_span.hi(), close_brace_span.lo()));

    // Get the first line (everything up to the first newline)
    let first_line = snippet.lines().next().unwrap_or("");
    let trimmed = first_line.trim();

    if trimmed.is_empty() {
        return None;
    }

    // Check for // or /* comment
    if trimmed.starts_with("//") || trimmed.starts_with("/*") {
        Some(trimmed.to_string())
    } else {
        None
    }
}

fn rewrite_macro_with_items(
    context: &RewriteContext<'_>,
    items: &[MacroArg],
    macro_name: &str,
    shape: Shape,
    style: Delimiter,
    original_style: Delimiter,
    position: MacroPosition,
    span: Span,
) -> RewriteResult {
    let style_to_delims = |style| match style {
        Delimiter::Parenthesis => Ok(("(", ")")),
        Delimiter::Bracket => Ok(("[", "]")),
        Delimiter::Brace => Ok((" {", "}")),
        _ => Err(RewriteError::Unknown),
    };

    let (opener, closer) = style_to_delims(style)?;
    let (original_opener, _) = style_to_delims(original_style)?;
    let trailing_semicolon = match style {
        Delimiter::Parenthesis | Delimiter::Bracket if position == MacroPosition::Item => ";",
        _ => "",
    };

    let mut visitor = FmtVisitor::from_context(context);
    visitor.block_indent = shape.indent.block_indent(context.config);

    // The current opener may be different from the original opener. This can happen
    // if our macro is a forced bracket macro originally written with non-bracket
    // delimiters. We need to use the original opener to locate the span after it.
    visitor.last_pos = context
        .snippet_provider
        .span_after(span, original_opener.trim());
    for item in items {
        let item = match item {
            MacroArg::Item(item) => item,
            _ => return Err(RewriteError::Unknown),
        };
        visitor.visit_item(item);
    }

    let mut result = String::with_capacity(256);
    result.push_str(macro_name);
    result.push_str(opener);
    result.push_str(&visitor.block_indent.to_string_with_newline(context.config));
    result.push_str(visitor.buffer.trim());
    result.push_str(&shape.indent.to_string_with_newline(context.config));
    result.push_str(closer);
    result.push_str(trailing_semicolon);
    Ok(result)
}
