pub(crate) mod lexer;

use self::lexer::{Tok, Token};
use crate::ast::*;
use crate::diag::Span;
use std::rc::Rc;

fn flush_fn_groups(
    items: &mut Vec<Rc<Item>>,
    order: &mut Vec<(String, usize)>,
    groups: &mut std::collections::HashMap<(String, usize), FnDef>,
) {
    for key in order.drain(..) {
        if let Some(def) = groups.remove(&key) {
            items.push(Rc::new(Item::Fn(def)));
        }
    }
}

#[derive(Debug)]
pub struct ParseError {
    pub msg: String,
    pub span: Span,
    kind: ParseErrorKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ParseErrorKind {
    Syntax,
    Incomplete,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Plain-text fallback. The .20.6 renderer is the proper rendering
        // path; `to_diagnostic` is what the driver calls.
        write!(f, "parse error: {}", self.msg)
    }
}

impl ParseError {
    pub fn syntax(msg: impl Into<String>, span: Span) -> Self {
        Self {
            msg: msg.into(),
            span,
            kind: ParseErrorKind::Syntax,
        }
    }

    pub fn incomplete(msg: impl Into<String>, span: Span) -> Self {
        Self {
            msg: msg.into(),
            span,
            kind: ParseErrorKind::Incomplete,
        }
    }

    pub fn is_incomplete(&self) -> bool {
        self.kind == ParseErrorKind::Incomplete
    }

    /// Promote a parse-time error into a structured Diagnostic. v1 maps
    /// every parse error to `parse/expected-token`; later passes can
    /// refine to specific codes (duplicate-doc, unknown-attribute, …)
    /// at each call site once `self.err(..)` learns to pick codes.
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        crate::diag::Diagnostic::error(
            crate::diag::codes::PARSE_EXPECTED_TOKEN,
            self.msg.clone(),
            self.span,
        )
    }
}

pub struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// fz-rcp.1 — when true, the call-postfix `do … end` (and `,do:`)
    /// sugar in `parse_bp` is suppressed. Enabled by `with_no_trailing_do`
    /// around cond-position expressions: `if`/`case`/`cond`/`with`
    /// sources and `when`-guards. Without this, `if pred(h) do … end`
    /// parses `pred(h) do … end` as `pred(h, do_block)` and the
    /// surrounding `else`/`end` becomes unexpected.
    suppress_trailing_do: bool,
    /// fz-g58.2.3a — true while parsing a single element of a comma-delimited
    /// container (list/tuple/map/bitstring/parenthesized call args). A
    /// no-parens call recognized in that state takes a single argument and
    /// leaves the comma to the enclosing container, so `[foo a, b]` is
    /// `[foo(a), b]` rather than `[foo(a, b)]`. At statement/operand position
    /// (the default, and inside any nested block, lambda, or grouping) it is
    /// false, and a no-parens call greedily takes comma-separated args.
    comma_bound: bool,
    /// fz-g58.2.3b — set by the no-parens-call recognition site, read by the
    /// caller to learn whether the expression it just parsed was a bare call.
    /// The AST does not record parens-vs-no-parens (`bar x` and `bar(x)` are
    /// the same `Call`), so this transient flag carries that distinction to
    /// the ambiguity check in `parse_no_parens_keyword_list`.
    saw_no_parens_call: bool,
    /// fz-g58.2.3b — non-fatal diagnostics gathered during the parse. Emitted
    /// to telemetry by `parse_program_with_telemetry`; dropped on the plain
    /// `parse_program` path (warnings are observability, not control flow).
    warnings: Vec<crate::diag::Diagnostic>,
}

type PR<T> = Result<T, ParseError>;

const PARSE_PASS_NAME: &[&str] = &["fz", "parser", "pass"];
const ITEMS_BUILT_NAME: &[&str] = &["fz", "parser", "items_built"];
/// Diagnostic events under the `[fz, diag]` prefix are rendered by the
/// telemetry `DiagRenderer`; `warning` is the severity leaf.
const DIAG_WARNING_NAME: &[&str] = &["fz", "diag", "warning"];

impl Parser {
    pub fn new(toks: Vec<Token>) -> Self {
        Self {
            toks,
            pos: 0,
            suppress_trailing_do: false,
            comma_bound: false,
            saw_no_parens_call: false,
            warnings: Vec::new(),
        }
    }

    /// Record a non-fatal diagnostic. Surfaced via telemetry on the
    /// `parse_program_with_telemetry` path; otherwise collected and dropped.
    fn warn(&mut self, diag: crate::diag::Diagnostic) {
        self.warnings.push(diag);
    }

    /// Run `f` with the call-postfix trailing-do sugar suppressed.
    /// Restores the prior flag value on return (so nesting works).
    fn with_no_trailing_do<T>(&mut self, f: impl FnOnce(&mut Self) -> PR<T>) -> PR<T> {
        let prev = self.suppress_trailing_do;
        self.suppress_trailing_do = true;
        let r = f(self);
        self.suppress_trailing_do = prev;
        r
    }

    /// Run `f` while parsing a comma-delimited container element: a no-parens
    /// call recognized inside takes a single argument (see `comma_bound`).
    fn with_comma_bound<T>(&mut self, f: impl FnOnce(&mut Self) -> PR<T>) -> PR<T> {
        let prev = self.comma_bound;
        self.comma_bound = true;
        let r = f(self);
        self.comma_bound = prev;
        r
    }

    /// Run `f` in a fresh statement/operand context (block, lambda body, or
    /// grouping): a no-parens call recognized inside greedily takes
    /// comma-separated args, regardless of any enclosing container.
    fn with_comma_unbound<T>(&mut self, f: impl FnOnce(&mut Self) -> PR<T>) -> PR<T> {
        let prev = self.comma_bound;
        self.comma_bound = false;
        let r = f(self);
        self.comma_bound = prev;
        r
    }

    /// Whether trivia immediately precedes the token at `pos + off` (so the
    /// parser can read inter-token spacing for no-parens / dual-op decisions).
    fn space_before_at(&self, off: usize) -> bool {
        self.toks
            .get(self.pos + off)
            .map(|t| t.space_before)
            .unwrap_or(false)
    }

    // --- token helpers ---

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn peek_at(&self, off: usize) -> &Tok {
        self.toks
            .get(self.pos + off)
            .map(|t| &t.tok)
            .unwrap_or(&Tok::Eof)
    }
    fn cur_span(&self) -> Span {
        self.toks[self.pos].span
    }
    /// Span of the last consumed token. Used when closing out a parse fn:
    /// the construct spans from its starting token through the last token
    /// it consumed.
    fn prev_span(&self) -> Span {
        if self.pos == 0 {
            Span::DUMMY
        } else {
            self.toks[self.pos - 1].span
        }
    }
    /// Build a span from a starting span through the last consumed token.
    fn finish(&self, start: Span) -> Span {
        start.merge(self.prev_span())
    }
    fn err<T>(&self, msg: impl Into<String>) -> PR<T> {
        Err(ParseError::syntax(msg, self.cur_span()))
    }
    fn incomplete<T>(&self, msg: impl Into<String>) -> PR<T> {
        Err(ParseError::incomplete(msg, self.cur_span()))
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].tok.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: &Tok) -> bool {
        if self.at(t) {
            self.bump();
            true
        } else {
            false
        }
    }
    fn at(&self, t: &Tok) -> bool {
        std::mem::discriminant(self.peek()) == std::mem::discriminant(t)
    }
    fn bump_keyword_key(&mut self) -> PR<Spanned<String>> {
        let span = self.cur_span();
        match self.bump() {
            Tok::KwKey(key) => Ok(Spanned::new(key, span)),
            other => self.err(format!("expected keyword key, got {:?}", other)),
        }
    }
    fn continue_keyword_entries(&mut self, terminator: &Tok, positional_msg: &str) -> PR<bool> {
        self.skip_newlines();
        if !self.eat(&Tok::Comma) {
            return Ok(false);
        }
        self.skip_newlines();
        if self.at(terminator) {
            return Ok(false);
        }
        if !matches!(self.peek(), Tok::KwKey(_)) {
            return self.err(positional_msg);
        }
        Ok(true)
    }
    fn expect(&mut self, t: &Tok, what: &str) -> PR<()> {
        if self.eat(t) {
            Ok(())
        } else if matches!(self.peek(), Tok::Eof) {
            self.incomplete(format!("expected {}, got {:?}", what, self.peek()))
        } else {
            self.err(format!("expected {}, got {:?}", what, self.peek()))
        }
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline | Tok::Semi) {
            self.bump();
        }
    }
    fn skip_newline_tokens(&mut self) {
        while matches!(self.peek(), Tok::Newline) {
            self.bump();
        }
    }
    fn peek_after_newlines(&self) -> &Tok {
        let mut off = 0;
        while matches!(self.peek_at(off), Tok::Newline) {
            off += 1;
        }
        self.peek_at(off)
    }

    // --- entry ---

    pub fn parse_program(&mut self) -> PR<Program> {
        let (items, top_attrs) = self.parse_items_until(&[Tok::Eof])?;
        for a in &top_attrs {
            match a {
                Attribute::ModuleDoc(_) => {
                    return self.err("@moduledoc only valid inside a defmodule body".to_string());
                }
                Attribute::TypeAlias(_) => {
                    return self.err("@type only valid inside a defmodule body".to_string());
                }
                _ => {}
            }
        }
        Ok(Program {
            items,
            module_interfaces: Default::default(),
            external_module_interfaces: Default::default(),
            module_docs: Default::default(),
            module_type_envs: Default::default(),
            protocol_registry: Default::default(),
            opaque_inners: Default::default(),
            brand_inners: Default::default(),
        })
    }

    pub fn parse_program_with_telemetry(
        &mut self,
        tel: &dyn crate::telemetry::Telemetry,
    ) -> PR<Program> {
        use crate::telemetry::TelemetryExt;

        let _span = tel.span(PARSE_PASS_NAME, crate::telemetry::Metadata::new());
        let prog = self.parse_program()?;
        tel.execute(
            ITEMS_BUILT_NAME,
            &crate::measurements! { count: prog.items.len() },
            &crate::telemetry::Metadata::new(),
        );
        for diag in self.warnings.drain(..) {
            tel.event(
                DIAG_WARNING_NAME,
                crate::metadata! { diagnostic: crate::telemetry::value::opaque(&diag) },
            );
        }
        Ok(prog)
    }

    /// Like `parse_program` but allows top-level `@type` declarations
    /// (and returns them separately). Used for the built-in runtime.fz
    /// prelude, which is not wrapped in a `defmodule`.
    pub fn parse_prelude(&mut self) -> PR<(Vec<Rc<Item>>, Vec<crate::ast::Attribute>)> {
        let (items, attrs) = self.parse_items_until(&[Tok::Eof])?;
        Ok((items, attrs))
    }
}

mod expressions;
mod items;
mod patterns;

#[cfg(test)]
mod tests;
