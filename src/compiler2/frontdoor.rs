use std::fmt::{self, Display, Formatter};
use std::mem::discriminant;
use std::rc::Rc;

use crate::compiler::source::Span;
use crate::diag::{Diagnostic, codes::PARSE_EXPECTED_TOKEN};
use crate::parser::lexer::{Lexer, Tok, Token};
use crate::telemetry::Telemetry;
use fz_runtime::any_value::AnyValueRef;

use super::token_payload;
use super::{
    QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceBuilder, QuotedSourceError, QuotedSourceHeap,
    QuotedSourceMetadata, QuotedSourceRoot, QuotedSourceSpan,
};

#[derive(Debug)]
pub struct FrontDoorError {
    pub msg: String,
    pub span: Span,
}

impl FrontDoorError {
    fn syntax(msg: impl Into<String>, span: Span) -> Self {
        Self { msg: msg.into(), span }
    }

    pub fn to_diagnostic(&self) -> Diagnostic {
        Diagnostic::error(PARSE_EXPECTED_TOKEN, self.msg.clone(), self.span)
    }
}

impl Display for FrontDoorError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "frontdoor parse error: {}", self.msg)
    }
}

impl From<QuotedSourceError> for FrontDoorError {
    fn from(value: QuotedSourceError) -> Self {
        Self::syntax(value.to_string(), Span::DUMMY)
    }
}

pub fn parse_quoted_program(
    source_name: impl Into<String>,
    source_text: &str,
    tel: &dyn Telemetry,
) -> Result<QuotedSourceRoot, FrontDoorError> {
    let source_name = source_name.into();
    let tokens = Lexer::with_source_name(source_text, source_name.clone())
        .tokenize(tel)
        .map_err(|error| FrontDoorError::syntax(error.msg, error.span))?;
    FrontDoorParser::new(tokens, source_name, source_text).parse_program()
}

struct FrontDoorParser<'a> {
    toks: Vec<Token>,
    pos: usize,
    source_name: String,
    source_text: &'a str,
    builder: QuotedSourceBuilder,
    allow_trailing_do: bool,
    allow_extern_symbol_folding: bool,
    emit_type_payloads: bool,
}

#[derive(Clone)]
struct ParsedExpr {
    root: AnyValueRef,
    span: Span,
    call_head: Option<String>,
}

impl ParsedExpr {
    fn plain(root: AnyValueRef, span: Span) -> Self {
        Self {
            root,
            span,
            call_head: None,
        }
    }

    fn direct_name(root: AnyValueRef, span: Span, name: String) -> Self {
        Self {
            root,
            span,
            call_head: Some(name),
        }
    }
}

impl<'a> FrontDoorParser<'a> {
    fn new(toks: Vec<Token>, source_name: String, source_text: &'a str) -> Self {
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        Self {
            toks,
            pos: 0,
            source_name,
            source_text,
            builder,
            allow_trailing_do: true,
            allow_extern_symbol_folding: true,
            emit_type_payloads: true,
        }
    }

    fn parse_program(mut self) -> Result<QuotedSourceRoot, FrontDoorError> {
        let items = self.parse_items_until(&[Tok::Eof], &[])?;
        self.builder
            .root(self.builder.list(&items)?)
            .map_err(FrontDoorError::from)
    }

    fn parse_items_until(
        &mut self,
        terminators: &[Tok],
        module_path: &[String],
    ) -> Result<Vec<AnyValueRef>, FrontDoorError> {
        let mut items = Vec::new();
        self.skip_newlines();
        while !terminators.iter().any(|terminator| self.peek_is(terminator)) {
            items.push(self.parse_item(module_path)?);
            self.skip_newlines();
        }
        Ok(items)
    }

    fn parse_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        match self.peek() {
            Tok::At => self.parse_attribute_item(module_path),
            Tok::Alias => self.parse_alias(module_path),
            Tok::Import => self.parse_import_like("import", Tok::Import, module_path),
            Tok::Require => self.parse_import_like("require", Tok::Require, module_path),
            Tok::Defmodule => self.parse_module(module_path),
            Tok::Defstruct => self.parse_struct_item(module_path),
            Tok::Defprotocol => self.parse_protocol_item(module_path),
            Tok::Defimpl => self.parse_protocol_impl_item(module_path),
            Tok::Extern => self.parse_extern_item(module_path),
            Tok::Fn | Tok::Fnp | Tok::Defmacro => self.parse_function_item(module_path),
            Tok::Ident(_) => self.parse_item_macro_call(module_path),
            other => self.err(format!(
                "compiler2 quoted front door does not yet parse {:?} at item position",
                other
            )),
        }
    }

    fn parse_attribute_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::At, "`@`")?;
        let (name, value) = match self.bump() {
            Tok::Ident(name) if name == "doc" || name == "moduledoc" => {
                let value = match self.bump() {
                    Tok::Binary(bytes) => self.builder.bitstring(&bytes, (bytes.len() * 8) as u64)?,
                    other => {
                        return Err(self.error(format!("expected string literal after `@{}`, got {:?}", name, other)));
                    }
                };
                (name, value)
            }
            Tok::Ident(name) if name == "spec" => {
                let tokens = self.collect_line_tokens()?;
                (name, token_payload::encode_tokens(&self.builder, &tokens)?)
            }
            Tok::Type => {
                let tokens = self.collect_line_tokens()?;
                (
                    "type".to_string(),
                    token_payload::encode_tokens(&self.builder, &tokens)?,
                )
            }
            other => return Err(self.error(format!("unsupported compiler2 attribute head {:?}", other))),
        };
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, &[], span)?;
        self.builder
            .call(&format!("@{name}"), &meta, &[value])
            .map_err(FrontDoorError::from)
    }

    fn parse_function_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        let head_name = match self.bump() {
            Tok::Fn => "fn",
            Tok::Fnp => "fnp",
            Tok::Defmacro => "defmacro",
            other => unreachable!("guarded by parse_item: {:?}", other),
        };
        let (function_name, mut head) = self.parse_function_head(module_path)?;
        let scope = vec![function_name.clone()];
        if self.eat(&Tok::When) {
            let guard = self
                .with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, &scope))?
                .root;
            let meta = self.meta(module_path, &scope, start.merge(self.prev_span()))?;
            head = self.builder.call("when", &meta, &[head, guard])?;
        }
        let body = self.parse_function_body(module_path, &scope)?;
        let meta = self.meta(module_path, &scope, start.merge(self.prev_span()))?;
        let kw = self.builder.list(&[self.builder.keyword("do", body)?])?;
        self.builder
            .call(head_name, &meta, &[head, kw])
            .map_err(FrontDoorError::from)
    }

    fn parse_protocol_body_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        match self.peek() {
            Tok::At => self.parse_attribute_item(module_path),
            Tok::Fn => self.parse_protocol_callback_item(module_path),
            other => self.err(format!(
                "compiler2 quoted front door expected protocol callback or attribute, got {:?}",
                other
            )),
        }
    }

    fn parse_protocol_callback_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Fn, "`fn`")?;
        let (name, head) = self.parse_function_head(module_path)?;
        let scope = vec![name];
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, &scope, span)?;
        self.builder.call("fn", &meta, &[head]).map_err(FrontDoorError::from)
    }

    fn parse_item_macro_call(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let expr = self.parse_expr(module_path, &[])?;
        let Some(node) = self.builder.root(expr.root)?.cursor().ast_node()? else {
            return self.err("expected an item-level macro call");
        };
        if node.tail.list_items().is_err() {
            return self.err("expected an item-level macro call");
        }
        Ok(expr.root)
    }

    fn parse_alias(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Alias, "`alias`")?;
        let path = self.parse_upper_path("alias")?;
        let meta = self.meta(module_path, &[], start)?;
        let alias = self.builder.alias(&meta, &segments_ref(&path))?;
        let mut args = vec![alias];
        if self.eat(&Tok::Comma) {
            let kw = match self.bump() {
                Tok::KwKey(key) if key == "as" => key,
                other => return Err(self.error(format!("expected `as:` after alias comma, got {:?}", other))),
            };
            let alias_name = match self.bump() {
                Tok::Upper(name) => name,
                other => {
                    return Err(self.error(format!(
                        "expected uppercase alias nickname after `{}:`, got {:?}",
                        kw, other
                    )));
                }
            };
            let alias_value = self.builder.alias(&meta, &[alias_name.as_str()])?;
            args.push(self.builder.list(&[self.builder.keyword("as", alias_value)?])?);
        }
        self.builder.call("alias", &meta, &args).map_err(FrontDoorError::from)
    }

    fn parse_import_like(
        &mut self,
        head: &str,
        head_tok: Tok,
        module_path: &[String],
    ) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&head_tok, &format!("`{head}`"))?;
        let path = self.parse_upper_path(head)?;
        let meta = self.meta(module_path, &[], start)?;
        let alias = self.builder.alias(&meta, &segments_ref(&path))?;
        let mut args = vec![alias];
        if self.eat(&Tok::Comma) {
            let kind = match self.bump() {
                Tok::KwKey(kind) if kind == "only" || kind == "except" => kind,
                other => {
                    return Err(self.error(format!("expected `only:` or `except:` after `{head}`, got {:?}", other)));
                }
            };
            let filters = self.parse_arity_kw_list()?;
            args.push(self.builder.list(&[self.builder.keyword(&kind, filters)?])?);
        }
        self.builder.call(head, &meta, &args).map_err(FrontDoorError::from)
    }

    fn parse_module(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Defmodule, "`defmodule`")?;
        let name_path = self.parse_upper_path("module")?;
        let meta = self.meta(module_path, &[], start)?;
        let alias = self.builder.alias(&meta, &segments_ref(&name_path))?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut nested_path = module_path.to_vec();
        nested_path.extend(name_path.iter().cloned());
        let items = self.parse_items_until(&[Tok::End], &nested_path)?;
        self.expect(&Tok::End, "`end`")?;
        let body = self.builder.list(&items)?;
        let kw = self.builder.list(&[self.builder.keyword("do", body)?])?;
        self.builder
            .call("defmodule", &meta, &[alias, kw])
            .map_err(FrontDoorError::from)
    }

    fn parse_struct_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Defstruct, "`defstruct`")?;
        self.expect(&Tok::LBrack, "`[`")?;
        let mut fields = Vec::new();
        self.skip_newlines();
        if !self.peek_is(&Tok::RBrack) {
            loop {
                let field = match self.bump() {
                    Tok::Atom(name) | Tok::Ident(name) | Tok::KwKey(name) => self.builder.atom(&name),
                    other => return Err(self.error(format!("expected struct field name, got {:?}", other))),
                };
                fields.push(field);
                self.skip_newlines();
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBrack, "`]`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, &[], span)?;
        self.builder
            .call("defstruct", &meta, &[self.builder.list(&fields)?])
            .map_err(FrontDoorError::from)
    }

    fn parse_protocol_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Defprotocol, "`defprotocol`")?;
        let name_path = self.parse_upper_path("protocol")?;
        let meta = self.meta(module_path, &[], start)?;
        let alias = self.builder.alias(&meta, &segments_ref(&name_path))?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut items = Vec::new();
        while !self.peek_is(&Tok::End) {
            items.push(self.parse_protocol_body_item(module_path)?);
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        let span = start.merge(self.prev_span());
        let body_meta = self.meta(module_path, &[], span)?;
        let kw = self
            .builder
            .list(&[self.builder.keyword("do", self.builder.list(&items)?)?])?;
        self.builder
            .call("defprotocol", &body_meta, &[alias, kw])
            .map_err(FrontDoorError::from)
    }

    fn parse_protocol_impl_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Defimpl, "`defimpl`")?;
        let protocol_path = self.parse_upper_path("protocol")?;
        self.expect(&Tok::Comma, "`,`")?;
        match self.bump() {
            Tok::KwKey(key) if key == "for" => {}
            other => return Err(self.error(format!("expected `for:` in defimpl, got {:?}", other))),
        }
        let target_path = self.parse_upper_path("implementation target")?;
        let meta = self.meta(module_path, &[], start)?;
        let protocol_alias = self.builder.alias(&meta, &segments_ref(&protocol_path))?;
        let target_alias = self.builder.alias(&meta, &segments_ref(&target_path))?;
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let items = self.parse_items_until(&[Tok::End], module_path)?;
        self.expect(&Tok::End, "`end`")?;
        let span = start.merge(self.prev_span());
        let body_meta = self.meta(module_path, &[], span)?;
        let kw = self.builder.list(&[
            self.builder.keyword("for", target_alias)?,
            self.builder.keyword("do", self.builder.list(&items)?)?,
        ])?;
        self.builder
            .call("defimpl", &body_meta, &[protocol_alias, kw])
            .map_err(FrontDoorError::from)
    }

    fn parse_extern_item(&mut self, module_path: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        self.expect(&Tok::Extern, "`extern`")?;
        let abi = match self.bump() {
            Tok::Binary(bytes) => String::from_utf8(bytes)
                .map_err(|error| self.error(format!("extern ABI string must be valid UTF-8: {error}")))?,
            other => return Err(self.error(format!("expected ABI string after `extern`, got {:?}", other))),
        };
        self.expect(&Tok::Fn, "`fn` after extern ABI string")?;
        let name = self.parse_extern_name()?;
        self.expect(&Tok::LParen, "`(`")?;
        let mut params = Vec::new();
        let mut variadic = false;
        self.skip_newlines();
        if !self.peek_is(&Tok::RParen) {
            loop {
                if self.eat(&Tok::Ellipsis) {
                    if params.is_empty() {
                        return self.err("extern variadic `...` must follow at least one fixed parameter");
                    }
                    variadic = true;
                    self.skip_newlines();
                    if !self.peek_is(&Tok::RParen) {
                        return self.err("extern variadic `...` must be the final parameter");
                    }
                    break;
                }
                let param = self.collect_balanced_tokens_until(&[Tok::Comma, Tok::RParen])?;
                if param.is_empty() {
                    return self.err("expected extern parameter type");
                }
                params.push(token_payload::encode_tokens(&self.builder, &param)?);
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
                if self.eat(&Tok::Ellipsis) {
                    variadic = true;
                    self.skip_newlines();
                    if !self.peek_is(&Tok::RParen) {
                        return self.err("extern variadic `...` must be the final parameter");
                    }
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "`)`")?;
        self.expect(&Tok::ColonColon, "`::`")?;
        let ret = self.collect_balanced_tokens_until(&[Tok::When, Tok::Newline, Tok::Eof, Tok::End])?;
        if ret.is_empty() {
            return self.err("expected extern return type after `::`");
        }
        let ret = token_payload::encode_tokens(&self.builder, &ret)?;
        let mut constraints = Vec::new();
        if self.eat(&Tok::When) {
            loop {
                let (var, colon_consumed) = match self.bump() {
                    Tok::Ident(name) => (name, false),
                    Tok::KwKey(name) => (name, true),
                    other => return Err(self.error(format!("expected type variable after `when`, got {:?}", other))),
                };
                if !colon_consumed {
                    self.expect(&Tok::Colon, "`:`")?;
                }
                let ty = self.collect_balanced_tokens_until(&[Tok::Comma, Tok::Newline, Tok::Eof, Tok::End])?;
                if ty.is_empty() {
                    return self.err(format!("expected constraint type expression after `{var}:`"));
                }
                constraints.push((var, token_payload::encode_tokens(&self.builder, &ty)?));
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, &[], span)?;
        let constraints = constraints
            .iter()
            .map(|(name, ty)| self.builder.keyword(name, *ty))
            .collect::<Result<Vec<_>, _>>()?;
        let mut entries = vec![
            (self.builder.atom("name"), self.builder.utf8_binary(&name)?),
            (self.builder.atom("params"), self.builder.list(&params)?),
            (self.builder.atom("return"), ret),
            (self.builder.atom("variadic"), self.builder.bool(variadic)),
        ];
        if !constraints.is_empty() {
            entries.push((self.builder.atom("when"), self.builder.list(&constraints)?));
        }
        self.builder
            .call(
                "extern",
                &meta,
                &[self.builder.utf8_binary(&abi)?, self.builder.map(&entries)?],
            )
            .map_err(FrontDoorError::from)
    }

    fn parse_function_head(&mut self, module_path: &[String]) -> Result<(String, AnyValueRef), FrontDoorError> {
        let start = self.cur_span();
        if self.callable_name_token(self.peek()).is_some() && matches!(self.peek_at(1), Tok::LParen) {
            let name = self.bump_callable_name().expect("guarded callable head name");
            let scope = vec![name.clone()];
            self.expect(&Tok::LParen, "`(`")?;
            let params = self.parse_exprs_until(&Tok::RParen, module_path, &scope)?;
            self.expect(&Tok::RParen, "`)`")?;
            let meta = self.meta(module_path, &scope, start.merge(self.prev_span()))?;
            let head = self.builder.call(&name, &meta, &params)?;
            return Ok((name, head));
        }

        let left = self.parse_bp(121, module_path, &[])?;
        let op = self.operator_name(self.peek()).ok_or_else(|| {
            self.error(format!(
                "expected `name(` or an operator-headed function clause, got {:?}",
                self.peek()
            ))
        })?;
        self.bump();
        let right = self.parse_bp(121, module_path, &[])?;
        let meta = self.meta(module_path, &[op.to_string()], start.merge(self.prev_span()))?;
        let head = self.builder.call(op, &meta, &[left.root, right.root])?;
        Ok((op.to_string(), head))
    }

    fn callable_name_token<'tok>(&self, tok: &'tok Tok) -> Option<&'tok str> {
        match tok {
            Tok::Ident(name) => Some(name.as_str()),
            Tok::Fn => Some("fn"),
            Tok::Fnp => Some("fnp"),
            Tok::Defmacro => Some("defmacro"),
            Tok::Defmodule => Some("defmodule"),
            Tok::Defprotocol => Some("defprotocol"),
            Tok::Defimpl => Some("defimpl"),
            Tok::Defstruct => Some("defstruct"),
            Tok::Alias => Some("alias"),
            Tok::Import => Some("import"),
            Tok::Require => Some("require"),
            Tok::Extern => Some("extern"),
            _ => None,
        }
    }

    fn bump_callable_name(&mut self) -> Option<String> {
        match self.bump() {
            Tok::Ident(name) => Some(name),
            Tok::Fn => Some("fn".to_string()),
            Tok::Fnp => Some("fnp".to_string()),
            Tok::Defmacro => Some("defmacro".to_string()),
            Tok::Defmodule => Some("defmodule".to_string()),
            Tok::Defprotocol => Some("defprotocol".to_string()),
            Tok::Defimpl => Some("defimpl".to_string()),
            Tok::Defstruct => Some("defstruct".to_string()),
            Tok::Alias => Some("alias".to_string()),
            Tok::Import => Some("import".to_string()),
            Tok::Require => Some("require".to_string()),
            Tok::Extern => Some("extern".to_string()),
            _ => None,
        }
    }

    fn parse_function_body(&mut self, module_path: &[String], scope: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        if self.eat(&Tok::Comma) {
            match self.bump() {
                Tok::KwKey(key) if key == "do" => {}
                other => return Err(self.error(format!("expected `do:` after `,`, got {:?}", other))),
            }
            return Ok(self.parse_expr(module_path, scope)?.root);
        }
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let body = self.parse_block_until(&[Tok::End], module_path, scope)?;
        self.expect(&Tok::End, "`end`")?;
        Ok(body)
    }

    fn parse_expr(&mut self, module_path: &[String], scope: &[String]) -> Result<ParsedExpr, FrontDoorError> {
        self.skip_newlines();
        self.parse_bp(0, module_path, scope)
    }

    fn parse_bp(&mut self, min_bp: u8, module_path: &[String], scope: &[String]) -> Result<ParsedExpr, FrontDoorError> {
        let mut lhs = self.parse_prefix(module_path, scope)?;
        loop {
            if self.peek_is(&Tok::Newline) && self.starts_expr_continuation(self.peek_after_newlines()) {
                self.skip_newlines();
            }
            if self.peek_is(&Tok::LParen) {
                lhs = self.finish_call(lhs, module_path, scope)?;
                continue;
            }
            if self.peek_is(&Tok::Dot) && self.peek_is_at(1, &Tok::LParen) {
                lhs = self.finish_closure_call(lhs, module_path, scope)?;
                continue;
            }
            if self.peek_is(&Tok::Dot) {
                lhs = self.finish_remote_target(lhs, module_path, scope)?;
                continue;
            }
            if self.peek_is(&Tok::LBrack) {
                lhs = self.finish_bracket_access(lhs, module_path, scope)?;
                continue;
            }
            if self.peek_is(&Tok::Eq) {
                let lbp = 5;
                if lbp < min_bp {
                    break;
                }
                self.bump();
                self.skip_newlines();
                let rhs = self.parse_bp(lbp, module_path, scope)?;
                let span = lhs.span.merge(rhs.span);
                let meta = self.meta(module_path, scope, span)?;
                lhs = ParsedExpr::plain(self.builder.call("=", &meta, &[lhs.root, rhs.root])?, span);
                continue;
            }
            if self.peek_is(&Tok::Not) && self.peek_is_at(1, &Tok::In) {
                let lbp = 70;
                let rbp = 71;
                if lbp < min_bp {
                    break;
                }
                self.bump();
                self.bump();
                self.skip_newlines();
                let rhs = self.parse_bp(rbp, module_path, scope)?;
                let span = lhs.span.merge(rhs.span);
                let meta = self.meta(module_path, scope, span)?;
                lhs = ParsedExpr::plain(self.builder.call("not in", &meta, &[lhs.root, rhs.root])?, span);
                continue;
            }
            let Some((lbp, rbp, op)) = self.infix_bp(self.peek()) else {
                break;
            };
            if lbp < min_bp {
                break;
            }
            if self.emit_type_payloads && self.peek_is(&Tok::ColonColon) {
                self.bump();
                let rhs_tokens = self.collect_type_fragment_tokens(rbp)?;
                if rhs_tokens.is_empty() {
                    return self.err("expected type expression after `::`");
                }
                let rhs = token_payload::encode_tokens(&self.builder, &rhs_tokens)?;
                let span = lhs.span.merge(self.prev_span());
                let meta = self.meta(module_path, scope, span)?;
                lhs = ParsedExpr::plain(self.builder.call("::", &meta, &[lhs.root, rhs])?, span);
                continue;
            }
            self.bump();
            self.skip_newlines();
            let rhs = self.parse_bp(rbp, module_path, scope)?;
            let span = lhs.span.merge(rhs.span);
            let meta = self.meta(module_path, scope, span)?;
            lhs = ParsedExpr::plain(self.builder.call(op, &meta, &[lhs.root, rhs.root])?, span);
        }
        Ok(lhs)
    }

    fn parse_prefix(&mut self, module_path: &[String], scope: &[String]) -> Result<ParsedExpr, FrontDoorError> {
        let start = self.cur_span();
        match self.bump() {
            Tok::Int(value) => Ok(ParsedExpr::plain(self.builder.int(value), start)),
            Tok::Float(value) => Ok(ParsedExpr::plain(self.builder.float(value), start)),
            Tok::Binary(bytes) => Ok(ParsedExpr::plain(
                self.builder.bitstring(&bytes, (bytes.len() * 8) as u64)?,
                start,
            )),
            Tok::True => Ok(ParsedExpr::plain(self.builder.bool(true), start)),
            Tok::False => Ok(ParsedExpr::plain(self.builder.bool(false), start)),
            Tok::Nil => Ok(ParsedExpr::plain(self.builder.nil(), start)),
            Tok::Atom(name) => Ok(ParsedExpr::plain(self.builder.atom(&name), start)),
            Tok::Underscore => {
                let meta = self.meta(module_path, scope, start)?;
                Ok(ParsedExpr::plain(self.builder.variable("_", &meta)?, start))
            }
            Tok::Ident(name) => {
                let mut name = name;
                if self.allow_extern_symbol_folding
                    && self.peek_is(&Tok::ColonColon)
                    && self.prev_span().end == self.cur_span().start
                {
                    self.bump();
                    match self.bump() {
                        Tok::Ident(second) => {
                            name = format!("{name}::{second}");
                        }
                        other => {
                            return self.err(format!("expected name after `{}::`, got {:?}", name, other));
                        }
                    }
                }
                let meta = self.meta(module_path, scope, start)?;
                let root = self.builder.variable(&name, &meta)?;
                Ok(ParsedExpr::direct_name(root, start.merge(self.prev_span()), name))
            }
            Tok::Upper(name) => self.parse_alias_expr(name, module_path, scope, start),
            Tok::LParen => {
                let inner = self.parse_expr(module_path, scope)?;
                self.expect(&Tok::RParen, "`)`")?;
                Ok(ParsedExpr::plain(inner.root, start.merge(self.prev_span())))
            }
            Tok::LBrack => self.parse_list_literal(module_path, scope, start),
            Tok::LBrace => self.parse_tuple_literal(module_path, scope, start),
            Tok::PercentLBrace => self.parse_map_literal(module_path, scope, start),
            Tok::Percent => self.parse_struct_expr(module_path, scope, start),
            Tok::LBitstr => self.parse_bitstring_literal(module_path, scope, start),
            Tok::Minus => {
                let inner = self.parse_bp(120, module_path, scope)?;
                let span = start.merge(inner.span);
                let meta = self.meta(module_path, scope, span)?;
                Ok(ParsedExpr::plain(self.builder.call("-", &meta, &[inner.root])?, span))
            }
            Tok::Not => {
                let inner = self.parse_bp(120, module_path, scope)?;
                let span = start.merge(inner.span);
                let meta = self.meta(module_path, scope, span)?;
                Ok(ParsedExpr::plain(self.builder.call("not", &meta, &[inner.root])?, span))
            }
            Tok::Quote => self.parse_quote_expr(module_path, scope, start),
            Tok::Unquote => self.parse_unquote_expr(module_path, scope, start),
            Tok::If => self.parse_if_expr(module_path, scope, start),
            Tok::Cond => self.parse_cond_expr(module_path, scope, start),
            Tok::Receive => self.parse_receive_expr(module_path, scope, start),
            Tok::Case => self.parse_case_expr(module_path, scope, start),
            Tok::With => self.parse_with_expr(module_path, scope, start),
            Tok::Fn => self.parse_lambda_expr(module_path, scope, start),
            Tok::Amp => self.parse_capture_expr(module_path, scope, start),
            Tok::Caret => self.parse_pin_expr(module_path, scope, start),
            other => self.err(format!(
                "unsupported expression prefix in compiler2 front door: {:?}",
                other
            )),
        }
    }

    fn finish_call(
        &mut self,
        lhs: ParsedExpr,
        module_path: &[String],
        scope: &[String],
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::LParen, "`(`")?;
        let mut args = self.parse_exprs_until(&Tok::RParen, module_path, scope)?;
        self.expect(&Tok::RParen, "`)`")?;
        self.attach_trailing_do(&mut args, module_path, scope)?;
        let span = lhs.span.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let root = if let Some(name) = lhs.call_head {
            self.builder.call(&name, &meta, &args)?
        } else {
            self.builder.call_callee(lhs.root, &meta, &args)?
        };
        Ok(ParsedExpr::plain(root, span))
    }

    fn finish_closure_call(
        &mut self,
        lhs: ParsedExpr,
        module_path: &[String],
        scope: &[String],
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::Dot, "`.`")?;
        self.expect(&Tok::LParen, "`(`")?;
        let mut args = self.parse_exprs_until(&Tok::RParen, module_path, scope)?;
        self.expect(&Tok::RParen, "`)`")?;
        self.attach_trailing_do(&mut args, module_path, scope)?;
        let dot_span = lhs.span.merge(self.prev_span());
        let dot_meta = self.meta(module_path, scope, dot_span)?;
        let callee = self
            .builder
            .ast_node(self.builder.atom("."), &dot_meta, self.builder.list(&[lhs.root])?)?;
        let call_meta = self.meta(module_path, scope, dot_span)?;
        let root = self.builder.call_callee(callee, &call_meta, &args)?;
        Ok(ParsedExpr::plain(root, dot_span))
    }

    fn finish_remote_target(
        &mut self,
        lhs: ParsedExpr,
        module_path: &[String],
        scope: &[String],
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::Dot, "`.`")?;
        let field = match self.bump() {
            Tok::Ident(name) | Tok::Upper(name) => name,
            other => return Err(self.error(format!("expected name after `.`, got {:?}", other))),
        };
        let span = lhs.span.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let tail = self.builder.list(&[lhs.root, self.builder.atom(&field)])?;
        let root = self.builder.ast_node(self.builder.atom("."), &meta, tail)?;
        Ok(ParsedExpr::plain(root, span))
    }

    fn finish_bracket_access(
        &mut self,
        lhs: ParsedExpr,
        module_path: &[String],
        scope: &[String],
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::LBrack, "`[`")?;
        let key = self.parse_expr(module_path, scope)?;
        self.expect(&Tok::RBrack, "`]`")?;
        let span = lhs.span.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let callee = self.builder.ast_node(
            self.builder.atom("."),
            &meta,
            self.builder
                .list(&[self.builder.alias(&meta, &["Access"])?, self.builder.atom("get")])?,
        )?;
        let root = self.builder.call_callee(callee, &meta, &[lhs.root, key.root])?;
        Ok(ParsedExpr::plain(root, span))
    }

    fn parse_alias_expr(
        &mut self,
        first: String,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let mut path = vec![first];
        while self.peek_is(&Tok::Dot) && matches!(self.peek_at(1), Tok::Upper(_)) {
            self.bump();
            match self.bump() {
                Tok::Upper(name) => path.push(name),
                _ => unreachable!("guarded by peek_at"),
            }
        }
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        Ok(ParsedExpr::plain(
            self.builder.alias(&meta, &segments_ref(&path))?,
            span,
        ))
    }

    fn parse_list_literal(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let mut items = Vec::new();
        self.skip_newlines();
        if self.peek_is(&Tok::RBrack) {
            self.expect(&Tok::RBrack, "`]`")?;
            return Ok(ParsedExpr::plain(
                self.builder.empty_list(),
                start.merge(self.prev_span()),
            ));
        }
        loop {
            if matches!(self.peek(), Tok::KwKey(_)) {
                items.push(self.parse_keyword_entry_expr(module_path, scope)?);
            } else {
                items.push(self.parse_expr(module_path, scope)?.root);
            }
            self.skip_newlines();
            if self.eat(&Tok::Bar) {
                let tail = self.parse_expr(module_path, scope)?.root;
                self.expect(&Tok::RBrack, "`]`")?;
                let span = start.merge(self.prev_span());
                let root = self.improper_list(&items, tail, module_path, scope, span)?;
                return Ok(ParsedExpr::plain(root, span));
            }
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        self.expect(&Tok::RBrack, "`]`")?;
        Ok(ParsedExpr::plain(
            self.builder.list(&items)?,
            start.merge(self.prev_span()),
        ))
    }

    fn parse_tuple_literal(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let items = self.parse_exprs_until(&Tok::RBrace, module_path, scope)?;
        self.expect(&Tok::RBrace, "`}`")?;
        let span = start.merge(self.prev_span());
        let root = if items.len() == 2 {
            self.builder.tuple(&items)?
        } else {
            let meta = self.meta(module_path, scope, span)?;
            self.builder.call("{}", &meta, &items)?
        };
        Ok(ParsedExpr::plain(root, span))
    }

    fn parse_map_literal(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let entries = self.parse_map_entries(module_path, scope, true)?;
        self.expect(&Tok::RBrace, "`}`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        Ok(ParsedExpr::plain(self.builder.call("%{}", &meta, &entries)?, span))
    }

    fn parse_struct_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let name_path = self.parse_upper_path("struct")?;
        self.expect(&Tok::LBrace, "`{`")?;
        let entries = self.parse_map_entries(module_path, scope, false)?;
        self.expect(&Tok::RBrace, "`}`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let alias = self.builder.alias(&meta, &segments_ref(&name_path))?;
        let map = self.builder.call("%{}", &meta, &entries)?;
        Ok(ParsedExpr::plain(self.builder.call("%", &meta, &[alias, map])?, span))
    }

    fn parse_bitstring_literal(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let segments = self.with_extern_symbol_folding_suppressed(|parser| {
            parser.with_type_payloads_suppressed(|parser| parser.parse_exprs_until(&Tok::RBitstr, module_path, scope))
        })?;
        self.expect(&Tok::RBitstr, "`>>`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        Ok(ParsedExpr::plain(self.builder.call("<<>>", &meta, &segments)?, span))
    }

    fn parse_quote_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let body = if matches!(self.peek(), Tok::KwKey(key) if key == "do") {
            self.bump();
            self.parse_expr(module_path, scope)?.root
        } else {
            self.expect(&Tok::Do, "`do`")?;
            self.skip_newlines();
            let body = self.parse_block_until(&[Tok::End], module_path, scope)?;
            self.expect(&Tok::End, "`end`")?;
            body
        };
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let kw = self.builder.list(&[self.builder.keyword("do", body)?])?;
        Ok(ParsedExpr::plain(self.builder.call("quote", &meta, &[kw])?, span))
    }

    fn parse_unquote_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::LParen, "`(` after `unquote`")?;
        let value = self.parse_expr(module_path, scope)?;
        self.expect(&Tok::RParen, "`)`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        Ok(ParsedExpr::plain(
            self.builder.call("unquote", &meta, &[value.root])?,
            span,
        ))
    }

    fn parse_if_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let cond = self.with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, scope))?;
        let mut kw_entries = Vec::new();
        if self.eat(&Tok::Comma) {
            match self.bump() {
                Tok::KwKey(key) if key == "do" => {}
                other => return Err(self.error(format!("expected `do:` after `if` condition, got {:?}", other))),
            }
            let body = self.parse_expr(module_path, scope)?.root;
            kw_entries.push(self.builder.keyword("do", body)?);
            if self.eat(&Tok::Comma) {
                match self.bump() {
                    Tok::KwKey(key) if key == "else" => {}
                    other => return Err(self.error(format!("expected `else:` after `if` branch, got {:?}", other))),
                }
                let els = self.parse_expr(module_path, scope)?.root;
                kw_entries.push(self.builder.keyword("else", els)?);
            }
        } else {
            self.expect(&Tok::Do, "`do`")?;
            self.skip_newlines();
            let body = self.parse_block_until(&[Tok::Else, Tok::End], module_path, scope)?;
            kw_entries.push(self.builder.keyword("do", body)?);
            if self.eat(&Tok::Else) {
                self.skip_newlines();
                let els = self.parse_block_until(&[Tok::End], module_path, scope)?;
                kw_entries.push(self.builder.keyword("else", els)?);
            }
            self.expect(&Tok::End, "`end`")?;
        }
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let kw = self.builder.list(&kw_entries)?;
        Ok(ParsedExpr::plain(
            self.builder.call("if", &meta, &[cond.root, kw])?,
            span,
        ))
    }

    fn parse_receive_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !matches!(self.peek(), Tok::After | Tok::End | Tok::Eof) {
            clauses.push(self.parse_case_clause(module_path, scope)?);
            self.skip_newlines();
        }
        let mut kw_entries = vec![self.builder.keyword("do", self.builder.list(&clauses)?)?];
        if self.eat(&Tok::After) {
            self.skip_newlines();
            let after_start = self.cur_span();
            let timeout = self.with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, scope))?;
            self.expect(&Tok::Arrow, "`->` after receive timeout")?;
            self.skip_newlines();
            let body = self.parse_expr(module_path, scope)?;
            let after_span = after_start.merge(body.span);
            let after_meta = self.meta(module_path, scope, after_span)?;
            let patterns = self.builder.list(&[timeout.root])?;
            let clause = self.builder.call("->", &after_meta, &[patterns, body.root])?;
            kw_entries.push(self.builder.keyword("after", self.builder.list(&[clause])?)?);
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let kw = self.builder.list(&kw_entries)?;
        Ok(ParsedExpr::plain(self.builder.call("receive", &meta, &[kw])?, span))
    }

    fn parse_lambda_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !matches!(self.peek(), Tok::End | Tok::Eof) {
            let clause_start = self.cur_span();
            let params = if self.eat(&Tok::LParen) {
                let params = self.parse_exprs_until(&Tok::RParen, module_path, scope)?;
                self.expect(&Tok::RParen, "`)`")?;
                params
            } else {
                vec![self.parse_expr(module_path, scope)?.root]
            };
            let patterns = if self.eat(&Tok::When) {
                let guard = self.parse_expr(module_path, scope)?;
                let when_span = clause_start.merge(guard.span);
                let when_meta = self.meta(module_path, scope, when_span)?;
                let mut when_args = params.clone();
                when_args.push(guard.root);
                self.builder
                    .list(&[self.builder.call("when", &when_meta, &when_args)?])?
            } else {
                self.builder.list(&params)?
            };
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            let body = self.parse_expr(module_path, scope)?;
            let clause_span = clause_start.merge(body.span);
            let clause_meta = self.meta(module_path, scope, clause_span)?;
            clauses.push(self.builder.call("->", &clause_meta, &[patterns, body.root])?);
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        Ok(ParsedExpr::plain(self.builder.call("fn", &meta, &clauses)?, span))
    }

    fn parse_capture_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        if let Tok::Int(index) = self.peek()
            && *index >= 1
            && start.end == self.cur_span().start
        {
            let index = match self.bump() {
                Tok::Int(index) => index,
                _ => unreachable!("guarded by peek"),
            };
            let span = start.merge(self.prev_span());
            let meta = self.meta(module_path, scope, span)?;
            return Ok(ParsedExpr::plain(
                self.builder.call("&", &meta, &[self.builder.int(index)])?,
                span,
            ));
        }

        if self.eat(&Tok::LParen) {
            let body = self.parse_expr(module_path, scope)?;
            self.expect(&Tok::RParen, "`)` to close `&(...)` capture")?;
            let span = start.merge(self.prev_span());
            let meta = self.meta(module_path, scope, span)?;
            return Ok(ParsedExpr::plain(self.builder.call("&", &meta, &[body.root])?, span));
        }

        let target = self.parse_capture_target(module_path, scope, start)?;
        self.expect(&Tok::Slash, "`/` in capture")?;
        let arity = match self.bump() {
            Tok::Int(arity) if arity >= 0 => arity,
            other => return Err(self.error(format!("expected capture arity after `&.../`, got {:?}", other))),
        };
        let span = target.span.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let slash = self.builder.call("/", &meta, &[target.root, self.builder.int(arity)])?;
        Ok(ParsedExpr::plain(self.builder.call("&", &meta, &[slash])?, span))
    }

    fn parse_capture_target(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let mut target = match self.bump() {
            Tok::Ident(name) => {
                let meta = self.meta(module_path, scope, start)?;
                ParsedExpr::direct_name(self.builder.variable(&name, &meta)?, start, name)
            }
            Tok::Upper(name) => self.parse_alias_expr(name, module_path, scope, start)?,
            other if self.operator_name(&other).is_some() => {
                let name = self.operator_name(&other).expect("checked operator token").to_string();
                let meta = self.meta(module_path, scope, start)?;
                ParsedExpr::direct_name(self.builder.variable(&name, &meta)?, start, name)
            }
            other => {
                return Err(self.error(format!(
                    "compiler2 front door only supports local, remote, and operator capture refs so far, got {:?}",
                    other
                )));
            }
        };

        while self.peek_is(&Tok::Dot) {
            self.expect(&Tok::Dot, "`.`")?;
            let field = match self.bump() {
                Tok::Ident(name) | Tok::Upper(name) => name,
                other if self.operator_name(&other).is_some() => {
                    self.operator_name(&other).expect("checked operator token").to_string()
                }
                other => return Err(self.error(format!("expected capture target name after `.`, got {:?}", other))),
            };
            let span = target.span.merge(self.prev_span());
            let meta = self.meta(module_path, scope, span)?;
            let callee = self.builder.ast_node(
                self.builder.atom("."),
                &meta,
                self.builder.list(&[target.root, self.builder.atom(&field)])?,
            )?;
            target = ParsedExpr::plain(callee, span);
        }

        Ok(target)
    }

    fn parse_pin_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let inner = self.parse_bp(120, module_path, scope)?;
        let span = start.merge(inner.span);
        let meta = self.meta(module_path, scope, span)?;
        Ok(ParsedExpr::plain(self.builder.call("^", &meta, &[inner.root])?, span))
    }

    fn parse_cond_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !self.peek_is(&Tok::End) {
            let test = self.with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, scope))?;
            self.expect(&Tok::Arrow, "`->`")?;
            self.skip_newlines();
            let body = self.parse_expr(module_path, scope)?;
            let clause_span = test.span.merge(body.span);
            let clause_meta = self.meta(module_path, scope, clause_span)?;
            clauses.push(
                self.builder
                    .call("->", &clause_meta, &[self.builder.list(&[test.root])?, body.root])?,
            );
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let kw = self
            .builder
            .list(&[self.builder.keyword("do", self.builder.list(&clauses)?)?])?;
        Ok(ParsedExpr::plain(self.builder.call("cond", &meta, &[kw])?, span))
    }

    fn parse_case_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let subject = if self.peek_is(&Tok::Do) {
            None
        } else {
            Some(
                self.with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, scope))?
                    .root,
            )
        };
        self.expect(&Tok::Do, "`do`")?;
        self.skip_newlines();
        let mut clauses = Vec::new();
        while !self.peek_is(&Tok::End) {
            clauses.push(self.parse_case_clause(module_path, scope)?);
            self.skip_newlines();
        }
        self.expect(&Tok::End, "`end`")?;
        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        let do_body = self.builder.list(&clauses)?;
        let kw = self.builder.list(&[self.builder.keyword("do", do_body)?])?;
        let mut args = Vec::new();
        if let Some(subject) = subject {
            args.push(subject);
        }
        args.push(kw);
        Ok(ParsedExpr::plain(self.builder.call("case", &meta, &args)?, span))
    }

    fn parse_with_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
        start: Span,
    ) -> Result<ParsedExpr, FrontDoorError> {
        let mut args = Vec::new();
        loop {
            self.skip_newlines();
            let binding_start = self.cur_span();
            let left = self.with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, scope))?;
            let binding = if self.eat(&Tok::LArrow) {
                let right = self.with_trailing_do_suppressed(|parser| parser.parse_expr(module_path, scope))?;
                let span = binding_start.merge(right.span);
                let meta = self.meta(module_path, scope, span)?;
                self.builder.call("<-", &meta, &[left.root, right.root])?
            } else {
                left.root
            };
            args.push(binding);
            self.skip_newlines();
            if self.peek_is(&Tok::Comma) && !matches!(self.peek_at(1), Tok::KwKey(key) if key == "do") {
                self.bump();
                continue;
            }
            break;
        }

        let mut kw_entries = Vec::new();
        if self.peek_is(&Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(key) if key == "do") {
            self.bump();
            self.bump();
            let body = self.parse_expr(module_path, scope)?.root;
            kw_entries.push(self.builder.keyword("do", body)?);
        } else {
            self.expect(&Tok::Do, "`do`")?;
            self.skip_newlines();
            let body = self.parse_block_until(&[Tok::Else, Tok::End], module_path, scope)?;
            kw_entries.push(self.builder.keyword("do", body)?);
            if self.eat(&Tok::Else) {
                self.skip_newlines();
                let mut clauses = Vec::new();
                while !matches!(self.peek(), Tok::End | Tok::Eof) {
                    clauses.push(self.parse_case_clause(module_path, scope)?);
                    self.skip_newlines();
                }
                kw_entries.push(self.builder.keyword("else", self.builder.list(&clauses)?)?);
            }
            self.expect(&Tok::End, "`end`")?;
        }

        let span = start.merge(self.prev_span());
        let meta = self.meta(module_path, scope, span)?;
        args.push(self.builder.list(&kw_entries)?);
        Ok(ParsedExpr::plain(self.builder.call("with", &meta, &args)?, span))
    }

    fn parse_case_clause(&mut self, module_path: &[String], scope: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        let start = self.cur_span();
        let mut pattern = self.parse_expr(module_path, scope)?;
        if self.eat(&Tok::When) {
            let guard = self.parse_expr(module_path, scope)?;
            let span = pattern.span.merge(guard.span);
            let meta = self.meta(module_path, scope, span)?;
            pattern = ParsedExpr::plain(self.builder.call("when", &meta, &[pattern.root, guard.root])?, span);
        }
        self.expect(&Tok::Arrow, "`->`")?;
        let body = self.parse_expr(module_path, scope)?;
        let span = start.merge(body.span);
        let meta = self.meta(module_path, scope, span)?;
        let patterns = self.builder.list(&[pattern.root])?;
        self.builder
            .call("->", &meta, &[patterns, body.root])
            .map_err(FrontDoorError::from)
    }

    fn parse_exprs_until(
        &mut self,
        terminator: &Tok,
        module_path: &[String],
        scope: &[String],
    ) -> Result<Vec<AnyValueRef>, FrontDoorError> {
        let mut items = Vec::new();
        self.skip_newlines();
        if self.peek_is(terminator) {
            return Ok(items);
        }
        loop {
            if matches!(self.peek(), Tok::KwKey(_)) {
                items.push(self.parse_keyword_list_expr(module_path, scope)?);
            } else {
                items.push(self.parse_expr(module_path, scope)?.root);
            }
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(items)
    }

    fn parse_block_until(
        &mut self,
        terminators: &[Tok],
        module_path: &[String],
        scope: &[String],
    ) -> Result<AnyValueRef, FrontDoorError> {
        let mut exprs = Vec::new();
        self.skip_newlines();
        while !terminators.iter().any(|terminator| self.peek_is(terminator)) {
            exprs.push(self.parse_expr(module_path, scope)?.root);
            self.skip_newlines();
        }
        if exprs.len() == 1 {
            return Ok(exprs.pop().expect("single block expr"));
        }
        let span = if exprs.is_empty() {
            self.cur_span()
        } else {
            self.prev_span()
        };
        let meta = self.meta(module_path, scope, span)?;
        self.builder
            .call("__block__", &meta, &exprs)
            .map_err(FrontDoorError::from)
    }

    fn attach_trailing_do(
        &mut self,
        args: &mut Vec<AnyValueRef>,
        module_path: &[String],
        scope: &[String],
    ) -> Result<(), FrontDoorError> {
        if !self.allow_trailing_do {
            return Ok(());
        }
        let body = if matches!(self.peek(), Tok::KwKey(key) if key == "do") {
            self.bump();
            Some(self.parse_expr(module_path, scope)?.root)
        } else if self.peek_is(&Tok::Do) {
            self.bump();
            self.skip_newlines();
            let body = self.parse_block_until(&[Tok::End], module_path, scope)?;
            self.expect(&Tok::End, "`end`")?;
            Some(body)
        } else if self.peek_is(&Tok::Comma) && matches!(self.peek_at(1), Tok::KwKey(key) if key == "do") {
            self.bump();
            self.bump();
            Some(self.parse_expr(module_path, scope)?.root)
        } else {
            None
        };
        if let Some(body) = body {
            args.push(self.builder.list(&[self.builder.keyword("do", body)?])?);
        }
        Ok(())
    }

    fn parse_arity_kw_list(&mut self) -> Result<AnyValueRef, FrontDoorError> {
        self.expect(&Tok::LBrack, "`[`")?;
        let mut entries = Vec::new();
        self.skip_newlines();
        if !self.peek_is(&Tok::RBrack) {
            loop {
                let name = match self.bump() {
                    Tok::KwKey(name) => name,
                    other if self.operator_name(&other).is_some() => {
                        let name = self.operator_name(&other).expect("checked operator token").to_string();
                        self.expect(&Tok::Colon, "`:` after operator name in import/require filter list")?;
                        name
                    }
                    other => {
                        return Err(self.error(format!(
                            "expected `name:` entry in import/require filter list, got {:?}",
                            other
                        )));
                    }
                };
                let arity = match self.bump() {
                    Tok::Int(arity) if arity >= 0 => arity,
                    other => {
                        return Err(self.error(format!(
                            "expected non-negative arity after `{}:`, got {:?}",
                            name, other
                        )));
                    }
                };
                entries.push(
                    self.builder
                        .tuple(&[self.builder.atom(&name), self.builder.int(arity)])?,
                );
                self.skip_newlines();
                if !self.eat(&Tok::Comma) {
                    break;
                }
                self.skip_newlines();
            }
        }
        self.expect(&Tok::RBrack, "`]`")?;
        self.builder.list(&entries).map_err(FrontDoorError::from)
    }

    fn parse_map_entries(
        &mut self,
        module_path: &[String],
        scope: &[String],
        allow_update: bool,
    ) -> Result<Vec<AnyValueRef>, FrontDoorError> {
        let mut entries = Vec::new();
        self.skip_newlines();
        if self.peek_is(&Tok::RBrace) {
            return Ok(entries);
        }

        if allow_update && !matches!(self.peek(), Tok::KwKey(_)) {
            let base = self.parse_expr(module_path, scope)?;
            if self.eat(&Tok::Bar) {
                let updates = self.parse_keyword_entries(module_path, scope)?;
                let span = base.span.merge(self.prev_span());
                let meta = self.meta(module_path, scope, span)?;
                let kw_list = self.builder.list(&updates)?;
                entries.push(self.builder.call("|", &meta, &[base.root, kw_list])?);
                return Ok(entries);
            }
            self.expect(&Tok::FatArrow, "`=>`")?;
            let value = self.parse_expr(module_path, scope)?;
            entries.push(self.builder.tuple(&[base.root, value.root])?);
            self.skip_newlines();
            while self.eat(&Tok::Comma) {
                self.skip_newlines();
                entries.push(self.parse_map_entry(module_path, scope)?);
                self.skip_newlines();
            }
            return Ok(entries);
        }

        loop {
            entries.push(self.parse_map_entry(module_path, scope)?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(entries)
    }

    fn parse_map_entry(&mut self, module_path: &[String], scope: &[String]) -> Result<AnyValueRef, FrontDoorError> {
        if let Tok::KwKey(name) = self.peek().clone() {
            self.bump();
            let value = self.parse_expr(module_path, scope)?;
            return self.builder.keyword(&name, value.root).map_err(FrontDoorError::from);
        }

        let key = self.parse_expr(module_path, scope)?;
        self.expect(&Tok::FatArrow, "`=>`")?;
        let value = self.parse_expr(module_path, scope)?;
        self.builder
            .tuple(&[key.root, value.root])
            .map_err(FrontDoorError::from)
    }

    fn parse_keyword_entries(
        &mut self,
        module_path: &[String],
        scope: &[String],
    ) -> Result<Vec<AnyValueRef>, FrontDoorError> {
        let mut entries = Vec::new();
        loop {
            entries.push(self.parse_keyword_entry_expr(module_path, scope)?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
        }
        Ok(entries)
    }

    fn parse_keyword_list_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
    ) -> Result<AnyValueRef, FrontDoorError> {
        let mut entries = Vec::new();
        loop {
            entries.push(self.parse_keyword_entry_expr(module_path, scope)?);
            self.skip_newlines();
            if !self.eat(&Tok::Comma) {
                break;
            }
            self.skip_newlines();
            if !matches!(self.peek(), Tok::KwKey(_)) {
                return Err(self.error(format!("expected keyword entry after `,`, got {:?}", self.peek())));
            }
        }
        self.builder.list(&entries).map_err(FrontDoorError::from)
    }

    fn parse_keyword_entry_expr(
        &mut self,
        module_path: &[String],
        scope: &[String],
    ) -> Result<AnyValueRef, FrontDoorError> {
        let name = match self.bump() {
            Tok::KwKey(name) => name,
            other => return Err(self.error(format!("expected keyword entry, got {:?}", other))),
        };
        let value = self.parse_expr(module_path, scope)?;
        self.builder.keyword(&name, value.root).map_err(FrontDoorError::from)
    }

    fn improper_list(
        &self,
        items: &[AnyValueRef],
        tail: AnyValueRef,
        module_path: &[String],
        scope: &[String],
        span: Span,
    ) -> Result<AnyValueRef, FrontDoorError> {
        let Some((last, prefix)) = items.split_last() else {
            return self.err("improper list requires at least one head");
        };
        let meta = self.meta(module_path, scope, span)?;
        let mut rendered = prefix.to_vec();
        rendered.push(self.builder.call("|", &meta, &[*last, tail])?);
        self.builder.list(&rendered).map_err(FrontDoorError::from)
    }

    fn parse_upper_path(&mut self, context: &str) -> Result<Vec<String>, FrontDoorError> {
        let mut path = Vec::new();
        match self.bump() {
            Tok::Upper(name) => path.push(name),
            other => {
                return Err(self.error(format!("expected uppercase {context} path, got {:?}", other)));
            }
        }
        while self.peek_is(&Tok::Dot) {
            self.bump();
            match self.bump() {
                Tok::Upper(name) => path.push(name),
                other => {
                    return Err(self.error(format!(
                        "expected uppercase segment after `.` in {context} path, got {:?}",
                        other
                    )));
                }
            }
        }
        Ok(path)
    }

    fn parse_extern_name(&mut self) -> Result<String, FrontDoorError> {
        let first = match self.bump() {
            Tok::Ident(name) => name,
            other => return Err(self.error(format!("expected function name, got {:?}", other))),
        };
        if self.eat(&Tok::ColonColon) {
            let second = match self.bump() {
                Tok::Ident(name) => name,
                other => {
                    return Err(self.error(format!(
                        "expected extern symbol name after `{}::`, got {:?}",
                        first, other
                    )));
                }
            };
            Ok(format!("{first}::{second}"))
        } else {
            Ok(first)
        }
    }

    fn collect_balanced_tokens_until(&mut self, terminators: &[Tok]) -> Result<Vec<Token>, FrontDoorError> {
        self.skip_newlines();
        let start = self.pos;
        let mut parens = 0_u32;
        let mut brackets = 0_u32;
        let mut braces = 0_u32;
        let mut bitstrings = 0_u32;
        while !self.peek_is(&Tok::Eof) {
            let tok = self.peek().clone();
            let at_top_level = parens == 0 && brackets == 0 && braces == 0 && bitstrings == 0;
            if at_top_level
                && terminators
                    .iter()
                    .any(|terminator| discriminant(terminator) == discriminant(&tok))
            {
                break;
            }
            match tok {
                Tok::LParen => parens += 1,
                Tok::RParen if parens > 0 => parens -= 1,
                Tok::LBrack => brackets += 1,
                Tok::RBrack if brackets > 0 => brackets -= 1,
                Tok::LBrace => braces += 1,
                Tok::RBrace if braces > 0 => braces -= 1,
                Tok::LBitstr => bitstrings += 1,
                Tok::RBitstr if bitstrings > 0 => bitstrings -= 1,
                _ => {}
            }
            self.bump();
        }
        if self.pos == start {
            return Ok(Vec::new());
        }
        Ok(self.toks[start..self.pos].to_vec())
    }

    fn collect_type_fragment_tokens(&mut self, min_bp: u8) -> Result<Vec<Token>, FrontDoorError> {
        let start = self.pos;
        let mut parens = 0_u32;
        let mut brackets = 0_u32;
        let mut braces = 0_u32;
        let mut bitstrings = 0_u32;
        while !self.peek_is(&Tok::Eof) {
            let tok = self.peek().clone();
            let at_top_level = parens == 0 && brackets == 0 && braces == 0 && bitstrings == 0;
            if at_top_level {
                if matches!(
                    tok,
                    Tok::Comma
                        | Tok::Newline
                        | Tok::Eof
                        | Tok::End
                        | Tok::Do
                        | Tok::RParen
                        | Tok::RBrack
                        | Tok::RBrace
                        | Tok::RBitstr
                        | Tok::Arrow
                ) {
                    break;
                }
                if self.peek_is(&Tok::Eq) && 5 < min_bp {
                    break;
                }
                if self.peek_is(&Tok::Not) && self.peek_is_at(1, &Tok::In) && 70 < min_bp {
                    break;
                }
                if let Some((lbp, _, _)) = self.infix_bp(&tok)
                    && lbp < min_bp
                {
                    break;
                }
            }
            match tok {
                Tok::LParen => parens += 1,
                Tok::RParen if parens > 0 => parens -= 1,
                Tok::LBrack => brackets += 1,
                Tok::RBrack if brackets > 0 => brackets -= 1,
                Tok::LBrace => braces += 1,
                Tok::RBrace if braces > 0 => braces -= 1,
                Tok::LBitstr => bitstrings += 1,
                Tok::RBitstr if bitstrings > 0 => bitstrings -= 1,
                _ => {}
            }
            self.bump();
        }
        Ok(self.toks[start..self.pos].to_vec())
    }

    fn meta(
        &self,
        module_path: &[String],
        scope: &[String],
        span: Span,
    ) -> Result<QuotedSourceMetadata, FrontDoorError> {
        Ok(QuotedSourceMetadata {
            lexical_context: Some(QuotedLexicalContext::new(
                QuotedLexicalContextKind::Source,
                module_path.to_vec(),
                scope.to_vec(),
            )),
            span: Some(self.quoted_span(span)),
        })
    }

    fn quoted_span(&self, span: Span) -> QuotedSourceSpan {
        let start = span.start as usize;
        let length = span.end.saturating_sub(span.start);
        let (line, column) = line_and_column(self.source_text, start);
        QuotedSourceSpan::new(self.source_name.clone(), line, column, length)
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn peek_at(&self, off: usize) -> &Tok {
        self.toks
            .get(self.pos + off)
            .map(|token| &token.tok)
            .unwrap_or(&Tok::Eof)
    }

    fn peek_is(&self, expected: &Tok) -> bool {
        discriminant(self.peek()) == discriminant(expected)
    }

    fn peek_is_at(&self, off: usize, expected: &Tok) -> bool {
        discriminant(self.peek_at(off)) == discriminant(expected)
    }

    fn cur_span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        if self.pos == 0 {
            Span::DUMMY
        } else {
            self.toks[self.pos - 1].span
        }
    }

    fn bump(&mut self) -> Tok {
        let tok = self.toks[self.pos].tok.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        tok
    }

    fn eat(&mut self, expected: &Tok) -> bool {
        if self.peek_is(expected) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, expected: &Tok, label: &str) -> Result<(), FrontDoorError> {
        if self.eat(expected) {
            Ok(())
        } else {
            self.err(format!("expected {}, got {:?}", label, self.peek()))
        }
    }

    fn skip_newlines(&mut self) {
        while self.peek_is(&Tok::Newline) {
            self.bump();
        }
    }

    fn collect_line_tokens(&mut self) -> Result<Vec<Token>, FrontDoorError> {
        self.skip_newlines();
        let start = self.pos;
        while !matches!(self.peek(), Tok::Newline | Tok::Eof | Tok::End) {
            self.bump();
        }
        if self.pos == start {
            return self.err("expected attribute payload");
        }
        Ok(self.toks[start..self.pos].to_vec())
    }

    fn err<T>(&self, msg: impl Into<String>) -> Result<T, FrontDoorError> {
        Err(self.error(msg))
    }

    fn error(&self, msg: impl Into<String>) -> FrontDoorError {
        FrontDoorError::syntax(msg, self.cur_span())
    }

    fn with_trailing_do_suppressed<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, FrontDoorError>,
    ) -> Result<T, FrontDoorError> {
        let old = self.allow_trailing_do;
        self.allow_trailing_do = false;
        let out = f(self);
        self.allow_trailing_do = old;
        out
    }

    fn with_extern_symbol_folding_suppressed<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, FrontDoorError>,
    ) -> Result<T, FrontDoorError> {
        let old = self.allow_extern_symbol_folding;
        self.allow_extern_symbol_folding = false;
        let out = f(self);
        self.allow_extern_symbol_folding = old;
        out
    }

    fn with_type_payloads_suppressed<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<T, FrontDoorError>,
    ) -> Result<T, FrontDoorError> {
        let old = self.emit_type_payloads;
        self.emit_type_payloads = false;
        let out = f(self);
        self.emit_type_payloads = old;
        out
    }

    fn infix_bp(&self, tok: &Tok) -> Option<(u8, u8, &'static str)> {
        Some(match tok {
            Tok::Or => (20, 21, "or"),
            Tok::And => (30, 31, "and"),
            Tok::EqEq => (40, 41, "=="),
            Tok::NotEq => (40, 41, "!="),
            Tok::Lt => (50, 51, "<"),
            Tok::LtEq => (50, 51, "<="),
            Tok::Gt => (50, 51, ">"),
            Tok::GtEq => (50, 51, ">="),
            Tok::Pipe => (60, 61, "|>"),
            Tok::In => (70, 71, "in"),
            Tok::ColonColon => (80, 81, "::"),
            Tok::SlashSlash => (81, 80, "//"),
            Tok::PlusPlus => (91, 90, "++"),
            Tok::MinusMinus => (91, 90, "--"),
            Tok::Concat => (91, 90, "<>"),
            Tok::DotDot => (91, 90, ".."),
            Tok::Plus => (100, 101, "+"),
            Tok::Minus => (100, 101, "-"),
            Tok::Star => (110, 111, "*"),
            Tok::Slash => (110, 111, "/"),
            Tok::Percent => (110, 111, "%"),
            _ => return None,
        })
    }

    fn operator_name(&self, tok: &Tok) -> Option<&'static str> {
        Some(match tok {
            Tok::Plus => "+",
            Tok::Minus => "-",
            Tok::Star => "*",
            Tok::Slash => "/",
            Tok::Percent => "%",
            Tok::EqEq => "==",
            Tok::NotEq => "!=",
            Tok::Lt => "<",
            Tok::LtEq => "<=",
            Tok::Gt => ">",
            Tok::GtEq => ">=",
            Tok::Pipe => "|>",
            _ => return None,
        })
    }

    fn starts_expr_continuation(&self, tok: &Tok) -> bool {
        matches!(tok, Tok::Dot | Tok::Eq) || self.infix_bp(tok).is_some()
    }

    fn peek_after_newlines(&self) -> &Tok {
        let mut offset = 0;
        while self.peek_is_at(offset, &Tok::Newline) {
            offset += 1;
        }
        self.peek_at(offset)
    }
}

fn line_and_column(source_text: &str, byte_offset: usize) -> (u32, u32) {
    let mut line = 1_u32;
    let mut column = 1_u32;
    for byte in source_text.as_bytes().iter().take(byte_offset).copied() {
        if byte == b'\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }
    (line, column)
}

fn segments_ref(segments: &[String]) -> Vec<&str> {
    segments.iter().map(String::as_str).collect()
}
