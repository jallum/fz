use std::collections::HashMap;

use fz_runtime::any_value::AnyValueRef;

use crate::ast::{Attribute, TypeAliasDecl, TypeExprBody};
use crate::compiler::source::{Id as SourceId, Span};
use crate::modules::identity::ModuleName;
use crate::parser::lexer::Tok;

use super::code::CodeId;
use super::source::{QuotedAstNode, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use super::token_payload;

const META_SPAN_KEY: &str = "__fz_span__";

#[derive(Clone, Copy)]
pub struct SurfaceSourceContext<'a> {
    pub code_id: CodeId,
    pub code_text: &'a str,
}

impl<'a> SurfaceSourceContext<'a> {
    pub fn new(code_id: CodeId, code_text: &'a str) -> Self {
        Self { code_id, code_text }
    }
}

#[derive(Debug, Clone)]
pub struct ScopeSurface {
    pub attrs: Vec<Attribute>,
    pub forms: Vec<ScopeForm>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum ScopeForm {
    Alias(AliasForm),
    Import(ImportForm),
    Require(ImportForm),
    CompilerService(CompilerServiceForm),
    Function(FunctionForm),
    Module(ModuleForm),
    Protocol(ProtocolForm),
    ProtocolImpl(ProtocolImplForm),
    Struct(StructForm),
    MacroCall(MacroCallForm),
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AliasForm {
    pub path: Vec<String>,
    pub as_name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ImportForm {
    pub path: Vec<String>,
    pub only: Option<Vec<(String, usize)>>,
    pub except: Option<Vec<(String, usize)>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct CompilerServiceForm {
    pub service: CompilerService,
    pub source: QuotedSourceRoot,
    pub env: QuotedSourceRoot,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilerService {
    Define,
}

#[derive(Debug, Clone)]
pub struct FunctionForm {
    pub source: QuotedSourceRoot,
    pub name: String,
    pub arity: usize,
    pub is_macro: bool,
    pub is_private: bool,
    pub variadic: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ModuleForm {
    pub source: QuotedSourceRoot,
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ProtocolForm {
    pub source: QuotedSourceRoot,
    pub name: ModuleName,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ProtocolImplForm {
    pub source: QuotedSourceRoot,
    pub protocol: ModuleName,
    pub target: ModuleName,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct StructForm {
    pub source: QuotedSourceRoot,
    pub fields: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct MacroCallForm {
    pub source: QuotedSourceRoot,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionGroupKey {
    name: String,
    arity: usize,
}

#[derive(Debug, Clone)]
struct PendingFunctionGroup {
    item_roots: Vec<AnyValueRef>,
    kind: String,
}

type ImportFilterList = Vec<(String, usize)>;
type ImportKeywordArgs = Vec<(String, ImportFilterList)>;

pub fn read_scope_surface(
    source: &QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ScopeSurface, QuotedSourceError> {
    let quoted_items = source.cursor().list_items()?;
    let mut attrs = Vec::new();
    let mut forms = Vec::new();
    let mut group_order: Vec<FunctionGroupKey> = Vec::new();
    let mut groups: HashMap<FunctionGroupKey, PendingFunctionGroup> = HashMap::new();
    let mut pending_function_attrs = Vec::new();

    for quoted_item in quoted_items {
        let Some(node) = quoted_item.ast_node()? else {
            return Err(QuotedSourceError::new("expected quoted item AST node"));
        };
        let head_name = match node.head.atom_name() {
            Ok(head_name) => head_name,
            Err(_) => {
                flush_function_groups(source, ctx, &mut forms, &mut group_order, &mut groups)?;
                pending_function_attrs.clear();
                forms.push(build_form(source.subroot(quoted_item.root()), ctx)?);
                continue;
            }
        };
        if head_name.starts_with('@') {
            if matches!(head_name.as_str(), "@doc" | "@spec") {
                pending_function_attrs.push(quoted_item.root());
            } else {
                attrs.push(parse_scope_attr(&quoted_item, ctx)?);
            }
            continue;
        }

        match head_name.as_str() {
            "fn" | "fnp" | "defmacro" => {
                let key = parse_function_group_key(&source.subroot(quoted_item.root()))?;
                let order_key = key.clone();
                let entry = groups.entry(key.clone()).or_insert_with(|| {
                    group_order.push(order_key);
                    PendingFunctionGroup {
                        item_roots: Vec::new(),
                        kind: head_name.clone(),
                    }
                });
                if entry.kind != head_name {
                    return Err(QuotedSourceError::new(format!(
                        "quoted function group `{}/{} ` mixes `{}` and `{}` heads",
                        key.name, key.arity, entry.kind, head_name
                    )));
                }
                entry.item_roots.append(&mut pending_function_attrs);
                entry.item_roots.push(quoted_item.root());
            }
            "extern" => {
                flush_function_groups(source, ctx, &mut forms, &mut group_order, &mut groups)?;
                let mut item_roots = std::mem::take(&mut pending_function_attrs);
                item_roots.push(quoted_item.root());
                let grouped = source.interned_list_subroot(&item_roots)?;
                forms.push(build_form(grouped, ctx)?);
            }
            _ => {
                flush_function_groups(source, ctx, &mut forms, &mut group_order, &mut groups)?;
                pending_function_attrs.clear();
                forms.push(build_form(source.subroot(quoted_item.root()), ctx)?);
            }
        }
    }

    flush_function_groups(source, ctx, &mut forms, &mut group_order, &mut groups)?;
    Ok(ScopeSurface { attrs, forms })
}

pub fn read_module_body_surface(
    form: &ModuleForm,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ScopeSurface, QuotedSourceError> {
    read_do_body_surface(&form.source, ctx)
}

pub fn read_protocol_body_surface(
    form: &ProtocolForm,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ScopeSurface, QuotedSourceError> {
    read_do_body_surface(&form.source, ctx)
}

pub fn read_protocol_impl_body_surface(
    form: &ProtocolImplForm,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ScopeSurface, QuotedSourceError> {
    read_do_body_surface(&form.source, ctx)
}

fn read_do_body_surface(
    source: &QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ScopeSurface, QuotedSourceError> {
    let body = extract_do_body_list_root(source)?;
    read_scope_surface(&body, ctx)
}

fn flush_function_groups(
    source: &QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
    forms: &mut Vec<ScopeForm>,
    order: &mut Vec<FunctionGroupKey>,
    groups: &mut HashMap<FunctionGroupKey, PendingFunctionGroup>,
) -> Result<(), QuotedSourceError> {
    for key in order.drain(..) {
        if let Some(group) = groups.remove(&key) {
            let grouped = source.interned_list_subroot(&group.item_roots)?;
            forms.push(build_form(grouped, ctx)?);
        }
    }
    Ok(())
}

fn build_form(source: QuotedSourceRoot, ctx: &SurfaceSourceContext<'_>) -> Result<ScopeForm, QuotedSourceError> {
    if let Some(service) = parse_compiler_service_form(source.clone(), ctx)? {
        return Ok(ScopeForm::CompilerService(service));
    }

    let head = match surface_head_name(&source) {
        Ok(head) => head,
        Err(_error) if source.cursor().ast_node()?.is_some() => {
            return Ok(ScopeForm::MacroCall(MacroCallForm {
                span: surface_span(&source, ctx)?,
                source,
            }));
        }
        Err(error) => return Err(error),
    };
    match head.as_str() {
        "alias" => Ok(ScopeForm::Alias(parse_alias_form(source, ctx)?)),
        "import" => Ok(ScopeForm::Import(parse_import_form(source, ctx)?)),
        "require" => Ok(ScopeForm::Require(parse_import_form(source, ctx)?)),
        "fn" | "fnp" | "defmacro" | "extern" => Ok(ScopeForm::Function(parse_function_form(source, ctx)?)),
        "defmodule" => Ok(ScopeForm::Module(parse_module_form(source, ctx)?)),
        "defprotocol" => Ok(ScopeForm::Protocol(parse_protocol_form(source, ctx)?)),
        "defimpl" => Ok(ScopeForm::ProtocolImpl(parse_protocol_impl_form(source, ctx)?)),
        "defstruct" => Ok(ScopeForm::Struct(parse_struct_form(source, ctx)?)),
        _ => Ok(ScopeForm::MacroCall(MacroCallForm {
            span: surface_span(&source, ctx)?,
            source,
        })),
    }
}

fn parse_compiler_service_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<Option<CompilerServiceForm>, QuotedSourceError> {
    let Some(node) = source.cursor().ast_node()? else {
        return Ok(None);
    };
    let Some(callee) = node.head.ast_node()? else {
        return Ok(None);
    };
    if callee.head.atom_name()? != "." {
        return Ok(None);
    }
    let callee_parts = callee.tail.list_items()?;
    if callee_parts.len() != 2 {
        return Ok(None);
    }
    if !matches_alias(&callee_parts[0], &["Fz", "Compiler"])? {
        return Ok(None);
    }
    let service = match callee_parts[1].atom_name()?.as_str() {
        "define" => CompilerService::Define,
        other => {
            return Err(QuotedSourceError::new(format!(
                "unsupported Fz.Compiler service `{other}`"
            )));
        }
    };
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedSourceError::new(
            "Fz.Compiler.define expects source root and __ENV__ arguments",
        ));
    }
    Ok(Some(CompilerServiceForm {
        service,
        source: source.subroot(args[0].root()),
        env: source.subroot(args[1].root()),
        span: span_from_meta(&node.meta, ctx)?,
    }))
}

fn matches_alias(cursor: &QuotedSourceCursor, expected: &[&str]) -> Result<bool, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Ok(false);
    };
    if node.head.atom_name()? != "__aliases__" {
        return Ok(false);
    }
    let segments = node.tail.list_atom_names()?;
    Ok(segments.iter().map(String::as_str).eq(expected.iter().copied()))
}

fn parse_scope_attr(
    cursor: &QuotedSourceCursor,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<Attribute, QuotedSourceError> {
    let node = expect_ast_cursor_node(cursor, "scope attribute")?;
    let head = node.head.atom_name()?;
    let args = node.tail.list_items()?;
    let Some(value) = args.first() else {
        return Err(QuotedSourceError::new(format!(
            "quoted scope attribute `{head}` is missing its payload"
        )));
    };
    let span = span_from_meta(&node.meta, ctx)?;
    match head.as_str() {
        "@moduledoc" => Ok(Attribute::ModuleDoc(value.utf8_binary_text()?)),
        "@type" => decode_type_alias_attr(value, span),
        other => Err(QuotedSourceError::new(format!(
            "unsupported quoted scope attribute `{other}`"
        ))),
    }
}

fn decode_type_alias_attr(payload: &QuotedSourceCursor, span: Span) -> Result<Attribute, QuotedSourceError> {
    let mut tokens = token_payload::decode_tokens(payload)?
        .into_iter()
        .filter(|token| !matches!(token.tok, Tok::Newline | Tok::Eof))
        .peekable();

    let name = match tokens.next().map(|token| token.tok) {
        Some(Tok::Upper(name)) | Some(Tok::Ident(name)) => name,
        Some(other) => {
            return Err(QuotedSourceError::new(format!(
                "expected type-alias name after `@type`, got {:?}",
                other
            )));
        }
        None => return Err(QuotedSourceError::new("expected type-alias name after `@type`")),
    };

    let mut params = Vec::new();
    if matches!(tokens.peek().map(|token| &token.tok), Some(Tok::LParen)) {
        tokens.next();
        if !matches!(tokens.peek().map(|token| &token.tok), Some(Tok::RParen)) {
            loop {
                match tokens.next().map(|token| token.tok) {
                    Some(Tok::Ident(param)) => params.push(param),
                    Some(other) => {
                        return Err(QuotedSourceError::new(format!(
                            "expected type parameter name in `@type` head, got {:?}",
                            other
                        )));
                    }
                    None => return Err(QuotedSourceError::new("expected type parameter name in `@type` head")),
                }
                if !matches!(tokens.peek().map(|token| &token.tok), Some(Tok::Comma)) {
                    break;
                }
                tokens.next();
            }
        }
        match tokens.next().map(|token| token.tok) {
            Some(Tok::RParen) => {}
            Some(other) => {
                return Err(QuotedSourceError::new(format!(
                    "expected `)` after `@type` parameters, got {:?}",
                    other
                )));
            }
            None => return Err(QuotedSourceError::new("expected `)` after `@type` parameters")),
        }
    }

    match tokens.next().map(|token| token.tok) {
        Some(Tok::ColonColon) => {}
        Some(other) => {
            return Err(QuotedSourceError::new(format!(
                "expected `::` in `@type`, got {:?}",
                other
            )));
        }
        None => return Err(QuotedSourceError::new("expected `::` in `@type`")),
    }

    let body_tokens = tokens.collect::<Vec<_>>();
    if body_tokens.is_empty() {
        return Err(QuotedSourceError::new(
            "expected type expression body after `::` in `@type`",
        ));
    }

    Ok(Attribute::TypeAlias(TypeAliasDecl {
        name,
        name_span: span,
        params,
        body_tokens: TypeExprBody(body_tokens),
        span,
    }))
}

fn parse_alias_form(source: QuotedSourceRoot, ctx: &SurfaceSourceContext<'_>) -> Result<AliasForm, QuotedSourceError> {
    let node = expect_surface_node(&source)?;
    let span = span_from_meta(&node.meta, ctx)?;
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("alias expects a target path"));
    }
    let path = parse_alias_segments(&args[0])?;
    let as_name = if let Some(kwargs) = args.get(1) {
        parse_alias_keyword_args(kwargs)?
    } else {
        None
    }
    .unwrap_or_else(|| path.last().cloned().unwrap_or_default());
    Ok(AliasForm { path, as_name, span })
}

fn parse_import_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ImportForm, QuotedSourceError> {
    let node = expect_surface_node(&source)?;
    let span = span_from_meta(&node.meta, ctx)?;
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("import/require expects a target path"));
    }
    let path = parse_alias_segments(&args[0])?;
    let mut only = None;
    let mut except = None;
    if let Some(kwargs) = args.get(1) {
        for (kind, entries) in parse_import_keyword_args(kwargs)? {
            match kind.as_str() {
                "only" => only = Some(entries),
                "except" => except = Some(entries),
                _ => {}
            }
        }
    }
    Ok(ImportForm {
        path,
        only,
        except,
        span,
    })
}

fn parse_function_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<FunctionForm, QuotedSourceError> {
    let span = surface_span(&source, ctx)?;
    let head = surface_head_name(&source)?;
    if head == "extern" {
        let node = first_non_attr_node(&source)?;
        let args = node.tail.list_items()?;
        if args.len() != 2 {
            return Err(QuotedSourceError::new("quoted extern expects ABI and detail map"));
        }
        let details = &args[1];
        let name = details
            .map_value("name")?
            .ok_or_else(|| QuotedSourceError::new("quoted extern is missing `name`"))?
            .utf8_binary_text()?;
        let arity = details
            .map_value("params")?
            .ok_or_else(|| QuotedSourceError::new("quoted extern is missing `params`"))?
            .list_items()?
            .len();
        let variadic = decode_bool(
            &details
                .map_value("variadic")?
                .ok_or_else(|| QuotedSourceError::new("quoted extern is missing `variadic`"))?,
        )?;
        return Ok(FunctionForm {
            source,
            name,
            arity,
            is_macro: false,
            is_private: false,
            variadic,
            span,
        });
    }

    let FunctionGroupKey { name, arity } = parse_function_group_key(&source)?;
    Ok(FunctionForm {
        source,
        name,
        arity,
        is_macro: head == "defmacro",
        is_private: head == "fnp",
        variadic: false,
        span,
    })
}

fn parse_module_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ModuleForm, QuotedSourceError> {
    let node = expect_surface_node(&source)?;
    let span = span_from_meta(&node.meta, ctx)?;
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("defmodule expects a module alias"));
    }
    let name = parse_alias_segments(&args[0])?.join(".");
    Ok(ModuleForm { source, name, span })
}

fn parse_protocol_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ProtocolForm, QuotedSourceError> {
    let node = expect_surface_node(&source)?;
    let span = span_from_meta(&node.meta, ctx)?;
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("defprotocol expects a protocol alias"));
    }
    let name = ModuleName::from_segments(parse_alias_segments(&args[0])?);
    Ok(ProtocolForm { source, name, span })
}

fn parse_protocol_impl_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<ProtocolImplForm, QuotedSourceError> {
    let node = expect_surface_node(&source)?;
    let span = span_from_meta(&node.meta, ctx)?;
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedSourceError::new(
            "defimpl expects a protocol alias and keyword args",
        ));
    }
    let protocol = ModuleName::from_segments(parse_alias_segments(&args[0])?);
    let kwargs = args[1].list_items()?;
    let target = kwargs
        .into_iter()
        .find_map(|entry| {
            let tuple = entry.tuple_items().ok()?;
            if tuple.len() != 2 || tuple[0].atom_name().ok().as_deref() != Some("for") {
                return None;
            }
            parse_alias_segments(&tuple[1]).ok().map(ModuleName::from_segments)
        })
        .ok_or_else(|| QuotedSourceError::new("defimpl is missing `for:` target"))?;
    Ok(ProtocolImplForm {
        source,
        protocol,
        target,
        span,
    })
}

fn parse_struct_form(
    source: QuotedSourceRoot,
    ctx: &SurfaceSourceContext<'_>,
) -> Result<StructForm, QuotedSourceError> {
    let node = expect_surface_node(&source)?;
    let span = span_from_meta(&node.meta, ctx)?;
    let args = node.tail.list_items()?;
    let Some(fields) = args.first() else {
        return Err(QuotedSourceError::new("defstruct expects a field list"));
    };
    let fields = fields.list_atom_names()?;
    Ok(StructForm { source, fields, span })
}

fn parse_function_group_key(root: &QuotedSourceRoot) -> Result<FunctionGroupKey, QuotedSourceError> {
    let node = first_non_attr_node(root)?;
    let args = node.tail.list_items()?;
    let Some(head) = args.first() else {
        return Err(QuotedSourceError::new(
            "quoted function clause is missing its head expression",
        ));
    };
    parse_function_head_key(head)
}

fn parse_function_head_key(cursor: &QuotedSourceCursor) -> Result<FunctionGroupKey, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Err(QuotedSourceError::new("expected quoted function head AST node"));
    };
    if node.head.atom_name()? == "when" {
        let args = node.tail.list_items()?;
        let Some(inner) = args.first() else {
            return Err(QuotedSourceError::new(
                "quoted `when` head is missing the guarded function head",
            ));
        };
        return parse_function_head_key(inner);
    }
    Ok(FunctionGroupKey {
        name: node.head.atom_name()?,
        arity: node.tail.list_items()?.len(),
    })
}

fn parse_alias_segments(cursor: &QuotedSourceCursor) -> Result<Vec<String>, QuotedSourceError> {
    let Some(node) = cursor.ast_node()? else {
        return Err(QuotedSourceError::new("expected alias AST node"));
    };
    if node.head.atom_name()? != "__aliases__" {
        return Err(QuotedSourceError::new("expected __aliases__ node"));
    }
    node.tail.list_atom_names()
}

fn parse_import_keyword_args(cursor: &QuotedSourceCursor) -> Result<ImportKeywordArgs, QuotedSourceError> {
    let mut out = Vec::new();
    for entry in cursor.list_items()? {
        let tuple = entry.tuple_items()?;
        if tuple.len() != 2 {
            return Err(QuotedSourceError::new("expected keyword tuple"));
        }
        let kind = tuple[0].atom_name()?;
        let values = tuple[1]
            .list_items()?
            .into_iter()
            .map(|value| {
                let tuple = value.tuple_items()?;
                if tuple.len() != 2 {
                    return Err(QuotedSourceError::new("expected import filter tuple"));
                }
                Ok((tuple[0].atom_name()?, tuple[1].int_value()? as usize))
            })
            .collect::<Result<Vec<_>, _>>()?;
        out.push((kind, values));
    }
    Ok(out)
}

fn parse_alias_keyword_args(cursor: &QuotedSourceCursor) -> Result<Option<String>, QuotedSourceError> {
    for entry in cursor.list_items()? {
        let tuple = entry.tuple_items()?;
        if tuple.len() != 2 {
            return Err(QuotedSourceError::new("expected alias keyword tuple"));
        }
        if tuple[0].atom_name()? == "as" {
            let path = parse_alias_segments(&tuple[1])?;
            return path
                .last()
                .cloned()
                .map(Some)
                .ok_or_else(|| QuotedSourceError::new("alias `as:` expects a module alias"));
        }
    }
    Ok(None)
}

fn decode_bool(cursor: &QuotedSourceCursor) -> Result<bool, QuotedSourceError> {
    match cursor.atom_name()?.as_str() {
        "true" => Ok(true),
        "false" => Ok(false),
        other => Err(QuotedSourceError::new(format!("expected boolean atom, got `{other}`"))),
    }
}

fn extract_do_body_list_root(root: &QuotedSourceRoot) -> Result<QuotedSourceRoot, QuotedSourceError> {
    let Some(node) = root.cursor().ast_node()? else {
        return Err(QuotedSourceError::new("expected quoted call node with a do body"));
    };
    let args = node.tail.list_items()?;
    let Some(kwargs) = args.get(1) else {
        return Err(QuotedSourceError::new("expected quoted call keyword args"));
    };
    for entry in kwargs.list_items()? {
        let tuple = entry.tuple_items()?;
        if tuple.len() != 2 {
            return Err(QuotedSourceError::new("expected keyword tuple in quoted do body"));
        }
        if tuple[0].atom_name()? == "do" {
            return Ok(root.subroot(tuple[1].root()));
        }
    }
    Err(QuotedSourceError::new("expected quoted do-body keyword"))
}

fn surface_head_name(root: &QuotedSourceRoot) -> Result<String, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node()? {
        return node.head.atom_name();
    }
    first_non_attr_node(root)?.head.atom_name()
}

fn first_non_attr_node(root: &QuotedSourceRoot) -> Result<QuotedAstNode, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node()? {
        return Ok(node);
    }
    for item in root.cursor().list_items()? {
        let Some(node) = item.ast_node()? else {
            return Err(QuotedSourceError::new("expected quoted grouped surface item AST node"));
        };
        let head = node.head.atom_name()?;
        if !head.starts_with('@') {
            return Ok(node);
        }
    }
    Err(QuotedSourceError::new(
        "expected grouped quoted surface to contain a non-attribute form",
    ))
}

fn expect_surface_node(root: &QuotedSourceRoot) -> Result<QuotedAstNode, QuotedSourceError> {
    root.cursor()
        .ast_node()?
        .ok_or_else(|| QuotedSourceError::new("expected quoted item AST node"))
}

fn expect_ast_cursor_node(cursor: &QuotedSourceCursor, label: &str) -> Result<QuotedAstNode, QuotedSourceError> {
    cursor
        .ast_node()?
        .ok_or_else(|| QuotedSourceError::new(format!("expected {label} AST node")))
}

fn surface_span(root: &QuotedSourceRoot, ctx: &SurfaceSourceContext<'_>) -> Result<Span, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node()? {
        return span_from_meta(&node.meta, ctx);
    }
    let mut merged: Option<Span> = None;
    for item in root.cursor().list_items()? {
        let Some(node) = item.ast_node()? else {
            return Err(QuotedSourceError::new("expected grouped quoted surface item AST node"));
        };
        let span = span_from_meta(&node.meta, ctx)?;
        merged = Some(match merged {
            Some(current) => current.merge(span),
            None => span,
        });
    }
    Ok(merged.unwrap_or(Span::DUMMY))
}

fn span_from_meta(meta: &QuotedSourceCursor, ctx: &SurfaceSourceContext<'_>) -> Result<Span, QuotedSourceError> {
    let Some(span_map) = meta.map_value(META_SPAN_KEY)? else {
        return Ok(Span::DUMMY);
    };
    let line = span_map
        .map_value("line")?
        .ok_or_else(|| QuotedSourceError::new("quoted span is missing `line`"))?
        .int_value()? as u32;
    let column = span_map
        .map_value("column")?
        .ok_or_else(|| QuotedSourceError::new("quoted span is missing `column`"))?
        .int_value()? as u32;
    let length = span_map
        .map_value("length")?
        .ok_or_else(|| QuotedSourceError::new("quoted span is missing `length`"))?
        .int_value()? as u32;
    let start = byte_offset_from_line_col(ctx.code_text, line, column)?;
    Ok(Span::new(
        SourceId(ctx.code_id.as_u32()),
        start,
        start.saturating_add(length),
    ))
}

fn byte_offset_from_line_col(source: &str, line: u32, column: u32) -> Result<u32, QuotedSourceError> {
    if line == 0 || column == 0 {
        return Err(QuotedSourceError::new("quoted span line/column must be 1-based"));
    }
    let mut current_line = 1_u32;
    let mut current_col = 1_u32;
    for (index, byte) in source.as_bytes().iter().copied().enumerate() {
        if current_line == line && current_col == column {
            return Ok(index as u32);
        }
        if byte == b'\n' {
            current_line += 1;
            current_col = 1;
        } else {
            current_col += 1;
        }
    }
    if current_line == line && current_col == column {
        return Ok(source.len() as u32);
    }
    Err(QuotedSourceError::new(format!(
        "quoted span line/column {line}:{column} is outside the source text",
    )))
}
