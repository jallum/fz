use std::collections::HashMap;

use fz_runtime::any_value::AnyValueRef;

use crate::ast::{Attribute, TypeAliasDecl, TypeExprBody};
use crate::modules::identity::ModuleName;
use crate::parser::lexer::Tok;
use crate::source::{SourceMap, Span};

use super::source::{QuotedAstNode, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use super::token_payload;

#[derive(Debug, Clone)]
pub struct ScopeSurface {
    pub attrs: Vec<Attribute>,
    pub forms: Vec<ScopeForm>,
}

pub(crate) fn is_function_definition_head(head: &str) -> bool {
    matches!(head, "fn" | "fnp" | "defmacro")
}

pub(crate) fn is_scope_definition_head(head: &str) -> bool {
    is_function_definition_head(head) || matches!(head, "defmodule" | "defprotocol" | "defimpl")
}

#[derive(Debug, Clone)]
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
    pub name: ModuleName,
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
pub struct StructForm {
    pub source: QuotedSourceRoot,
    pub fields: Vec<String>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct MacroCallForm {
    pub source: QuotedSourceRoot,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub(crate) enum ReservedSourceDefinition {
    Function { name: String, arity: usize, is_macro: bool },
    Module { name: ModuleName },
    Protocol { name: ModuleName },
    ProtocolImpl,
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

/// Reads user surface: there is exactly one source read, and a def-head
/// (`fn`/`fnp`/`defmacro`/`defmodule`/...) is just a macro call to be expanded
/// later. Structure is never re-parsed from source here; it emerges from the
/// expand -> `Fz.Compiler.define` -> define pipeline.
pub fn read_scope_surface(source: &QuotedSourceRoot, sources: &SourceMap) -> Result<ScopeSurface, QuotedSourceError> {
    read_surface(source, sources)
}

/// Reads canonical content — the bootstrap source and any post-expansion node
/// (a `Fz.Compiler.define` payload, item-macro output, protocol/impl bodies).
/// Identical to the user read, then every def-head the user read left as a
/// `MacroCall` is extracted into its typed [`ScopeForm`] via
/// [`build_definition_form`]: in canonical content a def-head is a definition to
/// extract, not a macro to expand.
pub fn read_compiler_fragment_surface(
    source: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<ScopeSurface, QuotedSourceError> {
    canonicalize_definitions(read_surface(source, sources)?, sources)
}

/// Extracts the typed definitions out of an already-read surface. A def-head
/// that the user reader produced as a `MacroCall` becomes its typed form; every
/// other form passes through unchanged.
fn canonicalize_definitions(surface: ScopeSurface, sources: &SourceMap) -> Result<ScopeSurface, QuotedSourceError> {
    let ScopeSurface { attrs, forms } = surface;
    let mut canonical = Vec::with_capacity(forms.len());
    for form in forms {
        match form {
            ScopeForm::MacroCall(call) => match surface_head_name(&call.source, sources)? {
                Some(head) if is_scope_definition_head(&head) => {
                    canonical.push(build_definition_form(call.source, &head, sources)?);
                }
                _ => canonical.push(ScopeForm::MacroCall(call)),
            },
            other => canonical.push(other),
        }
    }
    Ok(ScopeSurface {
        attrs,
        forms: canonical,
    })
}

fn read_surface(source: &QuotedSourceRoot, sources: &SourceMap) -> Result<ScopeSurface, QuotedSourceError> {
    let quoted_items = source.cursor().list_items()?;
    let mut attrs = Vec::new();
    let mut forms = Vec::new();
    let mut group_order: Vec<FunctionGroupKey> = Vec::new();
    let mut groups: HashMap<FunctionGroupKey, PendingFunctionGroup> = HashMap::new();
    let mut pending_function_attrs = Vec::new();

    for quoted_item in quoted_items {
        let Some(node) = quoted_item.ast_node(sources)? else {
            return Err(QuotedSourceError::new("expected quoted item AST node"));
        };
        if node.head.root().tag() != fz_runtime::any_value::ValueKind::ATOM {
            flush_function_groups(source, &mut forms, &mut group_order, &mut groups, sources)?;
            reject_dangling_function_attrs(source, &pending_function_attrs, sources)?;
            forms.push(build_form(source.subroot(quoted_item.root()), sources)?);
            continue;
        }
        let head_name = node.head.atom_name()?;
        if head_name.starts_with('@') {
            if matches!(head_name.as_str(), "@doc" | "@spec") {
                pending_function_attrs.push(quoted_item.root());
            } else {
                attrs.push(parse_scope_attr(&quoted_item, sources)?);
            }
            continue;
        }

        match head_name.as_str() {
            head if is_function_definition_head(head) => {
                let key = parse_function_group_key(&source.subroot(quoted_item.root()), sources)?;
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
                flush_function_groups(source, &mut forms, &mut group_order, &mut groups, sources)?;
                let mut item_roots = std::mem::take(&mut pending_function_attrs);
                item_roots.push(quoted_item.root());
                let grouped = source.interned_list_subroot(&item_roots)?;
                forms.push(build_form(grouped, sources)?);
            }
            _ => {
                flush_function_groups(source, &mut forms, &mut group_order, &mut groups, sources)?;
                reject_dangling_function_attrs(source, &pending_function_attrs, sources)?;
                forms.push(build_form(source.subroot(quoted_item.root()), sources)?);
            }
        }
    }

    flush_function_groups(source, &mut forms, &mut group_order, &mut groups, sources)?;
    reject_dangling_function_attrs(source, &pending_function_attrs, sources)?;
    Ok(ScopeSurface { attrs, forms })
}

pub fn read_module_body_surface(form: &ModuleForm, sources: &SourceMap) -> Result<ScopeSurface, QuotedSourceError> {
    read_do_body_surface(&form.source, sources)
}

pub fn read_protocol_body_surface(form: &ProtocolForm, sources: &SourceMap) -> Result<ScopeSurface, QuotedSourceError> {
    canonicalize_definitions(read_do_body_surface(&form.source, sources)?, sources)
}

pub fn read_protocol_impl_body_surface(
    form: &ProtocolImplForm,
    sources: &SourceMap,
) -> Result<ScopeSurface, QuotedSourceError> {
    canonicalize_definitions(read_do_body_surface(&form.source, sources)?, sources)
}

fn read_do_body_surface(source: &QuotedSourceRoot, sources: &SourceMap) -> Result<ScopeSurface, QuotedSourceError> {
    let body = extract_do_body_list_root(source, sources)?;
    read_surface(&body, sources)
}

/// A pending `@doc`/`@spec` attaches to the NEXT function group (or extern).
/// Reaching a non-function form or the end of scope with attrs still pending
/// means they attach to nothing — a source-surface error reported here,
/// where the dangling attribute is visible, instead of degrading into a
/// confusing unknown-export diagnostic when the described function is rooted
/// later.
fn reject_dangling_function_attrs(
    source: &QuotedSourceRoot,
    pending: &[AnyValueRef],
    sources: &SourceMap,
) -> Result<(), QuotedSourceError> {
    let Some(root) = pending.first() else {
        return Ok(());
    };
    let attr_root = source.subroot(*root);
    let head = attr_root
        .cursor()
        .ast_node(sources)?
        .map(|node| node.head.atom_name())
        .transpose()?
        .unwrap_or_else(|| "@doc/@spec".to_string());
    let span = surface_span(&attr_root, sources)?;
    Err(QuotedSourceError::user(
        crate::diag::codes::PARSE_DANGLING_FUNCTION_ATTR,
        Some(span),
        format!(
            "`{head}` does not attach to any function definition: function attributes must be followed by their function's clauses",
        ),
    ))
}

fn flush_function_groups(
    source: &QuotedSourceRoot,
    forms: &mut Vec<ScopeForm>,
    order: &mut Vec<FunctionGroupKey>,
    groups: &mut HashMap<FunctionGroupKey, PendingFunctionGroup>,
    sources: &SourceMap,
) -> Result<(), QuotedSourceError> {
    for key in order.drain(..) {
        if let Some(group) = groups.remove(&key) {
            let grouped = source.interned_list_subroot(&group.item_roots)?;
            forms.push(build_form(grouped, sources)?);
        }
    }
    Ok(())
}

/// Builds the typed [`ScopeForm`] for a recognized scope-definition head
/// (`fn`/`fnp`/`defmacro`/`defmodule`/`defprotocol`/`defimpl`). This is the
/// canonical structural extraction of a def-head — the analogue of Elixir
/// `store_definition`/module compile — invoked by the define pipeline and the
/// bootstrap. It does not depend on any surface-read mode: it always extracts a
/// definition from a node already known to be a def-head.
pub(crate) fn build_definition_form(
    source: QuotedSourceRoot,
    head: &str,
    sources: &SourceMap,
) -> Result<ScopeForm, QuotedSourceError> {
    Ok(match head {
        head if is_function_definition_head(head) => ScopeForm::Function(parse_function_form(source, sources)?),
        "defmodule" => ScopeForm::Module(parse_module_form(source, sources)?),
        "defprotocol" => ScopeForm::Protocol(parse_protocol_form(source, sources)?),
        "defimpl" => ScopeForm::ProtocolImpl(parse_protocol_impl_form(source, sources)?),
        _ => unreachable!("covered by is_scope_definition_head"),
    })
}

fn build_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<ScopeForm, QuotedSourceError> {
    if let Some(service) = parse_compiler_service_form(source.clone(), sources)? {
        return Ok(ScopeForm::CompilerService(service));
    }

    let head = match surface_head_name(&source, sources)? {
        Some(head) => head,
        None if source.cursor().ast_node(sources)?.is_some() => {
            return Ok(ScopeForm::MacroCall(MacroCallForm {
                span: surface_span(&source, sources)?,
                source,
            }));
        }
        None => return Err(QuotedSourceError::new("expected quoted item AST node")),
    };
    match head.as_str() {
        "alias" => Ok(ScopeForm::Alias(parse_alias_form(source, sources)?)),
        "import" => Ok(ScopeForm::Import(parse_import_form(source, sources)?)),
        "require" => Ok(ScopeForm::Require(parse_import_form(source, sources)?)),
        head if is_scope_definition_head(head) => Ok(ScopeForm::MacroCall(MacroCallForm {
            span: surface_span(&source, sources)?,
            source,
        })),
        "extern" => Ok(ScopeForm::Function(parse_function_form(source, sources)?)),
        "defstruct" => Ok(ScopeForm::Struct(parse_struct_form(source, sources)?)),
        _ => Ok(ScopeForm::MacroCall(MacroCallForm {
            span: surface_span(&source, sources)?,
            source,
        })),
    }
}

fn parse_compiler_service_form(
    source: QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<Option<CompilerServiceForm>, QuotedSourceError> {
    let Some(node) = source.cursor().ast_node(sources)? else {
        return Ok(None);
    };
    let Some(callee) = node.head.ast_node(sources)? else {
        return Ok(None);
    };
    if callee.head.atom_name()? != "." {
        return Ok(None);
    }
    let callee_parts = callee.tail.list_items()?;
    if callee_parts.len() != 2 {
        return Ok(None);
    }
    if !matches_alias(&callee_parts[0], &["Fz", "Compiler"], sources)? {
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
        span: node.span.unwrap_or(Span::DUMMY),
    }))
}

fn matches_alias(
    cursor: &QuotedSourceCursor,
    expected: &[&str],
    sources: &SourceMap,
) -> Result<bool, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(false);
    };
    if node.head.atom_name()? != "__aliases__" {
        return Ok(false);
    }
    let segments = node.tail.list_atom_names()?;
    Ok(segments.iter().map(String::as_str).eq(expected.iter().copied()))
}

fn parse_scope_attr(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Attribute, QuotedSourceError> {
    let node = expect_ast_cursor_node(cursor, "scope attribute", sources)?;
    let head = node.head.atom_name()?;
    let args = node.tail.list_items()?;
    let Some(value) = args.first() else {
        return Err(QuotedSourceError::new(format!(
            "quoted scope attribute `{head}` is missing its payload"
        )));
    };
    let span = node.span.unwrap_or(Span::DUMMY);
    match head.as_str() {
        "@moduledoc" => Ok(Attribute::ModuleDoc(value.utf8_binary_text()?)),
        "@type" => decode_type_alias_attr(value, span, sources),
        other => Err(QuotedSourceError::new(format!(
            "unsupported quoted scope attribute `{other}`"
        ))),
    }
}

fn decode_type_alias_attr(
    payload: &QuotedSourceCursor,
    span: Span,
    sources: &SourceMap,
) -> Result<Attribute, QuotedSourceError> {
    let mut tokens = token_payload::decode_tokens(payload, sources)?
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

fn parse_alias_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<AliasForm, QuotedSourceError> {
    let node = expect_surface_node(&source, sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("alias expects a target path"));
    }
    let path = parse_alias_segments(&args[0], sources)?;
    let as_name = if let Some(kwargs) = args.get(1) {
        parse_alias_keyword_args(kwargs, sources)?
    } else {
        None
    }
    .unwrap_or_else(|| path.last().cloned().unwrap_or_default());
    Ok(AliasForm { path, as_name, span })
}

fn parse_import_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<ImportForm, QuotedSourceError> {
    let node = expect_surface_node(&source, sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("import/require expects a target path"));
    }
    let path = parse_alias_segments(&args[0], sources)?;
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

fn parse_function_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<FunctionForm, QuotedSourceError> {
    let span = surface_span(&source, sources)?;
    let head = surface_head_name(&source, sources)?
        .ok_or_else(|| QuotedSourceError::new("expected atom-headed function form"))?;
    if head == "extern" {
        let node = first_non_attr_node(&source, sources)?;
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

    let FunctionGroupKey { name, arity } = parse_function_group_key(&source, sources)?;
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

fn parse_module_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<ModuleForm, QuotedSourceError> {
    let node = expect_surface_node(&source, sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("defmodule expects a module alias"));
    }
    let name = ModuleName::from_segments(parse_alias_segments(&args[0], sources)?);
    Ok(ModuleForm { source, name, span })
}

fn parse_protocol_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<ProtocolForm, QuotedSourceError> {
    let node = expect_surface_node(&source, sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("defprotocol expects a protocol alias"));
    }
    let name = ModuleName::from_segments(parse_alias_segments(&args[0], sources)?);
    Ok(ProtocolForm { source, name, span })
}

fn parse_protocol_impl_form(
    source: QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<ProtocolImplForm, QuotedSourceError> {
    let node = expect_surface_node(&source, sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    if args.len() != 2 {
        return Err(QuotedSourceError::new(
            "defimpl expects a protocol alias and keyword args",
        ));
    }
    let protocol = ModuleName::from_segments(parse_alias_segments(&args[0], sources)?);
    let kwargs = args[1].list_items()?;
    let mut target = None;
    for entry in kwargs {
        let tuple = entry.tuple_items()?;
        if tuple.len() != 2
            || tuple[0].root().tag() != fz_runtime::any_value::ValueKind::ATOM
            || tuple[0].atom_name()? != "for"
        {
            continue;
        }
        target = Some(ModuleName::from_segments(parse_alias_segments(&tuple[1], sources)?));
        break;
    }
    let target = target.ok_or_else(|| QuotedSourceError::new("defimpl is missing `for:` target"))?;
    Ok(ProtocolImplForm {
        source,
        protocol,
        target,
        span,
    })
}

fn parse_struct_form(source: QuotedSourceRoot, sources: &SourceMap) -> Result<StructForm, QuotedSourceError> {
    let node = expect_surface_node(&source, sources)?;
    let span = node.span.unwrap_or(Span::DUMMY);
    let args = node.tail.list_items()?;
    let Some(fields) = args.first() else {
        return Err(QuotedSourceError::new("defstruct expects a field list"));
    };
    let fields = fields.list_atom_names()?;
    Ok(StructForm { source, fields, span })
}

fn parse_function_group_key(
    root: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<FunctionGroupKey, QuotedSourceError> {
    let node = first_non_attr_node(root, sources)?;
    let args = node.tail.list_items()?;
    let Some(head) = args.first() else {
        return Err(QuotedSourceError::new(
            "quoted function clause is missing its head expression",
        ));
    };
    parse_function_head_key(head, sources)
}

pub(crate) fn reserved_source_definition(
    source: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<Option<ReservedSourceDefinition>, QuotedSourceError> {
    let Some(head) = surface_head_name(source, sources)? else {
        return Ok(None);
    };
    Ok(match head.as_str() {
        "fn" | "fnp" | "defmacro" => {
            let FunctionGroupKey { name, arity } = parse_function_group_key(source, sources)?;
            Some(ReservedSourceDefinition::Function {
                name,
                arity,
                is_macro: head == "defmacro",
            })
        }
        "defmodule" => {
            let node = expect_surface_node(source, sources)?;
            let args = node.tail.list_items()?;
            let Some(name) = args.first() else {
                return Err(QuotedSourceError::new("defmodule expects a module alias"));
            };
            let name = ModuleName::from_segments(parse_alias_segments(name, sources)?);
            Some(ReservedSourceDefinition::Module { name })
        }
        "defprotocol" => {
            let node = expect_surface_node(source, sources)?;
            let args = node.tail.list_items()?;
            let Some(name) = args.first() else {
                return Err(QuotedSourceError::new("defprotocol expects a protocol alias"));
            };
            Some(ReservedSourceDefinition::Protocol {
                name: ModuleName::from_segments(parse_alias_segments(name, sources)?),
            })
        }
        "defimpl" => {
            // Recognition only: scope-time registration resolves the protocol
            // and target into the implementation's typed owner pair. Validate
            // just the arity here.
            let node = expect_surface_node(source, sources)?;
            let args = node.tail.list_items()?;
            if args.len() != 2 {
                return Err(QuotedSourceError::new(
                    "defimpl expects a protocol alias and keyword args",
                ));
            }
            Some(ReservedSourceDefinition::ProtocolImpl)
        }
        _ => None,
    })
}

fn parse_function_head_key(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<FunctionGroupKey, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Err(QuotedSourceError::new("expected quoted function head AST node"));
    };
    if node.head.atom_name()? == "when" {
        let args = node.tail.list_items()?;
        let Some(inner) = args.first() else {
            return Err(QuotedSourceError::new(
                "quoted `when` head is missing the guarded function head",
            ));
        };
        return parse_function_head_key(inner, sources);
    }
    Ok(FunctionGroupKey {
        name: node.head.atom_name()?,
        arity: node.tail.list_items()?.len(),
    })
}

fn parse_alias_segments(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Vec<String>, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
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

fn parse_alias_keyword_args(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<String>, QuotedSourceError> {
    for entry in cursor.list_items()? {
        let tuple = entry.tuple_items()?;
        if tuple.len() != 2 {
            return Err(QuotedSourceError::new("expected alias keyword tuple"));
        }
        if tuple[0].atom_name()? == "as" {
            let path = parse_alias_segments(&tuple[1], sources)?;
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

fn extract_do_body_list_root(
    root: &QuotedSourceRoot,
    sources: &SourceMap,
) -> Result<QuotedSourceRoot, QuotedSourceError> {
    let Some(node) = root.cursor().ast_node(sources)? else {
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

fn surface_head_name(root: &QuotedSourceRoot, sources: &SourceMap) -> Result<Option<String>, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node(sources)? {
        return atom_head_name(&node);
    }
    atom_head_name(&first_non_attr_node(root, sources)?)
}

fn first_non_attr_node(root: &QuotedSourceRoot, sources: &SourceMap) -> Result<QuotedAstNode, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node(sources)? {
        return Ok(node);
    }
    for item in root.cursor().list_items()? {
        let Some(node) = item.ast_node(sources)? else {
            return Err(QuotedSourceError::new("expected quoted grouped surface item AST node"));
        };
        if !atom_head_name(&node)?.is_some_and(|head| head.starts_with('@')) {
            return Ok(node);
        }
    }
    Err(QuotedSourceError::new(
        "expected grouped quoted surface to contain a non-attribute form",
    ))
}

fn expect_surface_node(root: &QuotedSourceRoot, sources: &SourceMap) -> Result<QuotedAstNode, QuotedSourceError> {
    root.cursor()
        .ast_node(sources)?
        .ok_or_else(|| QuotedSourceError::new("expected quoted item AST node"))
}

fn expect_ast_cursor_node(
    cursor: &QuotedSourceCursor,
    label: &str,
    sources: &SourceMap,
) -> Result<QuotedAstNode, QuotedSourceError> {
    cursor
        .ast_node(sources)?
        .ok_or_else(|| QuotedSourceError::new(format!("expected {label} AST node")))
}

fn surface_span(root: &QuotedSourceRoot, sources: &SourceMap) -> Result<Span, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node(sources)? {
        return Ok(node.span.unwrap_or(Span::DUMMY));
    }
    let mut merged: Option<Span> = None;
    for item in root.cursor().list_items()? {
        let Some(node) = item.ast_node(sources)? else {
            return Err(QuotedSourceError::new("expected grouped quoted surface item AST node"));
        };
        let span = node.span.unwrap_or(Span::DUMMY);
        merged = Some(match merged {
            Some(current) => current.merge(span),
            None => span,
        });
    }
    Ok(merged.unwrap_or(Span::DUMMY))
}

fn atom_head_name(node: &QuotedAstNode) -> Result<Option<String>, QuotedSourceError> {
    if node.head.root().tag() != fz_runtime::any_value::ValueKind::ATOM {
        return Ok(None);
    }
    node.head.atom_name().map(Some)
}
