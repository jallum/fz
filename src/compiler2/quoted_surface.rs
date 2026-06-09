use std::collections::HashMap;
use std::rc::Rc;

use fz_runtime::any_value::AnyValueRef;

use crate::ast::{Attribute, FnDef, Item, ModuleDef, ProtocolDef, ProtocolImplDef, StructDef};
use crate::compiler::source::Span;

use super::source::{QuotedAstNode, QuotedSourceCarrier, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};

#[derive(Debug, Clone)]
pub struct ScopeSurface {
    pub legacy_attrs: Vec<Attribute>,
    pub forms: Vec<ScopeForm>,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum ScopeForm {
    Alias(AliasForm),
    Import(ImportForm),
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
pub struct FunctionForm {
    pub source: QuotedSourceCarrier,
    pub legacy_fn: FnDef,
}

#[derive(Debug, Clone)]
pub struct ModuleForm {
    pub source: QuotedSourceCarrier,
    pub legacy_module: ModuleDef,
}

#[derive(Debug, Clone)]
pub struct ProtocolForm {
    pub source: QuotedSourceCarrier,
    pub legacy_protocol: ProtocolDef,
}

#[derive(Debug, Clone)]
pub struct ProtocolImplForm {
    pub source: QuotedSourceCarrier,
    pub legacy_protocol_impl: ProtocolImplDef,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct StructForm {
    pub source: QuotedSourceCarrier,
    pub legacy_struct: StructDef,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct MacroCallForm {
    pub source: QuotedSourceCarrier,
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
    legacy_items: &[Rc<Item>],
    legacy_attrs: &[Attribute],
) -> Result<ScopeSurface, QuotedSourceError> {
    let quoted_forms = prepare_surface_forms(source)?;
    if quoted_forms.len() != legacy_items.len() {
        return Err(QuotedSourceError::new(format!(
            "quoted surface produced {} grouped forms but legacy compatibility carries {} items",
            quoted_forms.len(),
            legacy_items.len()
        )));
    }
    let mut forms = Vec::new();
    for (quoted_form, legacy_item) in quoted_forms.into_iter().zip(legacy_items.iter()) {
        forms.push(build_form(quoted_form, legacy_item)?);
    }
    Ok(ScopeSurface {
        legacy_attrs: legacy_attrs.to_vec(),
        forms,
    })
}

pub fn read_module_body_surface(form: &ModuleForm) -> Result<ScopeSurface, QuotedSourceError> {
    read_module_body_surface_from_parts(&form.source, &form.legacy_module.items, &form.legacy_module.attrs)
}

pub fn read_protocol_impl_body_surface(form: &ProtocolImplForm) -> Result<ScopeSurface, QuotedSourceError> {
    read_do_body_surface_from_parts(
        &form.source,
        &form.legacy_protocol_impl.items,
        &form.legacy_protocol_impl.attrs,
    )
}

pub fn read_module_body_surface_from_parts(
    source: &QuotedSourceCarrier,
    legacy_items: &[Rc<Item>],
    legacy_attrs: &[Attribute],
) -> Result<ScopeSurface, QuotedSourceError> {
    read_do_body_surface_from_parts(source, legacy_items, legacy_attrs)
}

fn read_do_body_surface_from_parts(
    source: &QuotedSourceCarrier,
    legacy_items: &[Rc<Item>],
    legacy_attrs: &[Attribute],
) -> Result<ScopeSurface, QuotedSourceError> {
    let body = extract_do_body_list_root(&source.root)?;
    read_scope_surface(&body, legacy_items, legacy_attrs)
}

fn build_form(source: QuotedSourceCarrier, legacy_item: &Rc<Item>) -> Result<ScopeForm, QuotedSourceError> {
    let head = surface_head_name(&source.root)?;
    match (head.as_str(), &**legacy_item) {
        ("alias", Item::Alias { span, .. }) => {
            let node = expect_surface_node(&source.root)?;
            Ok(ScopeForm::Alias(parse_alias(&node, *span)?))
        }
        ("import", Item::Import { span, .. }) => {
            let node = expect_surface_node(&source.root)?;
            Ok(ScopeForm::Import(parse_import(&node, *span)?))
        }
        ("fn" | "fnp" | "defmacro" | "extern", Item::Fn(def)) => Ok(ScopeForm::Function(FunctionForm {
            source,
            legacy_fn: def.clone(),
        })),
        ("defmodule", Item::Module(module)) => Ok(ScopeForm::Module(ModuleForm {
            source,
            legacy_module: module.clone(),
        })),
        ("defprotocol", Item::Protocol(protocol)) => Ok(ScopeForm::Protocol(ProtocolForm {
            source,
            legacy_protocol: protocol.clone(),
        })),
        ("defimpl", Item::ProtocolImpl(protocol_impl)) => Ok(ScopeForm::ProtocolImpl(ProtocolImplForm {
            source,
            legacy_protocol_impl: protocol_impl.clone(),
        })),
        ("defstruct", Item::Struct(struct_def)) => Ok(ScopeForm::Struct(StructForm {
            source,
            legacy_struct: struct_def.clone(),
        })),
        (_, Item::MacroCall { span, .. }) => Ok(ScopeForm::MacroCall(MacroCallForm { source, span: *span })),
        (quoted, legacy) => Err(QuotedSourceError::new(format!(
            "quoted surface head `{quoted}` does not align with legacy compatibility item {legacy:?}"
        ))),
    }
}

fn prepare_surface_forms(source: &QuotedSourceRoot) -> Result<Vec<QuotedSourceCarrier>, QuotedSourceError> {
    let quoted_items = source.cursor().list_items()?;
    let mut forms = Vec::new();
    let mut group_order = Vec::new();
    let mut groups: HashMap<FunctionGroupKey, PendingFunctionGroup> = HashMap::new();
    let mut pending_attrs = Vec::new();

    for quoted_item in quoted_items {
        let Some(node) = quoted_item.ast_node()? else {
            return Err(QuotedSourceError::new("expected quoted item AST node"));
        };
        let head_name = node.head.atom_name()?;
        if head_name.starts_with('@') {
            if matches!(head_name.as_str(), "@doc" | "@spec") {
                pending_attrs.push(quoted_item.root());
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
                entry.item_roots.append(&mut pending_attrs);
                entry.item_roots.push(quoted_item.root());
            }
            "extern" => {
                flush_function_groups(source, &mut forms, &mut group_order, &mut groups)?;
                let mut item_roots = std::mem::take(&mut pending_attrs);
                item_roots.push(quoted_item.root());
                forms.push(grouped_surface_carrier(source, &item_roots)?);
            }
            _ => {
                flush_function_groups(source, &mut forms, &mut group_order, &mut groups)?;
                pending_attrs.clear();
                forms.push(QuotedSourceCarrier::new(source.subroot(quoted_item.root()))?);
            }
        }
    }

    flush_function_groups(source, &mut forms, &mut group_order, &mut groups)?;
    Ok(forms)
}

fn flush_function_groups(
    source: &QuotedSourceRoot,
    forms: &mut Vec<QuotedSourceCarrier>,
    order: &mut Vec<FunctionGroupKey>,
    groups: &mut HashMap<FunctionGroupKey, PendingFunctionGroup>,
) -> Result<(), QuotedSourceError> {
    for key in order.drain(..) {
        if let Some(group) = groups.remove(&key) {
            forms.push(grouped_surface_carrier(source, &group.item_roots)?);
        }
    }
    Ok(())
}

fn grouped_surface_carrier(
    source: &QuotedSourceRoot,
    item_roots: &[AnyValueRef],
) -> Result<QuotedSourceCarrier, QuotedSourceError> {
    let root = source.interned_list_subroot(item_roots)?;
    QuotedSourceCarrier::new(root)
}

fn surface_head_name(root: &QuotedSourceRoot) -> Result<String, QuotedSourceError> {
    if let Some(node) = root.cursor().ast_node()? {
        return node.head.atom_name();
    }
    for item in root.cursor().list_items()? {
        let Some(node) = item.ast_node()? else {
            return Err(QuotedSourceError::new("expected quoted grouped surface item AST node"));
        };
        let head = node.head.atom_name()?;
        if !head.starts_with('@') {
            return Ok(head);
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

fn parse_function_group_key(source: &QuotedSourceRoot) -> Result<FunctionGroupKey, QuotedSourceError> {
    let Some(node) = source.cursor().ast_node()? else {
        return Err(QuotedSourceError::new("expected grouped function clause AST node"));
    };
    let args = node.tail.list_items()?;
    let Some(head) = args.first() else {
        return Err(QuotedSourceError::new(
            "quoted function clause is missing its head expression",
        ));
    };
    let (name, arity) = parse_function_head_key(head)?;
    Ok(FunctionGroupKey { name, arity })
}

fn parse_function_head_key(cursor: &QuotedSourceCursor) -> Result<(String, usize), QuotedSourceError> {
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
    Ok((node.head.atom_name()?, node.tail.list_items()?.len()))
}

fn parse_alias(node: &QuotedAstNode, span: Span) -> Result<AliasForm, QuotedSourceError> {
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("alias expects a target path"));
    }
    let path = parse_alias_segments(&args[0])?;
    let as_name = if let Some(kwargs) = args.get(1) {
        parse_import_keyword_args(kwargs)?
            .into_iter()
            .find_map(|(kind, values)| {
                (kind == "as")
                    .then(|| values.into_iter().next())
                    .flatten()
                    .map(|(name, _)| name)
            })
    } else {
        None
    }
    .unwrap_or_else(|| path.last().cloned().unwrap_or_default());
    Ok(AliasForm { path, as_name, span })
}

fn parse_import(node: &QuotedAstNode, span: Span) -> Result<ImportForm, QuotedSourceError> {
    let args = node.tail.list_items()?;
    if args.is_empty() {
        return Err(QuotedSourceError::new("import expects a target path"));
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
