use std::collections::HashMap;
use std::rc::Rc;

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
    source: QuotedSourceCarrier,
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

pub fn read_module_body_surface_from_parts(
    source: &QuotedSourceCarrier,
    legacy_items: &[Rc<Item>],
    legacy_attrs: &[Attribute],
) -> Result<ScopeSurface, QuotedSourceError> {
    let body = extract_do_body_list_root(&source.root)?;
    read_scope_surface(&body, legacy_items, legacy_attrs)
}

fn build_form(source: QuotedSourceCarrier, legacy_item: &Rc<Item>) -> Result<ScopeForm, QuotedSourceError> {
    let Some(node) = source.root.cursor().ast_node()? else {
        return Err(QuotedSourceError::new("expected quoted item AST node"));
    };
    let head = node.head.atom_name()?;
    match (head.as_str(), &**legacy_item) {
        ("alias", Item::Alias { span, .. }) => Ok(ScopeForm::Alias(parse_alias(&node, *span)?)),
        ("import", Item::Import { span, .. }) => Ok(ScopeForm::Import(parse_import(&node, *span)?)),
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

    for quoted_item in quoted_items {
        let carrier = QuotedSourceCarrier::new(source.subroot(quoted_item.root()))?;
        let Some(node) = carrier.root.cursor().ast_node()? else {
            return Err(QuotedSourceError::new("expected quoted item AST node"));
        };
        let head_name = node.head.atom_name()?;
        if head_name.starts_with('@') {
            continue;
        }
        match head_name.as_str() {
            "fn" | "fnp" | "defmacro" => {
                let key = parse_function_group_key(&carrier)?;
                if let Some(existing) = groups.get(&key) {
                    if existing.kind != head_name {
                        return Err(QuotedSourceError::new(format!(
                            "quoted function group `{}/{} ` mixes `{}` and `{}` heads",
                            key.name, key.arity, existing.kind, head_name
                        )));
                    }
                } else {
                    group_order.push(key.clone());
                    groups.insert(
                        key,
                        PendingFunctionGroup {
                            source: carrier,
                            kind: head_name,
                        },
                    );
                }
            }
            "extern" => {
                flush_function_groups(&mut forms, &mut group_order, &mut groups);
                forms.push(carrier);
            }
            _ => {
                flush_function_groups(&mut forms, &mut group_order, &mut groups);
                forms.push(carrier);
            }
        }
    }

    flush_function_groups(&mut forms, &mut group_order, &mut groups);
    Ok(forms)
}

fn flush_function_groups(
    forms: &mut Vec<QuotedSourceCarrier>,
    order: &mut Vec<FunctionGroupKey>,
    groups: &mut HashMap<FunctionGroupKey, PendingFunctionGroup>,
) {
    for key in order.drain(..) {
        if let Some(group) = groups.remove(&key) {
            forms.push(group.source);
        }
    }
}

fn parse_function_group_key(source: &QuotedSourceCarrier) -> Result<FunctionGroupKey, QuotedSourceError> {
    let Some(node) = source.root.cursor().ast_node()? else {
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
