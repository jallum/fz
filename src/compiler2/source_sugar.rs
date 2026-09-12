//! Source-only rewrites over compiler2 quoted AST.
//!
//! These rules remove syntax sugar during staged function expansion, after raw
//! `FunctionSource` publication and before `DefineFunction` decodes the body.

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use super::source::{QuotedAstNode, QuotedSourceBuilder, QuotedSourceCursor, QuotedSourceError, QuotedSourceRoot};
use crate::source::SourceMap;

pub(crate) fn rewrite_source_sugar(
    owner: &QuotedSourceRoot,
    source: AnyValueRef,
    node: &QuotedAstNode,
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if let Some(rewritten) = owner.source_sugar_rewrite(source) {
        return Ok(Some(rewritten));
    }
    if !is_list_like(&node.tail) {
        return Ok(None);
    }
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(None);
    }
    let head = node.head.atom_name()?;
    let args = node.tail.list_items()?;
    let rewritten = match head.as_str() {
        "|>" if args.len() == 2 => rewrite_pipe(owner, node, &args, sources),
        "&" if args.len() == 1 => rewrite_capture(owner, node, &args[0], sources),
        "-" if args.len() == 1 => rewrite_unary_minus(owner, node, &args[0]),
        "fn" => rewrite_lambda(owner, node, &args, sources),
        "++" | "--" | "<>" | ".." | "//" | "in" | "not in" if args.len() == 2 => {
            rewrite_operator(owner, node, head.as_str(), &args, sources)
        }
        _ => Ok(None),
    }?;
    if let Some(rewritten) = rewritten {
        owner.memoize_source_sugar_rewrite(source, rewritten);
    }
    Ok(rewritten)
}

fn rewrite_pipe(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    args: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let lhs = args[0].root();
    let rhs = &args[1];
    let Some(rhs_node) = rhs.ast_node(sources)? else {
        return Ok(None);
    };
    if !is_list_like(&rhs_node.tail) {
        return Ok(None);
    }

    let rhs_args = roots(&rhs_node.tail.list_items()?);
    let is_case = rhs_node.head.root().tag() == ValueKind::ATOM && rhs_node.head.atom_name()? == "case";
    if is_case {
        if rhs_args.len() != 1 {
            return Ok(None);
        }
        return Ok(Some(ast_call(
            &owner.builder(),
            rhs_node.head.root(),
            node.meta.root(),
            &[lhs, rhs_args[0]],
        )?));
    }

    let mut piped_args = Vec::with_capacity(rhs_args.len() + 1);
    piped_args.push(lhs);
    piped_args.extend(rhs_args);
    Ok(Some(ast_call(
        &owner.builder(),
        rhs_node.head.root(),
        node.meta.root(),
        &piped_args,
    )?))
}

/// `-x` becomes `Kernel.negate(x)`, a typed clause family like every BINARY
/// operator.
///
/// Lowered instead to one machine instruction, unary minus read a single lane,
/// so `-x` aborted natively for an operand that might be an integer or a float
/// while `0 - x` on the same value worked (fz-5xp.38). Routing it through
/// `Kernel` makes the two agree by construction, and makes an unsupported
/// operand a missing clause rather than a wrong instruction.
///
/// A numeric LITERAL is left alone for the decoder to fold into a negative
/// literal: `-3` should not become a call.
fn rewrite_unary_minus(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    operand: &QuotedSourceCursor,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if matches!(operand.root().tag(), ValueKind::INT | ValueKind::FLOAT) {
        return Ok(None);
    }
    let builder = owner.builder();
    Ok(Some(remote_call(
        &builder,
        "Kernel.negate",
        node.meta.root(),
        &[operand.root()],
    )?))
}

fn rewrite_operator(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    op: &str,
    args: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    let builder = owner.builder();
    let left = args[0].root();
    let right = args[1].root();
    let meta = node.meta.root();
    let rewritten = match op {
        "++" => remote_call(&builder, "List.concat", meta, &[left, right])?,
        "--" => remote_call(&builder, "List.subtract", meta, &[left, right])?,
        "<>" => remote_call(&builder, "Kernel.fz_binary_concat", meta, &[left, right])?,
        ".." => remote_call(&builder, "Range.new", meta, &[left, right, builder.int(1)])?,
        "//" => {
            let Some((first, last)) = range_parts(&args[0], sources)? else {
                return Ok(None);
            };
            remote_call(&builder, "Range.new", meta, &[first, last, right])?
        }
        "in" => remote_call(&builder, "Enum.member?", meta, &[right, left])?,
        "not in" => {
            let member = remote_call(&builder, "Enum.member?", meta, &[right, left])?;
            named_call(&builder, "not", meta, &[member])?
        }
        _ => return Ok(None),
    };
    Ok(Some(rewritten))
}

fn range_parts(
    cursor: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<(AnyValueRef, AnyValueRef)>, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(None);
    };
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(None);
    }
    let head = node.head.atom_name()?;
    if head != ".." && head != "Range.new" {
        return Ok(None);
    }
    let args = node.tail.list_items()?;
    if args.len() < 2 {
        return Ok(None);
    }
    Ok(Some((args[0].root(), args[1].root())))
}

fn rewrite_capture(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    body: &QuotedSourceCursor,
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if is_function_ref_payload(body, sources)? {
        return Ok(None);
    }

    let builder = owner.builder();
    let meta = node.meta.root();
    if body.root().tag() == ValueKind::INT {
        let arity = body.int_value()?;
        if arity < 1 {
            return Ok(None);
        }
        let body = variable(&builder, capture_arg_name(arity as usize), meta)?;
        return Ok(Some(capture_lambda(&builder, arity as usize, body, meta)?));
    }

    let arity = max_capture_arg(body, sources)?.unwrap_or(0);
    let body = replace_capture_args(&builder, body, meta, sources)?.0;
    Ok(Some(capture_lambda(&builder, arity, body, meta)?))
}

fn rewrite_lambda(
    owner: &QuotedSourceRoot,
    node: &QuotedAstNode,
    clauses: &[QuotedSourceCursor],
    sources: &SourceMap,
) -> Result<Option<AnyValueRef>, QuotedSourceError> {
    if !lambda_source_sugar_shape(clauses, sources)? {
        return Ok(None);
    }
    if lambda_is_direct_clause(clauses, sources)? {
        return Ok(None);
    }

    let mut decoded = Vec::with_capacity(clauses.len());
    for clause in clauses {
        decoded.push(lambda_clause(clause, sources)?);
    }
    let Some(arity) = decoded.first().map(|clause| clause.params.len()) else {
        return Ok(None);
    };
    if decoded.iter().any(|clause| clause.params.len() != arity) {
        return Ok(None);
    }

    let builder = owner.builder();
    let meta = node.meta.root();
    let lambda_params = (0..arity)
        .map(|index| variable(&builder, lambda_arg_name(index), meta))
        .collect::<Result<Vec<_>, _>>()?;
    let subject = if arity == 1 {
        lambda_params[0]
    } else {
        builder.tuple(&lambda_params)?
    };

    let mut arms = Vec::with_capacity(decoded.len());
    for clause in decoded {
        let pattern = if arity == 1 {
            clause.params[0]
        } else {
            builder.tuple(&clause.params)?
        };
        let pattern = if let Some(guard) = clause.guard {
            named_call(&builder, "when", clause.meta, &[pattern, guard])?
        } else {
            pattern
        };
        let patterns = builder.list(&[pattern])?;
        arms.push(named_call(&builder, "->", clause.meta, &[patterns, clause.body])?);
    }

    let case_body = builder.list(&arms)?;
    let case_kw = builder.list(&[builder.keyword("do", case_body)?])?;
    let case = named_call(&builder, "case", meta, &[subject, case_kw])?;
    let params = builder.list(&lambda_params)?;
    let clause = named_call(&builder, "->", meta, &[params, case])?;
    Ok(Some(named_call(&builder, "fn", meta, &[clause])?))
}

fn lambda_source_sugar_shape(clauses: &[QuotedSourceCursor], sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    for clause in clauses {
        let Some(node) = clause.ast_node(sources)? else {
            return Ok(false);
        };
        if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "->" {
            return Ok(false);
        }
    }
    Ok(!clauses.is_empty())
}

struct LambdaClauseSource {
    params: Vec<AnyValueRef>,
    guard: Option<AnyValueRef>,
    body: AnyValueRef,
    meta: AnyValueRef,
}

fn lambda_is_direct_clause(clauses: &[QuotedSourceCursor], sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    let [clause] = clauses else {
        return Ok(false);
    };
    Ok(lambda_clause(clause, sources)?.guard.is_none())
}

fn lambda_clause(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<LambdaClauseSource, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Err(QuotedSourceError::new("lambda clause expected quoted AST"));
    };
    if node.head.atom_name()? != "->" {
        return Err(QuotedSourceError::new("lambda clause expected `->`"));
    }
    let parts = node.tail.list_items()?;
    let [params, body] = parts.as_slice() else {
        return Err(QuotedSourceError::new("lambda clause expected params and body"));
    };
    let params = params.list_items()?;
    if params.len() == 1
        && let Some(when) = params[0].ast_node(sources)?
        && when.head.atom_name()? == "when"
    {
        let args = when.tail.list_items()?;
        let Some((guard, params)) = args.split_last() else {
            return Err(QuotedSourceError::new("guarded lambda clause is empty"));
        };
        return Ok(LambdaClauseSource {
            params: roots(params),
            guard: Some(guard.root()),
            body: body.root(),
            meta: node.meta.root(),
        });
    }
    Ok(LambdaClauseSource {
        params: roots(&params),
        guard: None,
        body: body.root(),
        meta: node.meta.root(),
    })
}

fn is_function_ref_payload(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(false);
    };
    if node.head.root().tag() != ValueKind::ATOM {
        return Ok(false);
    }
    Ok(node.head.atom_name()? == "/" && is_list_like(&node.tail))
}

fn max_capture_arg(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<usize>, QuotedSourceError> {
    if let Some(index) = capture_arg_index(cursor, sources)? {
        return Ok(Some(index));
    }
    let mut max = None;
    for child in child_cursors(cursor)? {
        if let Some(index) = max_capture_arg(&child, sources)? {
            max = Some(max.map_or(index, |current: usize| current.max(index)));
        }
    }
    Ok(max)
}

fn replace_capture_args(
    builder: &QuotedSourceBuilder,
    cursor: &QuotedSourceCursor,
    meta: AnyValueRef,
    sources: &SourceMap,
) -> Result<(AnyValueRef, bool), QuotedSourceError> {
    if let Some(index) = capture_arg_index(cursor, sources)? {
        return Ok((variable(builder, capture_arg_name(index), meta)?, true));
    }

    match cursor.root().tag() {
        ValueKind::LIST => {
            let items = cursor.list_items()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                let (root, item_changed) = replace_capture_args(builder, &item, meta, sources)?;
                changed |= item_changed;
                out.push(root);
            }
            if changed {
                Ok((builder.list(&out)?, true))
            } else {
                Ok((cursor.root(), false))
            }
        }
        ValueKind::STRUCT => {
            let items = cursor.tuple_items()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                let (root, item_changed) = replace_capture_args(builder, &item, meta, sources)?;
                changed |= item_changed;
                out.push(root);
            }
            if changed {
                Ok((builder.tuple(&out)?, true))
            } else {
                Ok((cursor.root(), false))
            }
        }
        ValueKind::MAP => {
            let entries = cursor.map_entries()?;
            let mut changed = false;
            let mut out = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                let (key, key_changed) = replace_capture_args(builder, &key, meta, sources)?;
                let (value, value_changed) = replace_capture_args(builder, &value, meta, sources)?;
                changed |= key_changed || value_changed;
                out.push((key, value));
            }
            if changed {
                Ok((builder.map(&out)?, true))
            } else {
                Ok((cursor.root(), false))
            }
        }
        _ => Ok((cursor.root(), false)),
    }
}

fn capture_arg_index(cursor: &QuotedSourceCursor, sources: &SourceMap) -> Result<Option<usize>, QuotedSourceError> {
    let Some(node) = cursor.ast_node(sources)? else {
        return Ok(None);
    };
    if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "&" || !is_list_like(&node.tail) {
        return Ok(None);
    }
    let args = node.tail.list_items()?;
    let [arg] = args.as_slice() else {
        return Ok(None);
    };
    if arg.root().tag() != ValueKind::INT {
        return Ok(None);
    }
    let index = arg.int_value()?;
    if index < 1 {
        return Ok(None);
    }
    Ok(Some(index as usize))
}

fn child_cursors(cursor: &QuotedSourceCursor) -> Result<Vec<QuotedSourceCursor>, QuotedSourceError> {
    match cursor.root().tag() {
        ValueKind::LIST => cursor.list_items(),
        ValueKind::STRUCT => cursor.tuple_items(),
        ValueKind::MAP => Ok(cursor
            .map_entries()?
            .into_iter()
            .flat_map(|(key, value)| [key, value])
            .collect()),
        _ => Ok(Vec::new()),
    }
}

fn capture_lambda(
    builder: &QuotedSourceBuilder,
    arity: usize,
    body: AnyValueRef,
    meta: AnyValueRef,
) -> Result<AnyValueRef, QuotedSourceError> {
    let params = (1..=arity)
        .map(|index| variable(builder, capture_arg_name(index), meta))
        .collect::<Result<Vec<_>, _>>()?;
    let params = builder.list(&params)?;
    let clause = named_call(builder, "->", meta, &[params, body])?;
    named_call(builder, "fn", meta, &[clause])
}

fn variable(builder: &QuotedSourceBuilder, name: String, meta: AnyValueRef) -> Result<AnyValueRef, QuotedSourceError> {
    builder.tuple(&[builder.atom(&name), meta, builder.nil()])
}

fn named_call(
    builder: &QuotedSourceBuilder,
    name: &str,
    meta: AnyValueRef,
    args: &[AnyValueRef],
) -> Result<AnyValueRef, QuotedSourceError> {
    ast_call(builder, builder.atom(name), meta, args)
}

fn remote_call(
    builder: &QuotedSourceBuilder,
    name: &str,
    meta: AnyValueRef,
    args: &[AnyValueRef],
) -> Result<AnyValueRef, QuotedSourceError> {
    let Some((module, function)) = name.rsplit_once('.') else {
        return named_call(builder, name, meta, args);
    };
    let segments = module
        .split('.')
        .map(|segment| builder.atom(segment))
        .collect::<Vec<_>>();
    let alias = ast_call(builder, builder.atom("__aliases__"), meta, &segments)?;
    let callee = ast_call(builder, builder.atom("."), meta, &[alias, builder.atom(function)])?;
    ast_call(builder, callee, meta, args)
}

fn ast_call(
    builder: &QuotedSourceBuilder,
    head: AnyValueRef,
    meta: AnyValueRef,
    args: &[AnyValueRef],
) -> Result<AnyValueRef, QuotedSourceError> {
    builder.tuple(&[head, meta, builder.list(args)?])
}

fn roots(cursors: &[QuotedSourceCursor]) -> Vec<AnyValueRef> {
    cursors.iter().map(QuotedSourceCursor::root).collect()
}

fn is_list_like(cursor: &QuotedSourceCursor) -> bool {
    cursor.root().is_empty_list() || cursor.root().tag() == ValueKind::LIST
}

fn capture_arg_name(index: usize) -> String {
    format!("__fz_capture_arg_{index}")
}

fn lambda_arg_name(index: usize) -> String {
    format!("__fz_lambda_arg_{index}")
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use fz_runtime::any_value::{AnyValueRef, ValueKind};

    use super::{capture_arg_index, lambda_source_sugar_shape, range_parts};
    use crate::compiler2::{QuotedSourceHeap, QuotedSourceMetadata};
    use crate::source::SourceMap;

    #[test]
    fn sugar_shape_probes_propagate_invalid_atom_payloads() {
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        let unknown_atom_id = u64::MAX;
        let unknown_atom = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &unknown_atom_id)
            .expect("stack scalar is a valid temporary atom carrier");
        let node = builder
            .ast_node(unknown_atom, &QuotedSourceMetadata::default(), builder.empty_list())
            .expect("builder copies the scalar into its owned heap");
        let root = builder.root(node).expect("quoted source root");
        let cursor = root.cursor();
        let sources = SourceMap::new();

        for error in [
            range_parts(&cursor, &sources).expect_err("range probe must propagate invalid atom"),
            lambda_source_sugar_shape(std::slice::from_ref(&cursor), &sources)
                .expect_err("lambda probe must propagate invalid atom"),
            capture_arg_index(&cursor, &sources).expect_err("capture probe must propagate invalid atom"),
        ] {
            assert!(error.to_string().contains("unknown atom id"), "{error}");
        }
    }
}
