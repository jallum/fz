//! `<>` and `++` in patterns: the bitstring and list patterns they stand for.
//!
//! `"--" <> rest` is `<<"--", rest::binary>>` and `[1, 2] ++ rest` is
//! `[1, 2 | rest]`. The decoder reads the operator once, here, and returns the
//! pattern the rest of the compiler already knows.
//!
//! Two spellings reach a pattern. A function head is not expanded, so it keeps
//! the bare operator. Everywhere else the expander has rewritten the operator
//! into a call and stamped it with [`META_FROM_OPERATOR_KEY`]. A call spelled
//! `Kernel.<>(a, b)` by the user carries no stamp and is not a pattern.

use fz_runtime::any_value::ValueKind;

use super::quoted_function::{decode_bitstring_pattern, decode_pattern, sized_for_known_binary};
use super::source::{META_FROM_OPERATOR_KEY, QuotedAstNode, QuotedSourceCursor, QuotedSourceError};
use crate::ast::{BitField, BitFieldSpec, BitType, Pattern, Spanned};
use crate::diag::codes::PARSE_CONCAT_PATTERN_OPERAND;
use crate::source::{SourceMap, Span};

#[derive(Clone, Copy, PartialEq, Eq)]
enum ConcatOp {
    Binary,
    List,
}

impl ConcatOp {
    fn spelling(self) -> &'static str {
        match self {
            ConcatOp::Binary => "<>",
            ConcatOp::List => "++",
        }
    }
}

pub(super) struct ConcatOperands {
    op: ConcatOp,
    left: QuotedSourceCursor,
    right: QuotedSourceCursor,
}

/// The operands of a node that is the concatenation operator, in either of the
/// two spellings it can have.
pub(super) fn concat_operands(
    node: &QuotedAstNode,
    args: &[QuotedSourceCursor],
) -> Result<Option<ConcatOperands>, QuotedSourceError> {
    let spelling = if node.head.root().tag() == ValueKind::ATOM {
        node.head.atom_name()?
    } else {
        match node.meta.map_value(META_FROM_OPERATOR_KEY)? {
            Some(stamp) => stamp.atom_name()?,
            None => return Ok(None),
        }
    };
    let op = match spelling.as_str() {
        "<>" => ConcatOp::Binary,
        "++" => ConcatOp::List,
        _ => return Ok(None),
    };
    let [left, right] = args else {
        return Ok(None);
    };
    Ok(Some(ConcatOperands {
        op,
        left: left.clone(),
        right: right.clone(),
    }))
}

pub(super) fn decode_concat_pattern(
    operands: &ConcatOperands,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    match operands.op {
        ConcatOp::Binary => decode_binary_concat(operands, span, sources),
        ConcatOp::List => decode_list_concat(operands, span, sources),
    }
}

/// A call the user spelled out as a function, where the operator is what a
/// pattern accepts.
pub(super) fn refuse_concat_call(
    node: &QuotedAstNode,
    span: Span,
    sources: &SourceMap,
) -> Result<(), QuotedSourceError> {
    let Some(callee) = node.head.ast_node(sources)? else {
        return Ok(());
    };
    if callee.head.root().tag() != ValueKind::ATOM || callee.head.atom_name()? != "." {
        return Ok(());
    }
    let parts = callee.tail.list_items()?;
    let [module, function] = parts.as_slice() else {
        return Ok(());
    };
    let op = match (function.root().tag() == ValueKind::ATOM)
        .then(|| function.atom_name())
        .transpose()?
        .as_deref()
    {
        Some("<>") => ConcatOp::Binary,
        Some("concat") if module_is_list(module, sources)? => ConcatOp::List,
        _ => return Ok(()),
    };
    let written = callee_text(&callee, sources).unwrap_or_else(|| "the call".to_string());
    Err(refuse(
        Some(span),
        format!(
            "`{written}` called as a function is not a pattern; write the `{}` operator instead",
            op.spelling()
        ),
    ))
}

fn module_is_list(module: &QuotedSourceCursor, sources: &SourceMap) -> Result<bool, QuotedSourceError> {
    let Some(node) = module.ast_node(sources)? else {
        return Ok(false);
    };
    if node.head.root().tag() != ValueKind::ATOM || node.head.atom_name()? != "__aliases__" {
        return Ok(false);
    }
    let segments = node.tail.list_items()?;
    Ok(matches!(segments.as_slice(), [only] if only.atom_name().is_ok_and(|name| name == "List")))
}

fn callee_text(callee: &QuotedAstNode, sources: &SourceMap) -> Option<String> {
    source_text(callee.span?, sources).map(str::to_string)
}

// ----- `<>` ---------------------------------------------------------------

fn decode_binary_concat(
    operands: &ConcatOperands,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let mut fields = Vec::new();
    push_binary_operand(&operands.left, false, span, sources, &mut fields)?;
    push_binary_operand(&operands.right, true, span, sources, &mut fields)?;
    Ok(Spanned::new(Pattern::Bitstring(fields), span))
}

/// One operand of `<>` as the bitstring segments it contributes. Only the last
/// operand may be a name that takes whatever is left; every operand before it
/// must have a length of its own.
fn push_binary_operand(
    operand: &QuotedSourceCursor,
    is_last: bool,
    call_span: Span,
    sources: &SourceMap,
    fields: &mut Vec<BitField<Spanned<Pattern>>>,
) -> Result<(), QuotedSourceError> {
    let Some(node) = operand.ast_node(sources)? else {
        return push_binary_literal(operand, call_span, sources, fields);
    };
    let node_span = node.span.unwrap_or(call_span);
    if !node.tail.is_list_like() {
        if !is_last {
            return Err(refuse(
                node.span,
                format!(
                    "cannot perform prefix match because the left operand of <> has unknown size. The left operand of <> inside a match should either be a literal binary or an existing variable with the pin operator (such as ^some_var). Got: {}",
                    node.head.atom_name()?
                ),
            ));
        }
        let segment = decode_pattern(operand, Some(call_span), sources)?;
        fields.push(binary_segment(segment));
        return Ok(());
    }
    let args = node.tail.list_items()?;
    if let Some(inner) = concat_operands(&node, &args)? {
        if inner.op == ConcatOp::List {
            return Err(expected_binary(operand, node.span, call_span, sources));
        }
        push_binary_operand(&inner.left, false, call_span, sources, fields)?;
        return push_binary_operand(&inner.right, is_last, call_span, sources, fields);
    }
    if node.head.root().tag() != ValueKind::ATOM {
        return Err(only_binaries_numbers_and_variables(operand, node_span, sources));
    }
    match node.head.atom_name()?.as_str() {
        "^" => {
            let pinned = decode_pattern(operand, Some(call_span), sources)?;
            fields.push(binary_segment(pinned));
            Ok(())
        }
        "<<>>" => {
            let Pattern::Bitstring(inner) = decode_bitstring_pattern(&args, node_span, sources)?.node else {
                unreachable!("a bitstring pattern decodes to a bitstring");
            };
            fields.extend(inner);
            Ok(())
        }
        "-" if args.len() == 1 => Err(expected_binary(operand, node.span, call_span, sources)),
        _ => Err(only_binaries_numbers_and_variables(operand, node_span, sources)),
    }
}

fn push_binary_literal(
    operand: &QuotedSourceCursor,
    call_span: Span,
    sources: &SourceMap,
    fields: &mut Vec<BitField<Spanned<Pattern>>>,
) -> Result<(), QuotedSourceError> {
    match operand.root().tag() {
        ValueKind::BITSTRING | ValueKind::PROCBIN => {
            let literal = Spanned::new(Pattern::Binary(operand.raw_bytes()?), call_span);
            fields.push(binary_segment(literal));
            Ok(())
        }
        _ => Err(expected_binary(operand, None, call_span, sources)),
    }
}

/// A segment that is a `binary`: a literal is as long as its bytes, a pinned
/// variable as long as the binary it holds, and a name takes the rest.
fn binary_segment(value: Spanned<Pattern>) -> BitField<Spanned<Pattern>> {
    let spec = BitFieldSpec {
        ty: BitType::Binary,
        ..BitFieldSpec::default()
    };
    BitField {
        spec: sized_for_known_binary(&value.node, spec),
        value,
    }
}

fn expected_binary(
    operand: &QuotedSourceCursor,
    operand_span: Option<Span>,
    call_span: Span,
    sources: &SourceMap,
) -> QuotedSourceError {
    refuse(
        Some(operand_span.unwrap_or(call_span)),
        format!(
            "expected binary argument in <> operator but got: {}",
            render_operand(operand, sources)
        ),
    )
}

fn only_binaries_numbers_and_variables(
    operand: &QuotedSourceCursor,
    operand_span: Span,
    sources: &SourceMap,
) -> QuotedSourceError {
    refuse(
        Some(operand_span),
        format!(
            "a bitstring only accepts binaries, numbers, and variables inside a match, got: {}",
            render_operand(operand, sources)
        ),
    )
}

// ----- `++` ---------------------------------------------------------------

fn decode_list_concat(
    operands: &ConcatOperands,
    span: Span,
    sources: &SourceMap,
) -> Result<Spanned<Pattern>, QuotedSourceError> {
    let items = literal_list_items(&operands.left, span, sources)?;
    let tail = decode_pattern(&operands.right, Some(span), sources)?;
    Ok(list_followed_by(items, tail, span))
}

/// The elements of a literal proper list, which is the only thing `++` can
/// take on its left in a pattern: its length is what makes the rest knowable.
fn literal_list_items(
    list: &QuotedSourceCursor,
    call_span: Span,
    sources: &SourceMap,
) -> Result<Vec<Spanned<Pattern>>, QuotedSourceError> {
    let node = list.ast_node(sources)?;
    let is_literal_list = node.is_none() && (list.root().is_empty_list() || list.root().tag() == ValueKind::LIST);
    let items = if is_literal_list {
        list.list_items()?
    } else {
        Vec::new()
    };
    let improper = match items.last() {
        Some(last) => last.ast_node(sources)?.is_some_and(|marker| {
            marker.head.root().tag() == ValueKind::ATOM && marker.head.atom_name().is_ok_and(|name| name == "|")
        }),
        None => false,
    };
    if !is_literal_list || improper {
        return Err(refuse(
            Some(node.and_then(|node| node.span).unwrap_or(call_span)),
            format!(
                "invalid argument for ++ operator inside a match, expected a literal proper list, got: {}",
                render_operand(list, sources)
            ),
        ));
    }
    items
        .iter()
        .map(|item| decode_pattern(item, Some(call_span), sources))
        .collect()
}

/// `items ++ tail` as one list pattern: a tail that is itself a list pattern
/// continues the list, and no items leaves the tail alone.
fn list_followed_by(items: Vec<Spanned<Pattern>>, tail: Spanned<Pattern>, span: Span) -> Spanned<Pattern> {
    if items.is_empty() {
        return tail;
    }
    match tail.node {
        Pattern::List(rest, rest_tail) => {
            let mut items = items;
            items.extend(rest);
            Spanned::new(Pattern::List(items, rest_tail), span)
        }
        _ => Spanned::new(Pattern::List(items, Some(Box::new(tail))), span),
    }
}

// ----- diagnostics --------------------------------------------------------

fn refuse(span: Option<Span>, message: String) -> QuotedSourceError {
    QuotedSourceError::user(PARSE_CONCAT_PATTERN_OPERAND, span, message)
}

fn source_text(span: Span, sources: &SourceMap) -> Option<&str> {
    sources
        .code(span.source_version)
        .bytes
        .get(span.start as usize..span.end as usize)
}

/// An operand as the author wrote it: the source text when the operand has a
/// location, and the literal's own spelling when it does not.
fn render_operand(operand: &QuotedSourceCursor, sources: &SourceMap) -> String {
    if let Ok(Some(node)) = operand.ast_node(sources)
        && let Some(text) = node.span.and_then(|span| source_text(span, sources))
    {
        return text.to_string();
    }
    render_literal(operand, sources)
}

/// A list element, where an improper tail marker `head | tail` reads as the
/// author wrote it inside the brackets.
fn render_list_element(element: &QuotedSourceCursor, sources: &SourceMap) -> String {
    if let Ok(Some(marker)) = element.ast_node(sources)
        && marker.head.root().tag() == ValueKind::ATOM
        && marker.head.atom_name().is_ok_and(|name| name == "|")
        && let Ok(parts) = marker.tail.list_items()
    {
        return parts
            .iter()
            .map(|part| render_operand(part, sources))
            .collect::<Vec<_>>()
            .join(" | ");
    }
    render_operand(element, sources)
}

fn render_literal(operand: &QuotedSourceCursor, sources: &SourceMap) -> String {
    let root = operand.root();
    match root.tag() {
        ValueKind::INT => operand.int_value().map(|value| value.to_string()),
        ValueKind::FLOAT => root.load_float().map(|value| value.to_string()).map_err(Into::into),
        ValueKind::ATOM => operand.atom_name().map(|name| match name.as_str() {
            "nil" | "true" | "false" => name.to_string(),
            _ => format!(":{name}"),
        }),
        ValueKind::BITSTRING | ValueKind::PROCBIN => operand
            .raw_bytes()
            .map(|bytes| format!("{:?}", String::from_utf8_lossy(&bytes))),
        _ if root.is_empty_list() || root.tag() == ValueKind::LIST => operand.list_items().map(|items| {
            let items = items
                .iter()
                .map(|item| render_list_element(item, sources))
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{items}]")
        }),
        _ => Ok("an unprintable value".to_string()),
    }
    .unwrap_or_else(|_| "an unprintable value".to_string())
}
