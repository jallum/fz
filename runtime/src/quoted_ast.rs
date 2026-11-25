//! The shallow test `unquote(value)` applies to a value spliced into quoted
//! code, as Elixir's `elixir_quote:shallow_valid_ast/1` does: the value is
//! looked at one level deep, so a nested list is accepted without being read.

use crate::any_value::{AnyValueRef, ValueKind, struct_schema_id};
use crate::heap::{Heap, SchemaIdentity, list_head_ref, list_tail_ref};

/// Whether `value` may stand where `unquote(value)` is written: a proper list
/// of valid elements, or a valid element.
pub fn shallow_valid_ast(heap: &Heap, value: AnyValueRef) -> bool {
    if value.tag() == ValueKind::LIST {
        return shallow_valid_list(heap, value);
    }
    shallow_valid_elem(heap, value)
}

fn shallow_valid_list(heap: &Heap, mut list: AnyValueRef) -> bool {
    while !list.is_empty_list() {
        if list.tag() != ValueKind::LIST {
            return false;
        }
        let (Ok(head), Ok(tail)) = (list_head_ref(list), list_tail_ref(list)) else {
            return false;
        };
        if !shallow_valid_elem(heap, head) {
            return false;
        }
        list = tail;
    }
    true
}

/// A list, atom, binary, number, pid or function; a pair of valid elements; or
/// a three-tuple `{call, meta, args}` whose meta is a list, whose args are a
/// list or an atom (a variable's context), and whose call is an atom or valid.
fn shallow_valid_elem(heap: &Heap, value: AnyValueRef) -> bool {
    match value.tag() {
        ValueKind::LIST
        | ValueKind::ATOM
        | ValueKind::BITSTRING
        | ValueKind::BINVIEW
        | ValueKind::BINREF
        | ValueKind::INT
        | ValueKind::FLOAT
        | ValueKind::PID
        | ValueKind::CLOSURE => true,
        ValueKind::STRUCT => match tuple_fields(heap, value).as_deref() {
            Some([left, right]) => shallow_valid_elem(heap, *left) && shallow_valid_elem(heap, *right),
            Some([call, meta, args]) => {
                meta.tag() == ValueKind::LIST
                    && matches!(args.tag(), ValueKind::LIST | ValueKind::ATOM)
                    && (call.tag() == ValueKind::ATOM
                        || (args.tag() == ValueKind::LIST && shallow_valid_ast(heap, *call)))
            }
            _ => false,
        },
        _ => false,
    }
}

/// The fields of a tuple; `None` for a struct, which shares the tag.
fn tuple_fields(heap: &Heap, value: AnyValueRef) -> Option<Vec<AnyValueRef>> {
    let addr = value.struct_addr().ok()?;
    let schema_id = unsafe { struct_schema_id(addr as *const u8) };
    let registry = heap.schemas_registry();
    let registry = registry.borrow();
    let schema = registry.get(schema_id);
    if !matches!(schema.identity, SchemaIdentity::Tuple(_)) {
        return None;
    }
    schema
        .fields
        .iter()
        .map(|field| heap.read_struct_field_ref(value, field.offset).ok())
        .collect()
}

#[cfg(test)]
#[path = "quoted_ast_test.rs"]
mod quoted_ast_test;
