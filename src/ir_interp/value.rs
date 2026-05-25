use super::*;
use fz_runtime::fz_value::{AnyValue as RuntimeAnyValue, ValueKind};
use fz_runtime::tagged_value_ref::{TaggedValueRef, TaggedValueTag};

#[derive(Clone, Copy, Debug)]
/// Interpreter/REPL convenience view only. Keep runtime ABI, heap storage,
/// mailbox/scheduler state, and generated JIT/AOT code on opaque tagged words
/// rather than letting this become another runtime value representation.
pub(super) enum AnyValue {
    Null,
    Int(i64),
    Float(f64),
    Atom(u32),
    EmptyList,
    Ref(TaggedValueRef),
}

impl AnyValue {
    pub(super) fn value(self) -> Result<RuntimeAnyValue, String> {
        Ok(match self {
            AnyValue::Null => RuntimeAnyValue::null(),
            AnyValue::Int(value) => RuntimeAnyValue::int(value),
            AnyValue::Float(value) => RuntimeAnyValue::float(value),
            AnyValue::Atom(value) => RuntimeAnyValue::atom(value),
            AnyValue::EmptyList => RuntimeAnyValue::empty_list(),
            AnyValue::Ref(value) => fz_runtime::heap::any_value_from_ref(value)
                .map_err(|err| format!("interpreter ref storage view: {err:?}"))?,
        })
    }

    pub(super) fn extern_arg_bits(self) -> Result<u64, String> {
        match self {
            AnyValue::Null => Ok(0),
            AnyValue::Int(value) => Ok(value as u64),
            AnyValue::Float(_) => {
                Err("raw interpreter float cannot be materialized as extern arg bits".into())
            }
            AnyValue::Atom(value) => Ok(value as u64),
            AnyValue::EmptyList => Ok(0),
            AnyValue::Ref(value) => Ok(value.raw_word()),
        }
    }

    pub(super) fn extern_arg_ref_word(self) -> Result<u64, String> {
        self.as_ref_word()
    }

    pub(super) fn from_tagged_ref(value: TaggedValueRef) -> Result<Self, String> {
        interp_value_from_ref_word(value.raw_word(), "interpreter tagged mailbox value")
    }

    pub(super) fn as_ref_word(self) -> Result<u64, String> {
        match self {
            AnyValue::Null => Ok(TaggedValueRef::null().raw_word()),
            AnyValue::Int(value) => Ok(fz_runtime::ir_runtime::fz_box_int_for_any(value)),
            AnyValue::Float(value) => Ok(fz_runtime::ir_runtime::fz_box_float_for_any(value)),
            AnyValue::Atom(value) => Ok(fz_runtime::ir_runtime::fz_box_atom_for_any(value as u64)),
            AnyValue::EmptyList => Ok(TaggedValueRef::empty_list().raw_word()),
            AnyValue::Ref(value) => Ok(value.raw_word()),
        }
    }

    pub(super) fn as_tagged_ref(self) -> Result<TaggedValueRef, String> {
        let ref_word = self.as_ref_word()?;
        TaggedValueRef::from_raw_word(ref_word)
            .map_err(|err| format!("interpreter value ref word {ref_word:#x}: {err:?}"))
    }

    pub(super) fn as_float(self) -> Option<f64> {
        match self {
            AnyValue::Int(value) => Some(value as f64),
            AnyValue::Float(value) => Some(value),
            _ => None,
        }
    }

    pub(super) fn as_i64(self) -> Option<i64> {
        match self {
            AnyValue::Int(value) => Some(value),
            _ => None,
        }
    }

    pub(super) fn is_empty_list(self) -> bool {
        matches!(self, AnyValue::EmptyList)
    }

    pub(super) fn is_truthy(self) -> bool {
        match self {
            AnyValue::Atom(value) => !matches!(
                value,
                fz_runtime::fz_value::FALSE_ATOM_ID | fz_runtime::fz_value::NIL_ATOM_ID
            ),
            _ => true,
        }
    }

    pub(super) fn is_nil(self) -> bool {
        matches!(self, AnyValue::Atom(fz_runtime::fz_value::NIL_ATOM_ID))
    }

    pub(super) fn is_false(self) -> bool {
        matches!(self, AnyValue::Atom(fz_runtime::fz_value::FALSE_ATOM_ID))
    }

    pub(super) fn is_atom_id(self, atom_id: u32) -> bool {
        matches!(self, AnyValue::Atom(value) if value == atom_id)
    }

    pub(super) fn print(self) -> Result<(), String> {
        match self {
            AnyValue::Null => {
                fz_runtime::ir_runtime::fz_print_value_ref(TaggedValueRef::null().raw_word());
                Ok(())
            }
            AnyValue::Int(value) => {
                fz_runtime::fz_print_i64(value);
                Ok(())
            }
            AnyValue::Atom(_) | AnyValue::EmptyList | AnyValue::Ref(_) => {
                fz_runtime::ir_runtime::fz_print_value_ref(self.as_ref_word()?);
                Ok(())
            }
            AnyValue::Float(value) => {
                fz_runtime::fz_print_f64(value);
                Ok(())
            }
        }
    }

    pub(super) fn render(self) -> String {
        match self {
            AnyValue::Null => "null".to_string(),
            AnyValue::Int(value) => value.to_string(),
            AnyValue::Float(value) => value.to_string(),
            AnyValue::Atom(value) => {
                fz_runtime::fz_value::debug::render_value(RuntimeAnyValue::atom(value))
            }
            AnyValue::EmptyList => {
                fz_runtime::fz_value::debug::render_value(RuntimeAnyValue::empty_list())
            }
            AnyValue::Ref(value) => fz_runtime::fz_value::debug::render_value(
                fz_runtime::heap::any_value_from_ref(value).unwrap_or(RuntimeAnyValue::null()),
            ),
        }
    }
}

pub(super) fn bitstring_like_ptr(bits: u64) -> Option<*mut u8> {
    if matches!(
        bits & fz_runtime::fz_value::TAG_MASK,
        fz_runtime::fz_value::TAG_BITSTRING | fz_runtime::fz_value::TAG_PROCBIN
    ) {
        Some(bits as *mut u8)
    } else {
        None
    }
}

/// fz-ul4.35 — get-or-register a heap schema for a tuple of `arity`,
/// matching the JIT codegen layout in src/ir_codegen.rs (Tuple{N}, N*8
/// payload bytes, N RuntimeAnyValue fields at offsets 0, 8, 16, ...).
pub(super) fn interp_tuple_schema_id(arity: usize) -> u32 {
    INTERP_TUPLE_SCHEMA_IDS.with(|m| {
        if let Some(&id) = m.borrow().get(&arity) {
            return id;
        }
        use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
        let s = Schema {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::AnyValue,
                })
                .collect(),
        };
        let registry = fz_runtime::process::current_process()
            .heap
            .schemas_registry();
        let id = registry.borrow_mut().register(s);
        m.borrow_mut().insert(arity, id);
        id
    })
}

pub(super) fn interp_list_ptr(value: RuntimeAnyValue) -> Option<*mut u8> {
    if value.kind() == ValueKind::LIST {
        return (value.raw() != 0)
            .then(|| value.heap_addr())
            .flatten()
            .filter(|p| !p.is_null());
    }
    None
}

pub(super) fn interp_value_from_ref_word(ref_word: u64, context: &str) -> Result<AnyValue, String> {
    let value = TaggedValueRef::from_raw_word(ref_word)
        .map_err(|err| format!("{context}: invalid tagged value ref {ref_word:#x}: {err:?}"))?;
    let tag = fz_runtime::ir_runtime::fz_ref_tag(ref_word);
    Ok(
        match TaggedValueTag::try_from(tag)
            .map_err(|err| format!("{context}: invalid tagged value tag {tag}: {err:?}"))?
        {
            TaggedValueTag::Null => AnyValue::Null,
            TaggedValueTag::Int => AnyValue::Int(fz_runtime::ir_runtime::fz_ref_load_int(ref_word)),
            TaggedValueTag::Float => {
                AnyValue::Float(fz_runtime::ir_runtime::fz_ref_load_float(ref_word))
            }
            TaggedValueTag::Atom => {
                AnyValue::Atom(fz_runtime::ir_runtime::fz_ref_load_atom(ref_word) as u32)
            }
            TaggedValueTag::EmptyList => AnyValue::EmptyList,
            TaggedValueTag::List
            | TaggedValueTag::Map
            | TaggedValueTag::Struct
            | TaggedValueTag::Closure
            | TaggedValueTag::Bitstring
            | TaggedValueTag::ProcBin
            | TaggedValueTag::Resource => AnyValue::Ref(value),
        },
    )
}

pub(super) fn with_value_ref<T>(
    value: AnyValue,
    context: &str,
    f: impl FnOnce(u64) -> T,
) -> Result<T, String> {
    let value_ref = value
        .as_ref_word()
        .map_err(|err| format!("{context}: cannot create tagged ref: {err}"))?;
    Ok(f(value_ref))
}

pub(super) fn interp_struct_field_from_tagged_bits(
    bits: u64,
    field_offset: u32,
    context: &str,
) -> Result<AnyValue, String> {
    let value = interp_value_from_ref_word(bits, context)?;
    with_value_ref(value, context, |struct_ref| {
        fz_runtime::ir_runtime::fz_struct_get_field_ref(struct_ref, field_offset)
    })
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, context))
}

pub(super) fn interp_is_list_cons(value: RuntimeAnyValue) -> bool {
    interp_list_ptr(value).is_some()
}

pub(super) fn guard_int(v: AnyValue) -> Option<i64> {
    v.as_i64()
}

pub(super) fn interp_bool_value(b: bool) -> AnyValue {
    AnyValue::Atom(if b {
        fz_runtime::fz_value::TRUE_ATOM_ID
    } else {
        fz_runtime::fz_value::FALSE_ATOM_ID
    })
}

pub(super) fn interp_nil_value() -> AnyValue {
    AnyValue::Atom(fz_runtime::fz_value::NIL_ATOM_ID)
}

pub(super) fn interp_empty_list_value() -> AnyValue {
    AnyValue::EmptyList
}

pub(super) fn interp_value_from_extern_ref_word(ref_word: u64) -> Result<AnyValue, String> {
    interp_value_from_ref_word(ref_word, "extern any return")
}

pub(super) fn is_map_value(val: RuntimeAnyValue) -> bool {
    val.kind() == ValueKind::MAP && val.heap_addr().is_some_and(|p| !p.is_null())
}

pub(super) fn interp_value_from_slot(value: fz_runtime::fz_value::AnyValue) -> AnyValue {
    match value.kind() {
        fz_runtime::fz_value::ValueKind::NULL => AnyValue::Null,
        fz_runtime::fz_value::ValueKind::FLOAT => AnyValue::Float(f64::from_bits(value.raw())),
        fz_runtime::fz_value::ValueKind::INT => AnyValue::Int(value.raw() as i64),
        fz_runtime::fz_value::ValueKind::ATOM => AnyValue::Atom(value.raw() as u32),
        fz_runtime::fz_value::ValueKind::LIST if value.raw() == 0 => AnyValue::EmptyList,
        _ => AnyValue::Ref(value.ref_word()),
    }
}
