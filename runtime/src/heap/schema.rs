//! Strict struct layout descriptors + per-process registry.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FieldKind {
    /// Dynamic field stored as a raw payload plus compact kind metadata.
    /// GC traces heap-kind payloads.
    AnyValue,
    /// 8 bytes of raw f64 payload. GC tracer skips this slot. Introduced by
    /// fz-ul4.27.5.2 to let typed-float entry-frame params live as raw f64
    /// instead of as a tagged heap object.
    RawF64,
    /// 8 bytes of raw i64 — an int payload with the tag/shift stripped.
    /// GC tracer skips this slot. Introduced by fz-ul4.27.5.3 so typed-int
    /// entry-frame params can live as raw i64 instead of the tagged
    /// `(n << 3) | TAG_INT` form, letting arithmetic ops skip the
    /// per-op sshr/ishl round trip.
    RawI64,
    /// Generic raw bytes — width in bytes. GC tracer skips this slot. Used
    /// by miscellaneous non-frame schemas (bitstrings, etc.) and reserved
    /// for VR.3.3 (raw i64 entry-param slots).
    RawBytes(u32),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDescriptor {
    pub offset: u32,
    pub kind: FieldKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Schema {
    pub name: String,
    pub size: u32,
    pub fields: Vec<FieldDescriptor>,
}

impl Schema {
    pub const RANGE_NAME: &str = "Range";

    /// fz-ul4.38 — canonical `Tuple{N}` schema. N typed any values at offsets
    /// 0, 8, 16, … Used by every path that registers tuple schemas: JIT
    /// codegen (`ir_codegen::compile_with_backend`), interp lazy
    /// registration (`ir_interp::interp_tuple_schema_id`), and the AOT
    /// startup hook (`aot_shim::fz_aot_setup`). Single source of truth.
    pub fn tuple_of_arity(arity: usize) -> Self {
        Self {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::AnyValue,
                    name: None,
                })
                .collect(),
        }
    }

    pub fn named_struct(name: impl Into<String>, fields: impl IntoIterator<Item = String>) -> Self {
        let fields = fields
            .into_iter()
            .enumerate()
            .map(|(i, name)| FieldDescriptor {
                offset: (i * 8) as u32,
                kind: FieldKind::AnyValue,
                name: Some(name),
            })
            .collect::<Vec<_>>();
        Self {
            name: name.into(),
            size: (fields.len() * 8) as u32,
            fields,
        }
    }

    /// Elixir-parity Range struct. It is a normal schema-backed Struct, not
    /// a distinct heap tag. Its field layout comes from the source-level
    /// `defstruct [:first, :last, :step]` declaration.
    pub fn range() -> Self {
        Self {
            ..Self::named_struct(
                Self::RANGE_NAME,
                ["first".to_string(), "last".to_string(), "step".to_string()],
            )
        }
    }

    /// Closure environment schema. Payload offset 0 is the raw code pointer
    /// and is never traced. Captures are ordinary `AnyValue` fields starting
    /// at payload offset 8, so closure environments use the same field
    /// access and GC tracing machinery as tuples.
    pub fn closure_env(captures: usize) -> Self {
        let mut fields = Vec::with_capacity(captures + 1);
        fields.push(FieldDescriptor {
            offset: 0,
            kind: FieldKind::RawBytes(8),
            name: None,
        });
        fields.extend((0..captures).map(|i| FieldDescriptor {
            offset: 8 + (i * 8) as u32,
            kind: FieldKind::AnyValue,
            name: None,
        }));
        Self {
            name: format!("ClosureEnv{}", captures),
            size: ((captures + 1) * 8) as u32,
            fields,
        }
    }

    pub fn value_field_count(&self) -> usize {
        self.fields
            .iter()
            .filter(|field| field.kind == FieldKind::AnyValue)
            .count()
    }

    pub fn allocation_payload_size(&self) -> usize {
        let kind_bytes = (self.value_field_count() + 7) & !7;
        self.size as usize + kind_bytes
    }

    pub fn value_field_kind_offset(&self, field_offset: u32) -> u32 {
        let mut index = 0u32;
        for field in &self.fields {
            if field.kind == FieldKind::AnyValue {
                if field.offset == field_offset {
                    return self.size + index;
                }
                index += 1;
            }
        }
        panic!(
            "schema {} has no AnyValue field at offset {}",
            self.name, field_offset
        );
    }

    pub fn any_value_fields_with_kind_offsets(
        &self,
    ) -> impl Iterator<Item = (&FieldDescriptor, u32)> {
        let mut index = 0u32;
        self.fields.iter().filter_map(move |field| {
            if field.kind != FieldKind::AnyValue {
                return None;
            }
            let kind_offset = self.size + index;
            index += 1;
            Some((field, kind_offset))
        })
    }
}

pub struct SchemaRegistry {
    schemas: Vec<Schema>,
}

impl SchemaRegistry {
    pub fn new() -> Self {
        Self {
            schemas: Vec::new(),
        }
    }

    pub fn register(&mut self, schema: Schema) -> u32 {
        if let Some((id, _)) = self
            .schemas
            .iter()
            .enumerate()
            .find(|(_, existing)| existing.name == schema.name)
        {
            return id as u32;
        }
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn closure_env(&mut self, captures: usize) -> u32 {
        let name = format!("ClosureEnv{}", captures);
        if let Some((id, _)) = self
            .schemas
            .iter()
            .enumerate()
            .find(|(_, schema)| schema.name == name)
        {
            return id as u32;
        }
        self.register(Schema::closure_env(captures))
    }

    pub fn range(&mut self) -> u32 {
        if let Some((id, _)) = self
            .schemas
            .iter()
            .enumerate()
            .find(|(_, schema)| schema.name == Schema::RANGE_NAME)
        {
            return id as u32;
        }
        self.register(Schema::range())
    }

    pub fn get(&self, id: u32) -> &Schema {
        &self.schemas[id as usize]
    }

    pub fn len(&self) -> usize {
        self.schemas.len()
    }

    pub fn is_empty(&self) -> bool {
        self.schemas.is_empty()
    }
}

impl Default for SchemaRegistry {
    fn default() -> Self {
        Self::new()
    }
}
