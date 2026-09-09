//! Strict struct layout descriptors + per-process registry.

use crate::module_name::ModuleName;
use std::borrow::Cow;
use std::cmp::Ordering;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchemaIdentity {
    Tuple(usize),
    Named(ModuleName),
    Internal(String),
}

impl SchemaIdentity {
    pub fn semantic_cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Tuple(a), Self::Tuple(b)) => a.cmp(b),
            (Self::Named(a), Self::Named(b)) => a.cmp(b),
            (Self::Tuple(_), Self::Named(_)) => Ordering::Less,
            (Self::Named(_), Self::Tuple(_)) => Ordering::Greater,
            _ => panic!("internal storage schema is not a language value"),
        }
    }

    pub fn display_name(&self) -> Cow<'_, str> {
        match self {
            Self::Tuple(arity) => Cow::Owned(format!("Tuple{arity}")),
            Self::Named(name) => Cow::Owned(name.to_string()),
            Self::Internal(name) => Cow::Borrowed(name),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldKind {
    /// Dynamic field stored as a raw payload plus compact kind metadata.
    /// GC traces heap-kind payloads.
    AnyValue,
    /// Eight bytes of raw f64 payload, not traced by GC.
    RawF64,
    /// Eight bytes of raw i64 payload, not traced by GC.
    RawI64,
    /// A fixed-width byte field, not traced by GC.
    RawBytes(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FieldDescriptor {
    pub offset: u32,
    pub kind: FieldKind,
    pub name: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Schema {
    pub identity: SchemaIdentity,
    pub size: u32,
    pub fields: Vec<FieldDescriptor>,
}

impl Schema {
    pub const RANGE_NAME: &str = "Range";

    pub fn is_range(&self) -> bool {
        matches!(&self.identity, SchemaIdentity::Named(name) if name.segments().len() == 1 && name.last_segment() == Self::RANGE_NAME)
    }

    /// One typed arity and layout shared by interpreter, JIT, and AOT tuples.
    pub fn tuple_of_arity(arity: usize) -> Self {
        Self {
            identity: SchemaIdentity::Tuple(arity),
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

    pub fn named_struct(name: ModuleName, fields: impl IntoIterator<Item = String>) -> Self {
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
            identity: SchemaIdentity::Named(name),
            size: (fields.len() * 8) as u32,
            fields,
        }
    }

    /// Elixir-parity Range struct. It is a normal schema-backed Struct, not
    /// a distinct heap tag. Its field layout comes from the source-level
    /// `defstruct [:first, :last, :step]` declaration.
    pub fn range() -> Self {
        Self::named_struct(
            ModuleName::from_segments(vec![Self::RANGE_NAME.into()]),
            ["first".to_string(), "last".to_string(), "step".to_string()],
        )
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
            self.identity.display_name(),
            field_offset
        );
    }

    pub fn any_value_fields_with_kind_offsets(&self) -> impl Iterator<Item = (&FieldDescriptor, u32)> {
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
        Self { schemas: Vec::new() }
    }

    pub fn register(&mut self, schema: Schema) -> u32 {
        if let Some((id, existing)) = self
            .schemas
            .iter()
            .enumerate()
            .find(|(_, existing)| existing.identity == schema.identity)
        {
            assert_eq!(existing, &schema, "one schema identity must have one layout");
            return id as u32;
        }
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn range(&mut self) -> u32 {
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
