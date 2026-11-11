//! Strict struct layout descriptors + per-process registry.

use crate::module_name::{ModuleName, STRUCT_MODULE_FIELD};
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

/// The bitstring reader's result tuple (`{false}` on a miss) and reader tuple
/// (`{bits, offset, size}`) are the registry's first two schemas, so generated
/// code, the interpreter and the runtime agree on their ids without a program
/// having to declare it reads bitstrings.
pub const BITSTRING_RESULT_SCHEMA: u32 = 0;
pub const BITSTRING_READER_SCHEMA: u32 = 1;

/// One key of a named struct read as a map: the module under `__struct__`,
/// or the field at an index of the schema's fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructKey {
    Module,
    Field(usize),
}

impl Schema {
    /// The keys of this schema read as a map, in map key order (atom names
    /// compare by their text), or `None` when its values are not maps: a tuple
    /// or an internal layout.
    fn map_keys(&self) -> Option<Vec<StructKey>> {
        let SchemaIdentity::Named(_) = self.identity else {
            return None;
        };
        let name = |key: &StructKey| match key {
            StructKey::Module => STRUCT_MODULE_FIELD,
            StructKey::Field(index) => self.fields[*index]
                .name
                .as_deref()
                .expect("a named struct's field has a name"),
        };
        let mut keys: Vec<StructKey> = std::iter::once(StructKey::Module)
            .chain((0..self.fields.len()).map(StructKey::Field))
            .collect();
        keys.sort_by(|a, b| name(a).cmp(name(b)));
        Some(keys)
    }
}

pub struct SchemaRegistry {
    schemas: Vec<Schema>,
    map_keys: Vec<Option<Vec<StructKey>>>,
}

impl SchemaRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            schemas: Vec::new(),
            map_keys: Vec::new(),
        };
        let result = registry.register(Schema::tuple_of_arity(1));
        let reader = registry.register(Schema::tuple_of_arity(3));
        debug_assert_eq!((result, reader), (BITSTRING_RESULT_SCHEMA, BITSTRING_READER_SCHEMA));
        registry
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
        self.map_keys.push(schema.map_keys());
        self.schemas.push(schema);
        id
    }

    pub fn range(&mut self) -> u32 {
        self.register(Schema::range())
    }

    pub fn get(&self, id: u32) -> &Schema {
        &self.schemas[id as usize]
    }

    /// The named struct whose module is the atom spelled `atom_name`.
    pub fn named_by_atom_name(&self, atom_name: &str) -> Option<u32> {
        self.schemas
            .iter()
            .position(|schema| matches!(&schema.identity, SchemaIdentity::Named(name) if name.atom_name() == atom_name))
            .map(|id| id as u32)
    }

    /// The keys of schema `id`'s values read as maps, in map key order; `None`
    /// when they are not maps.
    pub fn map_keys(&self, id: u32) -> Option<&[StructKey]> {
        self.map_keys[id as usize].as_deref()
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
