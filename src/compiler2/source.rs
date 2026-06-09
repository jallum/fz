use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{self, Write};
use std::ptr;
use std::rc::Rc;
use std::slice;

use fz_runtime::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, ValueKind, map_count, map_key_kind, map_keys_ptr, map_tag_ptr,
    map_value_kind, map_values_ptr, struct_schema_id,
};
use fz_runtime::heap::{SHARED_BIN_THRESHOLD_BYTES, Schema, SchemaRegistry};
use fz_runtime::procbin::bitstring_bit_len as tagged_bitstring_bit_len;
use fz_runtime::procbin::bitstring_byte_ptr as procbin_byte_ptr;
use fz_runtime::process::{CompiledModuleConsts, DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process};

const NIL_ATOM: &str = "nil";
const TRUE_ATOM: &str = "true";
const FALSE_ATOM: &str = "false";

const META_LEXICAL_KEY: &str = "__fz_lexical__";
const META_NAMESPACE_ID_KEY: &str = "__fz_namespace_id__";
const META_SPAN_KEY: &str = "__fz_span__";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedSourceError {
    message: String,
}

impl QuotedSourceError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for QuotedSourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl From<AnyValueRefError> for QuotedSourceError {
    fn from(value: AnyValueRefError) -> Self {
        Self::new(format!("invalid any value ref: {value:?}"))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotedSourceFingerprintPolicy {
    Semantic,
    Diagnostic,
}

impl QuotedSourceFingerprintPolicy {
    fn includes_meta_key(self, key: &str) -> bool {
        match key {
            META_NAMESPACE_ID_KEY => false,
            META_SPAN_KEY => matches!(self, Self::Diagnostic),
            _ => true,
        }
    }
}

/// Non-owning comparison key for a quoted source root.
///
/// This is only meaningful while some `QuotedSourceRoot` (or equivalent owner)
/// keeps the heap alive. It is not itself a rooted carrier for the source
/// graph; storing `QuotedSourceKey` without the owning heap/root state would
/// leave the raw `AnyValueRef` dangling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuotedSourceKey {
    pub heap_id: usize,
    pub root: AnyValueRef,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedSourceFingerprint {
    pub policy: QuotedSourceFingerprintPolicy,
    pub digest: String,
    pub canonical: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedSourceCarrier {
    pub root: QuotedSourceRoot,
    pub semantic: QuotedSourceFingerprint,
}

impl QuotedSourceCarrier {
    pub fn new(root: QuotedSourceRoot) -> Result<Self, QuotedSourceError> {
        let semantic = root.fingerprint(QuotedSourceFingerprintPolicy::Semantic)?;
        Ok(Self { root, semantic })
    }

    pub fn empty() -> Self {
        let heap = Rc::new(QuotedSourceHeap::new());
        let root = QuotedSourceRoot::new(heap, AnyValueRef::empty_list());
        Self::new(root).expect("empty quoted source carrier should fingerprint")
    }

    pub fn key(&self) -> QuotedSourceKey {
        self.root.key()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotedLexicalContextKind {
    Source,
    Definition,
    Caller,
    Generated,
}

impl QuotedLexicalContextKind {
    fn atom_name(self) -> &'static str {
        match self {
            Self::Source => "source",
            Self::Definition => "definition",
            Self::Caller => "caller",
            Self::Generated => "generated",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedLexicalContext {
    pub kind: QuotedLexicalContextKind,
    pub module: Vec<String>,
    pub scope: Vec<String>,
    pub namespace_id: Option<u32>,
}

impl QuotedLexicalContext {
    pub fn new(kind: QuotedLexicalContextKind, module: Vec<String>, scope: Vec<String>) -> Self {
        Self {
            kind,
            module,
            scope,
            namespace_id: None,
        }
    }

    pub fn with_namespace_id(mut self, namespace_id: u32) -> Self {
        self.namespace_id = Some(namespace_id);
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotedSourceSpan {
    pub source_name: String,
    pub line: u32,
    pub column: u32,
    pub length: u32,
}

impl QuotedSourceSpan {
    pub fn new(source_name: impl Into<String>, line: u32, column: u32, length: u32) -> Self {
        Self {
            source_name: source_name.into(),
            line,
            column,
            length,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct QuotedSourceMetadata {
    pub lexical_context: Option<QuotedLexicalContext>,
    pub span: Option<QuotedSourceSpan>,
}

/// Owns the source-process heap that backs one quoted-source graph.
///
/// The root handle itself is only an `AnyValueRef`. Keeping the heap alive is
/// what makes the root durable across job boundaries, so `QuotedSourceRoot`
/// retains this heap by `Rc`.
///
/// Compiler2 treats this heap as an arena while quoted source escapes into
/// fact/state storage: the heap may grow, but it must not run a moving GC
/// behind out-of-band `AnyValueRef` roots held in Rust state. A bare
/// `{heap_id, root}` label is therefore not enough to carry quoted source; the
/// owning `QuotedSourceRoot` is the actual transport/persistence unit.
pub struct QuotedSourceHeap {
    process: RefCell<Process>,
    tuple_schemas: RefCell<HashMap<usize, u32>>,
    interned_lists: RefCell<HashMap<Vec<u64>, AnyValueRef>>,
}

impl fmt::Debug for QuotedSourceHeap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("QuotedSourceHeap")
            .field("heap_id", &format_args!("{:#x}", self as *const Self as usize))
            .field("tuple_schema_count", &self.tuple_schemas.borrow().len())
            .finish()
    }
}

impl Default for QuotedSourceHeap {
    fn default() -> Self {
        Self::new()
    }
}

impl QuotedSourceHeap {
    pub fn new() -> Self {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let node = Rc::new(Node::new(
            vec![NIL_ATOM.to_string(), TRUE_ATOM.to_string(), FALSE_ATOM.to_string()],
            Vec::new(),
        ));
        let process = Process::from_consts(
            node,
            schemas,
            &CompiledModuleConsts::empty(),
            0,
            DEFAULT_REDUCTIONS_PER_QUANTUM,
        );
        Self {
            process: RefCell::new(process),
            tuple_schemas: RefCell::new(HashMap::new()),
            interned_lists: RefCell::new(HashMap::new()),
        }
    }

    pub fn builder(self: &Rc<Self>) -> QuotedSourceBuilder {
        QuotedSourceBuilder { heap: self.clone() }
    }

    pub fn cursor(self: &Rc<Self>, root: AnyValueRef) -> QuotedSourceCursor {
        QuotedSourceCursor {
            heap: self.clone(),
            root,
        }
    }

    fn key(self: &Rc<Self>, root: AnyValueRef) -> QuotedSourceKey {
        QuotedSourceKey {
            heap_id: Rc::as_ptr(self) as usize,
            root,
        }
    }

    fn tuple_schema_id(&self, proc: &mut Process, arity: usize) -> u32 {
        if let Some(schema_id) = self.tuple_schemas.borrow().get(&arity).copied() {
            return schema_id;
        }
        let schema_id = proc.heap.register_schema(Schema::tuple_of_arity(arity));
        self.tuple_schemas.borrow_mut().insert(arity, schema_id);
        schema_id
    }
}

#[derive(Debug, Clone)]
pub struct QuotedSourceBuilder {
    heap: Rc<QuotedSourceHeap>,
}

impl QuotedSourceBuilder {
    pub fn int(&self, value: i64) -> AnyValueRef {
        let mut proc = self.heap.process.borrow_mut();
        proc.heap.box_any_value_ref(AnyValue::int(value))
    }

    pub fn float(&self, value: f64) -> AnyValueRef {
        let mut proc = self.heap.process.borrow_mut();
        proc.heap.box_any_value_ref(AnyValue::float(value))
    }

    pub fn atom(&self, name: &str) -> AnyValueRef {
        let mut proc = self.heap.process.borrow_mut();
        let atom_id = proc.node.intern_atom(name);
        proc.heap.box_any_value_ref(AnyValue::atom(atom_id))
    }

    pub fn bool(&self, value: bool) -> AnyValueRef {
        let mut proc = self.heap.process.borrow_mut();
        proc.heap.box_any_value_ref(AnyValue::bool_atom(value))
    }

    pub fn nil(&self) -> AnyValueRef {
        let mut proc = self.heap.process.borrow_mut();
        proc.heap.box_any_value_ref(AnyValue::nil_atom())
    }

    pub fn empty_list(&self) -> AnyValueRef {
        AnyValueRef::empty_list()
    }

    pub fn bitstring(&self, bytes: &[u8], bit_len: u64) -> Result<AnyValueRef, QuotedSourceError> {
        let mut proc = self.heap.process.borrow_mut();
        let ptr = proc.heap.alloc_bitstring(bytes, bit_len);
        let kind = if bytes.len() > SHARED_BIN_THRESHOLD_BYTES {
            ValueKind::PROCBIN
        } else {
            ValueKind::BITSTRING
        };
        AnyValueRef::from_heap_object(kind, ptr).map_err(QuotedSourceError::from)
    }

    pub fn utf8_binary(&self, text: &str) -> Result<AnyValueRef, QuotedSourceError> {
        self.bitstring(text.as_bytes(), (text.len() * 8) as u64)
    }

    pub fn list(&self, items: &[AnyValueRef]) -> Result<AnyValueRef, QuotedSourceError> {
        let mut proc = self.heap.process.borrow_mut();
        let mut tail = AnyValueRef::empty_list();
        for item in items.iter().rev().copied() {
            tail = proc
                .heap
                .alloc_list_cons_any(any_value_from_ref(item)?, tail)
                .map_err(QuotedSourceError::from)?;
        }
        Ok(tail)
    }

    pub fn interned_list(&self, items: &[AnyValueRef]) -> Result<AnyValueRef, QuotedSourceError> {
        let key = items.iter().map(|item| item.raw_word()).collect::<Vec<_>>();
        if let Some(existing) = self.heap.interned_lists.borrow().get(&key).copied() {
            return Ok(existing);
        }
        let list = self.list(items)?;
        self.heap.interned_lists.borrow_mut().insert(key, list);
        Ok(list)
    }

    pub fn tuple(&self, items: &[AnyValueRef]) -> Result<AnyValueRef, QuotedSourceError> {
        let mut proc = self.heap.process.borrow_mut();
        let schema_id = self.heap.tuple_schema_id(&mut proc, items.len());
        let ptr = proc.heap.alloc_struct(schema_id);
        for (index, item) in items.iter().copied().enumerate() {
            proc.heap
                .write_field_slot(ptr, (index * 8) as u32, any_value_from_ref(item)?);
        }
        AnyValueRef::from_heap_object(ValueKind::STRUCT, ptr).map_err(QuotedSourceError::from)
    }

    pub fn map(&self, entries: &[(AnyValueRef, AnyValueRef)]) -> Result<AnyValueRef, QuotedSourceError> {
        let mut sorted = entries.to_vec();
        sorted.sort_by(|(left, _), (right, _)| map_key_cmp(*left, *right));
        let mut proc = self.heap.process.borrow_mut();
        proc.heap.alloc_map_refs(&sorted).map_err(QuotedSourceError::from)
    }

    pub fn lexical_context(&self, context: &QuotedLexicalContext) -> Result<AnyValueRef, QuotedSourceError> {
        let kind_key = self.atom("kind");
        let module_key = self.atom("module");
        let scope_key = self.atom("scope");
        let namespace_key = self.atom(META_NAMESPACE_ID_KEY);
        let kind_value = self.atom(context.kind.atom_name());
        let module_value = self.atom_list(&context.module)?;
        let scope_value = self.atom_list(&context.scope)?;
        let mut entries = vec![
            (kind_key, kind_value),
            (module_key, module_value),
            (scope_key, scope_value),
        ];
        if let Some(namespace_id) = context.namespace_id {
            entries.push((namespace_key, self.int(namespace_id as i64)));
        }
        self.map(&entries)
    }

    pub fn span(&self, span: &QuotedSourceSpan) -> Result<AnyValueRef, QuotedSourceError> {
        self.map(&[
            (self.atom("source"), self.utf8_binary(&span.source_name)?),
            (self.atom("line"), self.int(span.line as i64)),
            (self.atom("column"), self.int(span.column as i64)),
            (self.atom("length"), self.int(span.length as i64)),
        ])
    }

    pub fn meta(&self, meta: &QuotedSourceMetadata) -> Result<AnyValueRef, QuotedSourceError> {
        let mut entries = Vec::new();
        if let Some(context) = &meta.lexical_context {
            entries.push((self.atom(META_LEXICAL_KEY), self.lexical_context(context)?));
        }
        if let Some(span) = &meta.span {
            entries.push((self.atom(META_SPAN_KEY), self.span(span)?));
        }
        self.map(&entries)
    }

    pub fn ast_node(
        &self,
        head: AnyValueRef,
        meta: &QuotedSourceMetadata,
        tail: AnyValueRef,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        self.tuple(&[head, self.meta(meta)?, tail])
    }

    pub fn variable(&self, name: &str, meta: &QuotedSourceMetadata) -> Result<AnyValueRef, QuotedSourceError> {
        let context = if let Some(context) = &meta.lexical_context {
            self.lexical_context(context)?
        } else {
            self.nil()
        };
        self.ast_node(self.atom(name), meta, context)
    }

    pub fn call(
        &self,
        name: &str,
        meta: &QuotedSourceMetadata,
        args: &[AnyValueRef],
    ) -> Result<AnyValueRef, QuotedSourceError> {
        self.ast_node(self.atom(name), meta, self.list(args)?)
    }

    pub fn call_callee(
        &self,
        callee: AnyValueRef,
        meta: &QuotedSourceMetadata,
        args: &[AnyValueRef],
    ) -> Result<AnyValueRef, QuotedSourceError> {
        self.ast_node(callee, meta, self.list(args)?)
    }

    pub fn alias(&self, meta: &QuotedSourceMetadata, segments: &[&str]) -> Result<AnyValueRef, QuotedSourceError> {
        let values = segments.iter().map(|segment| self.atom(segment)).collect::<Vec<_>>();
        self.ast_node(self.atom("__aliases__"), meta, self.list(&values)?)
    }

    pub fn keyword(&self, key: &str, value: AnyValueRef) -> Result<AnyValueRef, QuotedSourceError> {
        self.tuple(&[self.atom(key), value])
    }

    pub fn root(&self, root: AnyValueRef) -> Result<QuotedSourceRoot, QuotedSourceError> {
        Ok(QuotedSourceRoot::new(self.heap.clone(), root))
    }

    fn atom_list(&self, atoms: &[String]) -> Result<AnyValueRef, QuotedSourceError> {
        let values = atoms.iter().map(|atom| self.atom(atom)).collect::<Vec<_>>();
        self.list(&values)
    }
}

#[derive(Debug, Clone)]
pub struct QuotedSourceRoot {
    heap: Rc<QuotedSourceHeap>,
    root: AnyValueRef,
    key: QuotedSourceKey,
}

impl QuotedSourceRoot {
    /// The owning quoted-source carrier.
    ///
    /// Keeping this object alive keeps the source heap alive. Compiler2 state
    /// that persists quoted source must store this owner (or another object
    /// with the same rooting contract), not just `AnyValueRef` or
    /// `QuotedSourceKey`.
    pub fn new(heap: Rc<QuotedSourceHeap>, root: AnyValueRef) -> Self {
        Self {
            key: heap.key(root),
            heap,
            root,
        }
    }

    pub fn root(&self) -> AnyValueRef {
        self.root
    }

    pub fn key(&self) -> QuotedSourceKey {
        self.key
    }

    pub fn fingerprint(
        &self,
        policy: QuotedSourceFingerprintPolicy,
    ) -> Result<QuotedSourceFingerprint, QuotedSourceError> {
        fingerprint_root(&self.heap, self.root, policy)
    }

    pub fn cursor(&self) -> QuotedSourceCursor {
        self.heap.cursor(self.root)
    }

    fn builder(&self) -> QuotedSourceBuilder {
        self.heap.builder()
    }

    pub fn interned_list_subroot(&self, items: &[AnyValueRef]) -> Result<Self, QuotedSourceError> {
        let list = self.builder().interned_list(items)?;
        Ok(self.subroot(list))
    }

    pub fn subroot(&self, root: AnyValueRef) -> Self {
        Self::new(self.heap.clone(), root)
    }
}

impl PartialEq for QuotedSourceRoot {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for QuotedSourceRoot {}

#[derive(Debug, Clone)]
pub struct QuotedSourceCursor {
    heap: Rc<QuotedSourceHeap>,
    root: AnyValueRef,
}

#[derive(Debug, Clone)]
pub struct QuotedAstNode {
    pub head: QuotedSourceCursor,
    pub meta: QuotedSourceCursor,
    pub tail: QuotedSourceCursor,
}

impl QuotedSourceCursor {
    pub fn root(&self) -> AnyValueRef {
        self.root
    }

    pub fn atom_name(&self) -> Result<String, QuotedSourceError> {
        let atom_id = self.root.load_atom().map_err(QuotedSourceError::from)? as u32;
        let proc = self.heap.process.borrow();
        render_atom_name(&proc, atom_id)
    }

    pub fn int_value(&self) -> Result<i64, QuotedSourceError> {
        self.root.load_int().map_err(QuotedSourceError::from)
    }

    pub fn utf8_binary_text(&self) -> Result<String, QuotedSourceError> {
        let bytes = self.root_bytes()?;
        String::from_utf8(bytes)
            .map_err(|error| QuotedSourceError::new(format!("expected valid UTF-8 bitstring: {error}")))
    }

    fn root_bytes(&self) -> Result<Vec<u8>, QuotedSourceError> {
        let heap_word = match self.root.tag() {
            ValueKind::BITSTRING | ValueKind::PROCBIN => {
                self.root.heap_object_word().map_err(QuotedSourceError::from)?
            }
            other => {
                return Err(QuotedSourceError::new(format!(
                    "expected UTF-8 bitstring-like root, got {:?}",
                    other
                )));
            }
        };
        let byte_ptr = unsafe { procbin_byte_ptr(heap_word as *const u8) };
        let bit_len = unsafe { tagged_bitstring_bit_len(heap_word as *const u8) } as usize;
        if !bit_len.is_multiple_of(8) {
            return Err(QuotedSourceError::new(format!(
                "expected whole-byte UTF-8 bitstring, got {bit_len} bits"
            )));
        }
        let byte_len = bit_len / 8;
        let bytes = unsafe { slice::from_raw_parts(byte_ptr, byte_len) };
        Ok(bytes.to_vec())
    }

    pub fn list_items(&self) -> Result<Vec<Self>, QuotedSourceError> {
        let proc = self.heap.process.borrow();
        let mut cursor = self.root;
        let mut items = Vec::new();
        loop {
            if cursor.is_empty_list() {
                break;
            }
            let head = proc.heap.read_list_head_ref(cursor).map_err(QuotedSourceError::from)?;
            let tail = proc.heap.read_list_tail_ref(cursor).map_err(QuotedSourceError::from)?;
            items.push(Self {
                heap: self.heap.clone(),
                root: head,
            });
            cursor = tail;
        }
        Ok(items)
    }

    pub fn list_atom_names(&self) -> Result<Vec<String>, QuotedSourceError> {
        self.list_items()?
            .into_iter()
            .map(|item| item.atom_name())
            .collect::<Result<Vec<_>, _>>()
    }

    pub fn tuple_items(&self) -> Result<Vec<Self>, QuotedSourceError> {
        let addr = self.root.struct_addr().map_err(QuotedSourceError::from)?;
        let schema_id = unsafe { struct_schema_id(addr as *const u8) };
        let proc = self.heap.process.borrow();
        let schema_handle = proc.heap.schemas_registry();
        let schema = schema_handle.borrow();
        let fields = schema.get(schema_id).fields.clone();
        let mut items = Vec::with_capacity(fields.len());
        for field in fields {
            if field.kind != fz_runtime::heap::FieldKind::AnyValue {
                return Err(QuotedSourceError::new(format!(
                    "quoted source tuple cannot read raw field in schema {}",
                    schema.get(schema_id).name
                )));
            }
            let value = proc
                .heap
                .read_struct_field_ref(self.root, field.offset)
                .map_err(QuotedSourceError::from)?;
            items.push(Self {
                heap: self.heap.clone(),
                root: value,
            });
        }
        Ok(items)
    }

    pub fn map_entries(&self) -> Result<Vec<(Self, Self)>, QuotedSourceError> {
        let addr = self.root.map_addr().map_err(QuotedSourceError::from)?;
        let count = unsafe { map_count(addr as *const u8) };
        let mut entries = Vec::with_capacity(count);
        for index in 0..count {
            let tag = unsafe { ptr::read(map_tag_ptr(addr as *const u8).add(index)) };
            let keys = unsafe { map_keys_ptr(addr as *const u8, count) };
            let values = unsafe { map_values_ptr(addr as *const u8, count) };
            let key = storage_ref(unsafe { keys.add(index) }, map_key_kind(tag))?;
            let value = storage_ref(unsafe { values.add(index) }, map_value_kind(tag))?;
            entries.push((
                Self {
                    heap: self.heap.clone(),
                    root: key,
                },
                Self {
                    heap: self.heap.clone(),
                    root: value,
                },
            ));
        }
        Ok(entries)
    }

    pub fn map_value(&self, key_name: &str) -> Result<Option<Self>, QuotedSourceError> {
        for (key, value) in self.map_entries()? {
            if key.root.tag() != ValueKind::ATOM {
                continue;
            }
            if key.atom_name()? == key_name {
                return Ok(Some(value));
            }
        }
        Ok(None)
    }

    pub fn ast_node(&self) -> Result<Option<QuotedAstNode>, QuotedSourceError> {
        if self.root.tag() != ValueKind::STRUCT {
            return Ok(None);
        }
        let items = self.tuple_items()?;
        if items.len() != 3 {
            return Ok(None);
        }
        Ok(Some(QuotedAstNode {
            head: items[0].clone(),
            meta: items[1].clone(),
            tail: items[2].clone(),
        }))
    }

    pub fn fingerprint(
        &self,
        policy: QuotedSourceFingerprintPolicy,
    ) -> Result<QuotedSourceFingerprint, QuotedSourceError> {
        fingerprint_root(&self.heap, self.root, policy)
    }
}

fn fingerprint_root(
    heap: &QuotedSourceHeap,
    root: AnyValueRef,
    policy: QuotedSourceFingerprintPolicy,
) -> Result<QuotedSourceFingerprint, QuotedSourceError> {
    let proc = heap.process.borrow();
    let canonical = fingerprint_value(&proc, root, policy, &mut Vec::new())?;
    Ok(QuotedSourceFingerprint {
        policy,
        digest: digest_fnv64(&canonical),
        canonical,
    })
}

fn fingerprint_value(
    proc: &Process,
    value: AnyValueRef,
    policy: QuotedSourceFingerprintPolicy,
    stack: &mut Vec<(ValueKind, usize)>,
) -> Result<String, QuotedSourceError> {
    let needs_cycle_guard = value.is_heap_root();
    if needs_cycle_guard {
        let key = (value.tag(), value.storage_addr() as usize);
        if stack.contains(&key) {
            return Err(QuotedSourceError::new("quoted source graph contains a cycle"));
        }
        stack.push(key);
    }

    let rendered = match value.tag() {
        ValueKind::NULL => "null".to_string(),
        ValueKind::INT => format!("int:{}", value.load_int().map_err(QuotedSourceError::from)?),
        ValueKind::FLOAT => format!(
            "float:{:016x}",
            value.load_float().map_err(QuotedSourceError::from)?.to_bits()
        ),
        ValueKind::ATOM => {
            let atom_id = value.load_atom().map_err(QuotedSourceError::from)? as u32;
            format!("atom:{}", render_atom_name(proc, atom_id)?)
        }
        ValueKind::LIST if value.is_empty_list() => "list[]".to_string(),
        ValueKind::LIST => {
            let mut cursor = value;
            let mut items = Vec::new();
            while !cursor.is_empty_list() {
                let head = proc.heap.read_list_head_ref(cursor).map_err(QuotedSourceError::from)?;
                let tail = proc.heap.read_list_tail_ref(cursor).map_err(QuotedSourceError::from)?;
                items.push(head);
                cursor = tail;
            }
            let mut parts = Vec::with_capacity(items.len());
            for item in items {
                parts.push(fingerprint_value(proc, item, policy, stack)?);
            }
            format!("list[{}]", parts.join(","))
        }
        ValueKind::MAP => fingerprint_map(proc, value, policy, stack)?,
        ValueKind::STRUCT => fingerprint_struct(proc, value, policy, stack)?,
        ValueKind::BITSTRING | ValueKind::PROCBIN => fingerprint_bitstring(value)?,
        other => {
            return Err(QuotedSourceError::new(format!(
                "quoted source value cannot contain runtime kind {:?}",
                other
            )));
        }
    };

    if needs_cycle_guard {
        stack.pop();
    }

    Ok(rendered)
}

fn fingerprint_map(
    proc: &Process,
    value: AnyValueRef,
    policy: QuotedSourceFingerprintPolicy,
    stack: &mut Vec<(ValueKind, usize)>,
) -> Result<String, QuotedSourceError> {
    let addr = value.map_addr().map_err(QuotedSourceError::from)?;
    let count = unsafe { map_count(addr as *const u8) };
    let mut entries = Vec::with_capacity(count);
    for index in 0..count {
        let tag = unsafe { ptr::read(map_tag_ptr(addr as *const u8).add(index)) };
        let keys = unsafe { map_keys_ptr(addr as *const u8, count) };
        let values = unsafe { map_values_ptr(addr as *const u8, count) };
        let key_ref = storage_ref(unsafe { keys.add(index) }, map_key_kind(tag))?;
        if key_ref.tag() == ValueKind::ATOM {
            let atom_id = key_ref.load_atom().map_err(QuotedSourceError::from)? as u32;
            let atom_name = render_atom_name(proc, atom_id)?;
            if !policy.includes_meta_key(&atom_name) {
                continue;
            }
        }
        let value_ref = storage_ref(unsafe { values.add(index) }, map_value_kind(tag))?;
        let key = fingerprint_value(proc, key_ref, policy, stack)?;
        let value = fingerprint_value(proc, value_ref, policy, stack)?;
        entries.push((key, value));
    }
    entries.sort();
    let mut rendered = String::from("map{");
    for (index, (key, value)) in entries.iter().enumerate() {
        if index > 0 {
            rendered.push(',');
        }
        write!(&mut rendered, "{}=>{}", key, value).expect("write to string");
    }
    rendered.push('}');
    Ok(rendered)
}

fn fingerprint_struct(
    proc: &Process,
    value: AnyValueRef,
    policy: QuotedSourceFingerprintPolicy,
    stack: &mut Vec<(ValueKind, usize)>,
) -> Result<String, QuotedSourceError> {
    let addr = value.struct_addr().map_err(QuotedSourceError::from)?;
    let schema_id = unsafe { struct_schema_id(addr as *const u8) };
    let schema_handle = proc.heap.schemas_registry();
    let schema_borrow = schema_handle.borrow();
    let schema = schema_borrow.get(schema_id).clone();

    if schema
        .fields
        .iter()
        .any(|field| field.kind != fz_runtime::heap::FieldKind::AnyValue)
    {
        return Err(QuotedSourceError::new(format!(
            "quoted source struct {} contains raw fields",
            schema.name
        )));
    }

    let mut values = Vec::with_capacity(schema.fields.len());
    for field in &schema.fields {
        let field_value = proc
            .heap
            .read_struct_field_ref(value, field.offset)
            .map_err(QuotedSourceError::from)?;
        values.push((field.name.clone(), fingerprint_value(proc, field_value, policy, stack)?));
    }

    if let Some(arity) = tuple_arity(&schema.name) {
        let rendered = values.into_iter().map(|(_, value)| value).collect::<Vec<_>>();
        return Ok(format!("tuple{}[{}]", arity, rendered.join(",")));
    }

    let mut rendered = format!("struct:{}{{", schema.name);
    for (index, (name, value)) in values.iter().enumerate() {
        if index > 0 {
            rendered.push(',');
        }
        write!(&mut rendered, "{}={}", name.as_deref().unwrap_or("_"), value).expect("write to string");
    }
    rendered.push('}');
    Ok(rendered)
}

fn fingerprint_bitstring(value: AnyValueRef) -> Result<String, QuotedSourceError> {
    let heap_word = match value.tag() {
        ValueKind::BITSTRING | ValueKind::PROCBIN => value.heap_object_word().map_err(QuotedSourceError::from)?,
        other => {
            return Err(QuotedSourceError::new(format!(
                "expected bitstring-like root, got {:?}",
                other
            )));
        }
    };
    let tagged_ptr = heap_word as *const u8;
    let byte_ptr = unsafe { procbin_byte_ptr(tagged_ptr) };
    let bit_len = unsafe { tagged_bitstring_bit_len(tagged_ptr) } as usize;
    let byte_len = bit_len.div_ceil(8);
    let bytes = unsafe { slice::from_raw_parts(byte_ptr, byte_len) };
    let mut rendered = String::from("bits:");
    for byte in bytes {
        write!(&mut rendered, "{byte:02x}").expect("write to string");
    }
    write!(&mut rendered, "/{bit_len}").expect("write to string");
    Ok(rendered)
}

fn storage_ref(raw_slot: *const u64, kind: ValueKind) -> Result<AnyValueRef, QuotedSourceError> {
    Ok(match kind {
        ValueKind::NULL => AnyValueRef::null(),
        ValueKind::LIST if unsafe { ptr::read(raw_slot) } == 0 => AnyValueRef::empty_list(),
        tag if tag.is_scalar() => AnyValueRef::from_scalar_slot(tag, raw_slot).map_err(QuotedSourceError::from)?,
        tag => AnyValueRef::from_heap_object(tag, unsafe { ptr::read(raw_slot) } as *const u8)
            .map_err(QuotedSourceError::from)?,
    })
}

fn render_atom_name(proc: &Process, atom_id: u32) -> Result<String, QuotedSourceError> {
    match atom_id {
        0 => Ok(NIL_ATOM.to_string()),
        1 => Ok(TRUE_ATOM.to_string()),
        2 => Ok(FALSE_ATOM.to_string()),
        _ => proc
            .node
            .atom_name(atom_id)
            .ok_or_else(|| QuotedSourceError::new(format!("unknown atom id {atom_id}"))),
    }
}

fn any_value_from_ref(value: AnyValueRef) -> Result<AnyValue, QuotedSourceError> {
    AnyValue::from_ref(value).map_err(QuotedSourceError::from)
}

fn digest_fnv64(text: &str) -> String {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;

    let mut hash = FNV_OFFSET;
    for byte in text.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    format!("{hash:016x}")
}

fn tuple_arity(name: &str) -> Option<usize> {
    name.strip_prefix("Tuple").and_then(|suffix| suffix.parse().ok())
}

fn map_key_cmp(left: AnyValueRef, right: AnyValueRef) -> Ordering {
    map_key_category(left)
        .cmp(&map_key_category(right))
        .then_with(|| left.tag().tag().cmp(&right.tag().tag()))
        .then_with(|| {
            if left.tag() == ValueKind::INT {
                left.load_int()
                    .expect("int key")
                    .cmp(&right.load_int().expect("int key"))
            } else {
                left.storage_raw()
                    .expect("value ref sort payload")
                    .cmp(&right.storage_raw().expect("value ref sort payload"))
            }
        })
}

fn map_key_category(value: AnyValueRef) -> u8 {
    match value.tag() {
        ValueKind::INT => 0,
        ValueKind::ATOM => 1,
        ValueKind::NULL => 2,
        ValueKind::FLOAT => 4,
        _ => 3,
    }
}
