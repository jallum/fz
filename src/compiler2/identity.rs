use std::collections::HashMap;

use std::rc::Rc;

use crate::ast::{Attribute, FnDef, Item, ProtocolCallback as ProtocolCallbackDef};
use crate::compiler::source::Span;

use super::code::CodeId;
use super::namespace::{Namespace, NamespaceSymbol};
use super::types::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u32);

impl ModuleId {
    pub const GLOBAL: Self = Self(0);

    pub fn from_u32(value: u32) -> Self {
        Self(value)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn is_global(self) -> bool {
        self == Self::GLOBAL
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionId(u32);

impl FunctionId {
    pub fn from_u32(value: u32) -> Self {
        Self(value)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RootId(u32);

impl RootId {
    pub fn from_u32(value: u32) -> Self {
        Self(value)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ActivationKey {
    pub root: RootId,
    pub function: FunctionId,
    pub input: Vec<Ty>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExecutableNeed {
    Value,
    TupleFields(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExecutableKey {
    pub activation: ActivationKey,
    pub need: ExecutableNeed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RootEntry {
    pub function: FunctionId,
    pub need: ExecutableNeed,
}

#[derive(Debug, Clone)]
pub struct Root {
    pub entry: RootEntry,
    pub revision: u64,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub(crate) state: ModuleState,
    pub(crate) revision: u64,
}

impl Module {
    fn source(&self) -> Option<&ModuleSource> {
        match &self.state {
            ModuleState::Placeholder => None,
            ModuleState::Indexed(source) | ModuleState::Scoped { source, .. } | ModuleState::Defined { source, .. } => {
                Some(source)
            }
        }
    }

    fn base_namespace(&self) -> Option<Namespace> {
        match &self.state {
            ModuleState::Scoped { base, .. } => Some(*base),
            ModuleState::Defined { surface, .. } => Some(surface.base),
            _ => None,
        }
    }

    fn codes(&self) -> Option<Vec<CodeId>> {
        match &self.state {
            ModuleState::Defined { surface, .. } => Some(surface.codes.clone()),
            ModuleState::Indexed(source) | ModuleState::Scoped { source, .. } => Some(vec![source.code]),
            ModuleState::Placeholder => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum ModuleState {
    Placeholder,
    Indexed(ModuleSource),
    Scoped {
        source: ModuleSource,
        base: Namespace,
    },
    Defined {
        source: ModuleSource,
        surface: ModuleSurface,
    },
}

#[derive(Debug, Clone)]
pub struct ModuleSource {
    pub code: CodeId,
    pub parent: ModuleId,
    pub local_name: String,
    pub attrs: Vec<Attribute>,
    pub kind: ModuleSourceKind,
}

#[derive(Debug, Clone)]
pub enum ModuleSourceKind {
    Body { items: Vec<Rc<Item>> },
    Protocol { callbacks: Vec<ProtocolCallbackDef> },
}

impl ModuleSource {
    fn empty(code: CodeId) -> Self {
        Self {
            code,
            parent: ModuleId::GLOBAL,
            local_name: String::new(),
            attrs: Vec::new(),
            kind: ModuleSourceKind::Body { items: Vec::new() },
        }
    }

    pub fn items(&self) -> Option<&[Rc<Item>]> {
        match &self.kind {
            ModuleSourceKind::Body { items } => Some(items.as_slice()),
            ModuleSourceKind::Protocol { .. } => None,
        }
    }

    pub fn callbacks(&self) -> Option<&[ProtocolCallbackDef]> {
        match &self.kind {
            ModuleSourceKind::Body { .. } => None,
            ModuleSourceKind::Protocol { callbacks } => Some(callbacks.as_slice()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleSurface {
    pub codes: Vec<CodeId>,
    pub base: Namespace,
    pub namespace: Namespace,
    pub exports: Vec<ModuleExport>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleExport {
    pub name: String,
    pub arity: usize,
    pub symbol: NamespaceSymbol,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub state: FunctionState,
    pub revision: u64,
}

#[derive(Debug, Clone)]
pub enum FunctionState {
    Placeholder,
    Defined { def: Box<FunctionDef> },
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub code: CodeId,
    pub owner_module: ModuleId,
    pub namespace: Namespace,
    pub capture_params: Vec<String>,
    pub ast: FnDef,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionKey {
    module: ModuleId,
    name: String,
    arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct GeneratedFunctionKey {
    owner: FunctionId,
    span: Span,
    arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionRef {
    pub module: ModuleId,
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Default)]
pub struct ModuleMap {
    slots: Vec<Module>,
    names: Vec<Option<String>>,
    by_name: HashMap<String, ModuleId>,
}

impl ModuleMap {
    pub fn new() -> Self {
        Self {
            slots: vec![Module {
                state: ModuleState::Defined {
                    source: ModuleSource::empty(CodeId::ZERO),
                    surface: ModuleSurface {
                        codes: Vec::new(),
                        base: Namespace::default(),
                        namespace: Namespace::default(),
                        exports: Vec::new(),
                    },
                },
                revision: 0,
            }],
            names: vec![None],
            by_name: HashMap::new(),
        }
    }

    pub fn reference_named(&mut self, name: impl Into<String>) -> ModuleId {
        let name = name.into();
        if let Some(id) = self.by_name.get(&name) {
            return *id;
        }
        let id = ModuleId(self.slots.len() as u32);
        self.slots.push(Module {
            state: ModuleState::Placeholder,
            revision: 0,
        });
        self.names.push(Some(name.clone()));
        self.by_name.insert(name, id);
        id
    }

    pub fn define(&mut self, id: ModuleId, code: CodeId, namespace: Namespace, exports: Vec<ModuleExport>) -> u64 {
        let module = &mut self.slots[id.0 as usize];
        let source = module.source().cloned().unwrap_or_else(|| ModuleSource::empty(code));
        let mut codes = module.codes().unwrap_or_else(|| vec![source.code]);
        if !codes.contains(&code) {
            codes.push(code);
        }
        let next = ModuleState::Defined {
            source,
            surface: ModuleSurface {
                codes,
                base: module.base_namespace().unwrap_or(namespace),
                namespace,
                exports,
            },
        };
        replace_if_changed(&mut module.state, &mut module.revision, next)
    }

    pub fn scope(&mut self, id: ModuleId, base_namespace: Namespace) -> u64 {
        let module = self
            .slots
            .get_mut(id.0 as usize)
            .expect("module ids should be known before scoping modules");
        let source = module
            .source()
            .expect("modules should be indexed before scoping")
            .clone();
        let next = if let ModuleState::Defined { surface, .. } = &module.state {
            let mut surface = surface.clone();
            surface.base = base_namespace;
            ModuleState::Defined { source, surface }
        } else {
            ModuleState::Scoped {
                source,
                base: base_namespace,
            }
        };
        replace_if_changed(&mut module.state, &mut module.revision, next)
    }

    pub fn index_body(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        attrs: Vec<Attribute>,
        items: Vec<Rc<Item>>,
    ) -> u64 {
        let module = &mut self.slots[id.0 as usize];
        let next = ModuleState::Indexed(ModuleSource {
            code,
            parent,
            local_name,
            attrs,
            kind: ModuleSourceKind::Body { items },
        });
        replace_if_changed(&mut module.state, &mut module.revision, next)
    }

    pub fn index_protocol(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        attrs: Vec<Attribute>,
        callbacks: Vec<ProtocolCallbackDef>,
    ) -> u64 {
        let module = &mut self.slots[id.0 as usize];
        let next = ModuleState::Indexed(ModuleSource {
            code,
            parent,
            local_name,
            attrs,
            kind: ModuleSourceKind::Protocol { callbacks },
        });
        replace_if_changed(&mut module.state, &mut module.revision, next)
    }

    pub fn define_anonymous(&mut self, code: CodeId, namespace: Namespace) -> ModuleId {
        let id = ModuleId(self.slots.len() as u32);
        self.slots.push(Module {
            state: ModuleState::Defined {
                source: ModuleSource::empty(code),
                surface: ModuleSurface {
                    codes: vec![code],
                    base: namespace,
                    namespace,
                    exports: Vec::new(),
                },
            },
            revision: 1,
        });
        self.names.push(None);
        id
    }

    pub fn get(&self, id: ModuleId) -> &Module {
        self.slots
            .get(id.0 as usize)
            .expect("module ids should be known before reading module slots")
    }

    pub fn name(&self, id: ModuleId) -> Option<&str> {
        self.names
            .get(id.0 as usize)
            .expect("module ids should be known before reading module names")
            .as_deref()
    }
}

#[derive(Debug, Default)]
pub struct FunctionMap {
    slots: Vec<Function>,
    refs: Vec<FunctionRef>,
    by_key: HashMap<FunctionKey, FunctionId>,
    generated_by_key: HashMap<GeneratedFunctionKey, FunctionId>,
}

impl FunctionMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reference(&mut self, module: ModuleId, name: impl Into<String>, arity: usize) -> FunctionId {
        let name = name.into();
        let key = FunctionKey {
            module,
            name: name.clone(),
            arity,
        };
        if let Some(id) = self.by_key.get(&key) {
            return *id;
        }
        let id = FunctionId(self.slots.len() as u32);
        self.slots.push(Function {
            state: FunctionState::Placeholder,
            revision: 0,
        });
        self.refs.push(FunctionRef { module, name, arity });
        self.by_key.insert(key, id);
        id
    }

    pub fn reference_generated(&mut self, owner: FunctionId, module: ModuleId, span: Span, arity: usize) -> FunctionId {
        let key = GeneratedFunctionKey { owner, span, arity };
        if let Some(id) = self.generated_by_key.get(&key) {
            return *id;
        }
        let id = FunctionId(self.slots.len() as u32);
        self.slots.push(Function {
            state: FunctionState::Placeholder,
            revision: 0,
        });
        self.refs.push(FunctionRef {
            module,
            name: format!("#lambda:{}:{}-{}", owner.as_u32(), span.start, span.end),
            arity,
        });
        self.generated_by_key.insert(key, id);
        id
    }

    pub fn define(&mut self, id: FunctionId, def: FunctionDef) -> u64 {
        let function = &mut self.slots[id.0 as usize];
        let next = FunctionState::Defined { def: Box::new(def) };
        replace_if_changed(&mut function.state, &mut function.revision, next)
    }

    pub fn get(&self, id: FunctionId) -> &Function {
        self.slots
            .get(id.0 as usize)
            .expect("function ids should be known before reading function slots")
    }

    pub fn reference_for(&self, id: FunctionId) -> &FunctionRef {
        self.refs
            .get(id.0 as usize)
            .expect("function ids should be known before reading reverse references")
    }
}

#[derive(Debug, Default)]
pub struct RootMap {
    slots: Vec<Root>,
}

impl RootMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, entry: RootEntry) -> RootId {
        let id = RootId(self.slots.len() as u32);
        self.slots.push(Root { entry, revision: 1 });
        id
    }

    pub fn get(&self, id: RootId) -> &Root {
        self.slots
            .get(id.0 as usize)
            .expect("root ids should be known before reading root slots")
    }
    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

trait SameState {
    fn same_state(&self, other: &Self) -> bool;
}

fn replace_if_changed<T: SameState>(state: &mut T, revision: &mut u64, next: T) -> u64 {
    if !state.same_state(&next) {
        *state = next;
        *revision += 1;
    }
    *revision
}

impl SameState for ModuleState {
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (ModuleState::Placeholder, ModuleState::Placeholder) => true,
            (ModuleState::Indexed(left), ModuleState::Indexed(right)) => left.same_source(right),
            (
                ModuleState::Scoped {
                    source: left_source,
                    base: left_base,
                },
                ModuleState::Scoped {
                    source: right_source,
                    base: right_base,
                },
            ) => left_source.same_source(right_source) && left_base == right_base,
            (
                ModuleState::Defined {
                    source: left_source,
                    surface: left_surface,
                },
                ModuleState::Defined {
                    source: right_source,
                    surface: right_surface,
                },
            ) => left_source.same_source(right_source) && left_surface == right_surface,
            _ => false,
        }
    }
}

impl ModuleSource {
    fn same_source(&self, other: &Self) -> bool {
        self.code == other.code
            && self.parent == other.parent
            && self.local_name == other.local_name
            && self.kind.same_kind(&other.kind)
    }
}

fn same_items(left: &[Rc<Item>], right: &[Rc<Item>]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(left, right)| Rc::ptr_eq(left, right))
}

impl ModuleSourceKind {
    fn same_kind(&self, other: &Self) -> bool {
        match (self, other) {
            (ModuleSourceKind::Body { items: left }, ModuleSourceKind::Body { items: right }) => {
                same_items(left, right)
            }
            (ModuleSourceKind::Protocol { callbacks: left }, ModuleSourceKind::Protocol { callbacks: right }) => {
                left.len() == right.len()
                    && left.iter().zip(right).all(|(left, right)| {
                        left.name == right.name && left.arity == right.arity && left.span == right.span
                    })
            }
            _ => false,
        }
    }
}

impl SameState for FunctionState {
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (FunctionState::Placeholder, FunctionState::Placeholder) => true,
            (FunctionState::Defined { def: left }, FunctionState::Defined { def: right }) => {
                left.code == right.code
                    && left.owner_module == right.owner_module
                    && left.namespace == right.namespace
                    && left.capture_params == right.capture_params
            }
            _ => false,
        }
    }
}
