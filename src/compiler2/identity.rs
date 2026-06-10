use std::collections::{BTreeMap, HashMap};

use crate::compiler::source::Span;
use crate::function_surface::FunctionSurface;

use super::code::CodeId;
use super::namespace::{Namespace, NamespaceSymbol};
use super::quoted_surface::{ScopeForm, ScopeSurface};
use super::source::{Horizon, QuotedSourceRoot};
use super::type_expr::TypeDefBody;
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
}

#[derive(Debug, Clone)]
pub struct Module {
    pub(crate) state: ModuleState,
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
    pub source: QuotedSourceRoot,
    pub kind: ModuleSourceKind,
}

#[derive(Debug, Clone)]
pub enum ModuleSourceKind {
    Body(ScopeSurface),
    Protocol(ScopeSurface),
}

impl ModuleSource {
    fn empty(code: CodeId) -> Self {
        Self {
            code,
            parent: ModuleId::GLOBAL,
            local_name: String::new(),
            source: QuotedSourceRoot::empty(),
            kind: ModuleSourceKind::Body(ScopeSurface {
                attrs: Vec::new(),
                forms: Vec::new(),
            }),
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
    pub variadic: bool,
    pub symbol: NamespaceSymbol,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub state: FunctionState,
}

impl Function {
    pub fn state_source_heap_id(&self) -> Option<usize> {
        match &self.state {
            FunctionState::Placeholder => None,
            FunctionState::Defined { def } => Some(def.source.key().heap_id),
        }
    }

    pub fn state_source_root_word(&self) -> Option<u64> {
        match &self.state {
            FunctionState::Placeholder => None,
            FunctionState::Defined { def } => Some(def.source.root().raw_word()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum FunctionState {
    Placeholder,
    Defined { def: Box<FunctionDef> },
}

#[derive(Debug, Clone)]
pub struct FunctionSourceSlot {
    pub state: FunctionSourceState,
}

#[derive(Debug, Clone)]
pub enum FunctionSourceState {
    Placeholder,
    Noted { source: Box<FunctionSource> },
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub code: CodeId,
    pub owner_module: ModuleId,
    pub namespace: Namespace,
    pub capture_params: Vec<String>,
    pub source: QuotedSourceRoot,
    pub(crate) surface: FunctionSurface,
}

#[derive(Debug, Clone)]
pub struct FunctionSource {
    pub code: CodeId,
    pub owner_module: ModuleId,
    pub namespace: Namespace,
    pub capture_params: Vec<String>,
    pub variadic: bool,
    pub source: QuotedSourceRoot,
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

/// The identity of a named type: its owning module, source name, and arity.
///
/// Keying on the owning `ModuleId` (not a dotted string) means `t` resolved
/// inside `SomeModule` and `SomeModule.t` resolved from outside land on one
/// identity, and a module alias never changes it. `t/0` and `t/1` are distinct.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeName {
    pub module: ModuleId,
    pub name: String,
    pub arity: usize,
}

/// A `@type` declaration as noted during scoping: its formal parameters, its
/// parsed-but-unresolved body, and the namespace in scope where it appeared.
///
/// `DeriveTypeDef` (fz-rh2.12.2) reads this to resolve the body to a hard `Ty`
/// against the captured namespace — the namespace, not a `ModuleTypeEnv`, is
/// the resolution context.
#[derive(Debug, Clone)]
pub struct NotedTypeDecl {
    pub params: Vec<String>,
    pub body: TypeDefBody,
    pub namespace: Namespace,
    pub span: Span,
}

#[derive(Debug, Default)]
pub struct ModuleMap {
    slots: Vec<Module>,
    names: Vec<Option<String>>,
    by_name: HashMap<String, ModuleId>,
}

#[derive(Debug, Default)]
pub struct FunctionSourceMap {
    slots: Vec<FunctionSourceSlot>,
}

impl FunctionSourceMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn note(&mut self, id: FunctionId, source: FunctionSource, current_revision: u64) -> u64 {
        self.ensure_slot(id);
        let slot = &mut self.slots[id.0 as usize];
        let next = FunctionSourceState::Noted {
            source: Box::new(source),
        };
        update_if_changed(&mut slot.state, current_revision, next)
    }

    pub fn get(&self, id: FunctionId) -> Option<&FunctionSourceSlot> {
        self.slots.get(id.0 as usize)
    }

    fn ensure_slot(&mut self, id: FunctionId) {
        let needed = id.0 as usize + 1;
        if self.slots.len() >= needed {
            return;
        }
        self.slots.resize_with(needed, || FunctionSourceSlot {
            state: FunctionSourceState::Placeholder,
        });
    }
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
        });
        self.names.push(Some(name.clone()));
        self.by_name.insert(name, id);
        id
    }

    pub fn define(
        &mut self,
        id: ModuleId,
        code: CodeId,
        namespace: Namespace,
        exports: Vec<ModuleExport>,
        current_revision: u64,
    ) -> u64 {
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
        update_if_changed(&mut module.state, current_revision, next)
    }

    pub fn scope(&mut self, id: ModuleId, base_namespace: Namespace, current_revision: u64) -> u64 {
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
        update_if_changed(&mut module.state, current_revision, next)
    }

    pub fn index_body(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        source: QuotedSourceRoot,
        surface: ScopeSurface,
        current_revision: u64,
    ) -> u64 {
        let module = &mut self.slots[id.0 as usize];
        let next = ModuleState::Indexed(ModuleSource {
            code,
            parent,
            local_name,
            source,
            kind: ModuleSourceKind::Body(surface),
        });
        update_if_changed(&mut module.state, current_revision, next)
    }

    pub fn index_protocol(
        &mut self,
        id: ModuleId,
        code: CodeId,
        parent: ModuleId,
        local_name: String,
        source: QuotedSourceRoot,
        surface: ScopeSurface,
        current_revision: u64,
    ) -> u64 {
        let module = &mut self.slots[id.0 as usize];
        let next = ModuleState::Indexed(ModuleSource {
            code,
            parent,
            local_name,
            source,
            kind: ModuleSourceKind::Protocol(surface),
        });
        update_if_changed(&mut module.state, current_revision, next)
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

    pub fn named_struct_schemas(&self) -> BTreeMap<String, Vec<String>> {
        let mut out = BTreeMap::new();
        for (index, name) in self.names.iter().enumerate() {
            let Some(name) = name else {
                continue;
            };
            let module = &self.slots[index];
            let Some(fields) = (match &module.state {
                ModuleState::Placeholder => None,
                ModuleState::Indexed(source)
                | ModuleState::Scoped { source, .. }
                | ModuleState::Defined { source, .. } => match &source.kind {
                    ModuleSourceKind::Body(surface) => surface.forms.iter().find_map(|form| match form {
                        ScopeForm::Struct(def) => Some(def.fields.clone()),
                        _ => None,
                    }),
                    ModuleSourceKind::Protocol(_) => None,
                },
            }) else {
                continue;
            };
            out.insert(name.clone(), fields);
        }
        out
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
        });
        self.refs.push(FunctionRef {
            module,
            name: format!("#lambda:{}:{}-{}", owner.as_u32(), span.start, span.end),
            arity,
        });
        self.generated_by_key.insert(key, id);
        id
    }

    pub fn define(&mut self, id: FunctionId, def: FunctionDef, current_revision: u64) -> u64 {
        let function = &mut self.slots[id.0 as usize];
        let next = FunctionState::Defined { def: Box::new(def) };
        update_if_changed(&mut function.state, current_revision, next)
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

/// The noted `@type` declarations, keyed by [`TypeName`]. Populated while
/// scoping (fz-rh2.12.1) and read by `DeriveTypeDef` (fz-rh2.12.2). A type is
/// an identity that may be referenced before — or without ever — being
/// declared, so a missing entry is an unresolved-frontier question, not a
/// panic.
#[derive(Debug, Default)]
pub struct TypeDeclMap {
    decls: HashMap<TypeName, NotedTypeDecl>,
}

impl TypeDeclMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn note(&mut self, name: TypeName, decl: NotedTypeDecl) {
        self.decls.insert(name, decl);
    }

    pub fn get(&self, name: &TypeName) -> Option<&NotedTypeDecl> {
        self.decls.get(name)
    }
}

/// The type names each consumer references, recorded by the reference walk
/// (fz-rh2.12.12). A function (its `@spec`/extern) and a `@type` body each gain
/// a dependency list — the exact set of `TypeDefined` facts that consumer waits
/// on before it resolves (fz-rh2.12.2/.4). Recorded at index, never resolved.
#[derive(Debug, Default)]
pub struct TypeRefMap {
    by_function: HashMap<FunctionId, Vec<TypeName>>,
    by_type: HashMap<TypeName, Vec<TypeName>>,
}

impl TypeRefMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record_function(&mut self, function: FunctionId, refs: Vec<TypeName>) {
        self.by_function.insert(function, refs);
    }

    // Consumed by the contract re-seat (fz-rh2.12.4); recorded one inch ahead.
    #[allow(dead_code)]
    pub fn function_refs(&self, function: FunctionId) -> &[TypeName] {
        self.by_function.get(&function).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn record_type(&mut self, name: TypeName, refs: Vec<TypeName>) {
        self.by_type.insert(name, refs);
    }

    // Consumed by DeriveTypeDef (fz-rh2.12.2); recorded one inch ahead.
    #[allow(dead_code)]
    pub fn type_refs(&self, name: &TypeName) -> &[TypeName] {
        self.by_type.get(name).map(Vec::as_slice).unwrap_or(&[])
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
        self.slots.push(Root { entry });
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

/// Reconciles a fact's value when it is (re)produced. `current` is `None`
/// until the fact is first computed — distinct from any value, so fixpoint
/// facts never mistake "not yet known" for a result. The returned `u64` is
/// whatever the fact chooses to mean by "version" (here, a monotonic bump on
/// change); the value itself never carries the revision — the fact system
/// holds and threads it.
trait Reconcile: Sized {
    fn reconcile(current: Option<&Self>, incoming: Self, revision: u64) -> (Self, u64);
}

/// The monotonic reconcile policy: keep the revision when `same` holds against
/// the current value, otherwise bump it. `same` is evaluated before `incoming`
/// is moved into the result.
fn monotonic<T>(current: Option<&T>, incoming: T, revision: u64, same: impl Fn(&T, &T) -> bool) -> (T, u64) {
    let unchanged = current.is_some_and(|current| same(current, &incoming));
    let revision = if unchanged { revision } else { revision + 1 };
    (incoming, revision)
}

fn update_if_changed<T: Reconcile>(state: &mut T, current_revision: u64, next: T) -> u64 {
    let (value, new_revision) = T::reconcile(Some(state), next, current_revision);
    // Always store the fresh value; advance the revision only when the fact's
    // horizon deems it changed. A module's body-only edit keeps its revision put
    // but still refreshes the stored source for the per-function facts that
    // re-derive from it.
    *state = value;
    new_revision
}

impl Reconcile for ModuleState {
    fn reconcile(current: Option<&Self>, incoming: Self, revision: u64) -> (Self, u64) {
        monotonic(current, incoming, revision, ModuleState::same)
    }
}

impl ModuleState {
    fn same(&self, other: &Self) -> bool {
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
            && self.source.semantically_eq(&other.source, Horizon::Surface)
    }
}

impl Reconcile for FunctionState {
    fn reconcile(current: Option<&Self>, incoming: Self, revision: u64) -> (Self, u64) {
        monotonic(current, incoming, revision, FunctionState::same)
    }
}

impl FunctionState {
    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (FunctionState::Placeholder, FunctionState::Placeholder) => true,
            (FunctionState::Defined { def: left }, FunctionState::Defined { def: right }) => {
                left.code == right.code
                    && left.owner_module == right.owner_module
                    && left.namespace == right.namespace
                    && left.capture_params == right.capture_params
                    && left.source.semantically_eq(&right.source, Horizon::Full)
            }
            _ => false,
        }
    }
}

impl Reconcile for FunctionSourceState {
    fn reconcile(current: Option<&Self>, incoming: Self, revision: u64) -> (Self, u64) {
        monotonic(current, incoming, revision, FunctionSourceState::same)
    }
}

impl FunctionSourceState {
    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (FunctionSourceState::Placeholder, FunctionSourceState::Placeholder) => true,
            (FunctionSourceState::Noted { source: left }, FunctionSourceState::Noted { source: right }) => {
                left.code == right.code
                    && left.owner_module == right.owner_module
                    && left.namespace == right.namespace
                    && left.capture_params == right.capture_params
                    && left.variadic == right.variadic
                    && left.source.semantically_eq(&right.source, Horizon::Full)
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod reconcile_test {
    use super::monotonic;

    // The reconcile contract: the stored value is always the incoming one
    // (fresh content is never dropped), and the revision advances iff the new
    // value differs from the current — where `None` ("not yet computed") always
    // counts as a difference.
    #[test]
    fn monotonic_advances_only_when_the_value_changes() {
        let eq = |a: &u32, b: &u32| a == b;
        assert_eq!(monotonic(None, 5, 10, eq), (5, 11), "first computation advances");
        assert_eq!(
            monotonic(Some(&5), 5, 10, eq),
            (5, 10),
            "an unchanged value keeps the revision"
        );
        assert_eq!(
            monotonic(Some(&5), 7, 10, eq),
            (7, 11),
            "a change advances and stores the incoming value"
        );
    }
}
