use super::identity::{FunctionId, ModuleId};
use super::namespace::Namespace;

/// One immutable compiler2 scope snapshot.
///
/// `Namespace` answers ordinary name resolution. `ScopeSnapshot` wraps that
/// resolution head with the current module/function identity so compiler
/// variables and lexical metadata can be projected without inventing a second
/// mutable env authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeSnapshot {
    module: ModuleId,
    namespace: Namespace,
    function: Option<FunctionId>,
    /// Set inside a function body: the namespace the definition captured,
    /// which the body's own `alias`, `import` and `require` move forward from.
    body_origin: Option<Namespace>,
}

impl ScopeSnapshot {
    pub fn module(module: ModuleId, namespace: Namespace) -> Self {
        Self {
            module,
            namespace,
            function: None,
            body_origin: None,
        }
    }

    pub fn function(module: ModuleId, namespace: Namespace, function: FunctionId) -> Self {
        Self {
            module,
            namespace,
            function: Some(function),
            body_origin: None,
        }
    }

    pub fn module_id(self) -> ModuleId {
        self.module
    }

    pub fn namespace(self) -> Namespace {
        self.namespace
    }

    pub fn function_id(self) -> Option<FunctionId> {
        self.function
    }

    pub fn with_namespace(self, namespace: Namespace) -> Self {
        Self { namespace, ..self }
    }

    pub fn in_module(self, module: ModuleId) -> Self {
        Self {
            module,
            namespace: self.namespace,
            function: None,
            body_origin: None,
        }
    }

    /// This scope as the start of a function body: what the body binds stands
    /// apart from what the definition captured.
    pub fn in_body(self) -> Self {
        Self {
            body_origin: self.body_origin.or(Some(self.namespace)),
            ..self
        }
    }

    pub fn is_body(self) -> bool {
        self.body_origin.is_some()
    }

    /// The namespace the definition captured, when this scope is a body's.
    pub fn body_origin(self) -> Option<Namespace> {
        self.body_origin
    }

    /// Whether the body's own `alias`, `import` or `require` has moved this
    /// scope past the definition's.
    pub fn is_rebound(self) -> bool {
        self.body_origin.is_some_and(|origin| origin != self.namespace)
    }

    pub fn in_function(self, function: FunctionId) -> Self {
        Self {
            function: Some(function),
            ..self
        }
    }
}
