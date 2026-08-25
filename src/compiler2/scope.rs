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
}

impl ScopeSnapshot {
    pub fn module(module: ModuleId, namespace: Namespace) -> Self {
        Self {
            module,
            namespace,
            function: None,
        }
    }

    pub fn function(module: ModuleId, namespace: Namespace, function: FunctionId) -> Self {
        Self {
            module,
            namespace,
            function: Some(function),
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
        }
    }

    pub fn in_function(self, function: FunctionId) -> Self {
        Self {
            function: Some(function),
            ..self
        }
    }
}
