use std::collections::HashMap;

use crate::source::Span;

use super::code::SourceOwner;
use super::drive::FactKey;
use super::identity::{FunctionId, FunctionRef, ModuleId};
use super::namespace::NamespaceSymbol;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InterfaceCallableKind {
    PublicFunction,
    Macro,
    Callable,
}

impl InterfaceCallableKind {
    pub fn namespace_symbol(self, function: FunctionId) -> NamespaceSymbol {
        match self {
            Self::PublicFunction => NamespaceSymbol::Function(function),
            Self::Macro => NamespaceSymbol::Macro(function),
            Self::Callable => NamespaceSymbol::Callable(function),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleInterfaceCallable {
    pub function: FunctionId,
    pub reference: FunctionRef,
    pub kind: InterfaceCallableKind,
    pub variadic: bool,
}

impl ModuleInterfaceCallable {
    pub fn matches_name_arity(&self, name: &str, arity: usize) -> bool {
        self.reference.name() == name && self.reference.arity == arity
    }

    pub fn namespace_symbol(&self) -> NamespaceSymbol {
        self.kind.namespace_symbol(self.function)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceRequester {
    pub owner: SourceOwner,
    pub module: ModuleId,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceExpectation {
    pub name: String,
    pub arity: usize,
    pub kind: InterfaceCallableKind,
    pub requester: Option<InterfaceRequester>,
}

impl InterfaceExpectation {
    pub fn matches_callable(&self, callable: &ModuleInterfaceCallable) -> bool {
        callable.matches_name_arity(&self.name, self.arity)
            && match self.kind {
                InterfaceCallableKind::Callable => true,
                kind => kind == callable.kind,
            }
    }
}

/// A bare module reference recorded before the module resolved -- a
/// whole-module `import`/`require` naming no particular function, so there
/// is no `(name, arity)` to hang an [`InterfaceExpectation`] on. Deliberately
/// its own store rather than a field on [`ModuleInterface`]: `ModuleInterface`
/// doubles as "is this module's interface actually known" (checked by
/// `module_interface_if_present`), so folding an obligation into it would
/// make an undefined module look resolved the moment someone referenced it.
/// This is the module-reference sibling of
/// `structdef::StructReferenceExpectation`, kept separate from `ModuleInterface`
/// for the same reason `StructReferenceExpectation` is kept separate from
/// `StructDef`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleReferenceExpectation {
    pub requester: InterfaceRequester,
}

/// Module -> outstanding bare-reference obligations, read back by
/// `World::unresolved_module_issue` so a module that never resolves still
/// names the site that asked for it.
#[derive(Debug, Default)]
pub struct ModuleReferenceExpectationMap {
    references: HashMap<ModuleId, Vec<ModuleReferenceExpectation>>,
}

impl ModuleReferenceExpectationMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Records one obligation, deduplicating identical requesters so
    /// re-scoping the same `import`/`require` site stays idempotent -- the
    /// same discipline `StructExpectationMap::record_reference` follows.
    pub fn record(&mut self, module: ModuleId, expectation: ModuleReferenceExpectation) {
        let list = self.references.entry(module).or_default();
        if !list.contains(&expectation) {
            list.push(expectation);
        }
    }

    pub fn expectations(&self, module: ModuleId) -> &[ModuleReferenceExpectation] {
        self.references.get(&module).map(Vec::as_slice).unwrap_or(&[])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReadyOrPending<T> {
    Ready(T),
    Pending { waits: Vec<FactKey> },
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ModuleInterface {
    callables: Vec<ModuleInterfaceCallable>,
    expectations: Vec<InterfaceExpectation>,
}

impl ModuleInterface {
    pub fn new(callables: Vec<ModuleInterfaceCallable>) -> Self {
        Self {
            callables,
            expectations: Vec::new(),
        }
    }

    pub fn callables(&self) -> &[ModuleInterfaceCallable] {
        &self.callables
    }

    pub fn expectations(&self) -> &[InterfaceExpectation] {
        &self.expectations
    }

    pub fn public_function_with_name_arity(&self, name: &str, arity: usize) -> Option<FunctionId> {
        self.callables
            .iter()
            .find(|callable| {
                callable.kind == InterfaceCallableKind::PublicFunction && callable.matches_name_arity(name, arity)
            })
            .map(|callable| callable.function)
    }

    pub fn macro_with_name_arity(&self, name: &str, arity: usize) -> Option<FunctionId> {
        self.callables
            .iter()
            .find(|callable| callable.kind == InterfaceCallableKind::Macro && callable.matches_name_arity(name, arity))
            .map(|callable| callable.function)
    }

    pub fn exported_functions(
        &self,
        except: Option<&[(String, usize)]>,
    ) -> ReadyOrPending<Vec<ModuleInterfaceCallable>> {
        ReadyOrPending::Ready(self.filtered_callables(InterfaceCallableKind::PublicFunction, except))
    }

    pub fn exported_macros(&self, except: Option<&[(String, usize)]>) -> ReadyOrPending<Vec<ModuleInterfaceCallable>> {
        ReadyOrPending::Ready(self.filtered_callables(InterfaceCallableKind::Macro, except))
    }

    pub fn record_expectation(&mut self, expectation: InterfaceExpectation) {
        if self.expectations.contains(&expectation) {
            return;
        }
        self.expectations.push(expectation);
    }

    pub fn inherit_expectations_from(&mut self, prior: &ModuleInterface) {
        for expectation in prior.expectations() {
            self.record_expectation(expectation.clone());
        }
    }

    fn filtered_callables(
        &self,
        kind: InterfaceCallableKind,
        except: Option<&[(String, usize)]>,
    ) -> Vec<ModuleInterfaceCallable> {
        self.callables
            .iter()
            .filter(|callable| callable.kind == kind)
            .filter(|callable| {
                except.is_none_or(|except| {
                    !except
                        .iter()
                        .any(|(name, arity)| callable.matches_name_arity(name, *arity))
                })
            })
            .cloned()
            .collect()
    }
}

#[cfg(test)]
#[path = "module_interface_test.rs"]
mod module_interface_test;
