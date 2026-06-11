use crate::compiler::source::Span;

use super::code::CodeId;
use super::drive::FactKey;
use super::identity::{FunctionId, FunctionRef, ModuleId};
use super::namespace::NamespaceSymbol;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InterfaceCallableKind {
    PublicFunction,
    Macro,
}

impl InterfaceCallableKind {
    pub fn namespace_symbol(self, function: FunctionId) -> NamespaceSymbol {
        match self {
            Self::PublicFunction => NamespaceSymbol::Function(function),
            Self::Macro => NamespaceSymbol::Macro(function),
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
        self.reference.name == name && self.reference.arity == arity
    }

    pub fn namespace_symbol(&self) -> NamespaceSymbol {
        self.kind.namespace_symbol(self.function)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceRequester {
    pub code: CodeId,
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
        self.kind == callable.kind && callable.matches_name_arity(&self.name, self.arity)
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
mod tests {
    use super::*;

    fn callable(id: u32, name: &str, arity: usize, kind: InterfaceCallableKind) -> ModuleInterfaceCallable {
        ModuleInterfaceCallable {
            function: FunctionId::from_fn_id(crate::fz_ir::FnId(id)),
            reference: FunctionRef {
                module: ModuleId::GLOBAL,
                name: name.to_string(),
                arity,
            },
            kind,
            variadic: false,
        }
    }

    #[test]
    fn module_interface_queries_by_callable_kind() {
        let interface = ModuleInterface::new(vec![
            callable(1, "add", 2, InterfaceCallableKind::PublicFunction),
            callable(2, "defthing", 1, InterfaceCallableKind::Macro),
        ]);

        assert_eq!(
            interface.public_function_with_name_arity("add", 2),
            Some(FunctionId::from_fn_id(crate::fz_ir::FnId(1)))
        );
        assert_eq!(
            interface.macro_with_name_arity("defthing", 1),
            Some(FunctionId::from_fn_id(crate::fz_ir::FnId(2)))
        );
        assert_eq!(interface.public_function_with_name_arity("defthing", 1), None);
        assert_eq!(interface.macro_with_name_arity("add", 2), None);
    }

    #[test]
    fn module_interface_filters_export_sets_by_kind_and_except() {
        let interface = ModuleInterface::new(vec![
            callable(1, "add", 2, InterfaceCallableKind::PublicFunction),
            callable(2, "sub", 2, InterfaceCallableKind::PublicFunction),
            callable(3, "defthing", 1, InterfaceCallableKind::Macro),
        ]);

        let ReadyOrPending::Ready(functions) = interface.exported_functions(Some(&[("sub".to_string(), 2)])) else {
            panic!("defined interfaces should return ready callable sets");
        };
        assert_eq!(functions.len(), 1);
        assert!(functions[0].matches_name_arity("add", 2));

        let ReadyOrPending::Ready(macros) = interface.exported_macros(None) else {
            panic!("defined interfaces should return ready callable sets");
        };
        assert_eq!(macros.len(), 1);
        assert!(macros[0].matches_name_arity("defthing", 1));
    }

    #[test]
    fn module_interface_expectations_preserve_requested_kind() {
        let mut interface = ModuleInterface::default();
        interface.record_expectation(InterfaceExpectation {
            name: "add".to_string(),
            arity: 2,
            kind: InterfaceCallableKind::PublicFunction,
            requester: Some(InterfaceRequester {
                code: CodeId::ZERO,
                module: ModuleId::GLOBAL,
                span: Span::DUMMY,
            }),
        });
        interface.record_expectation(InterfaceExpectation {
            name: "add".to_string(),
            arity: 2,
            kind: InterfaceCallableKind::Macro,
            requester: Some(InterfaceRequester {
                code: CodeId::ZERO,
                module: ModuleId::GLOBAL,
                span: Span::DUMMY,
            }),
        });

        assert_eq!(interface.expectations().len(), 2);
        assert_ne!(interface.expectations()[0].kind, interface.expectations()[1].kind);
    }
}
