//! `alias`, `import` and `require`: the three forms that move a lexical scope
//! forward. A module body applies them to the namespace its definitions
//! capture, and a function body applies them to the namespace of the rest of
//! its block. One implementation serves both, so the two scopes cannot
//! disagree about what an import brings in.

use crate::diag::{Diagnostic, codes};
use crate::modules::identity::ModuleName;
use crate::source::Span;

use super::code::SourceOwner;
use super::drive::{FactKey, JobEffects, emit_job_diagnostic};
use super::identity::{FunctionId, ModuleId};
use super::module_interface::{InterfaceCallableKind, InterfaceRequester, ModuleInterfaceCallable};
use super::namespace::{Namespace, NamespaceSymbol};
use super::quoted_expander::DirectedScope;
use super::quoted_surface::{AliasForm, CallableKind, ImportForm, ImportSelection, ScopeForm};
use super::scope::ScopeSnapshot;
use super::world::World;
use fz_engine::FatalError;

/// A scope form being applied to a namespace, with the world it reads and the
/// place it stands: the module whose scope it is, and the source it came from.
pub(crate) struct ScopeDirective<'a, T: crate::telemetry::Telemetry> {
    pub world: &'a mut World,
    pub telemetry: &'a T,
    pub current_module: ModuleId,
    pub source_owner: SourceOwner,
    /// The facts the application depends on.
    pub reads: &'a mut Vec<FactKey>,
    /// The namespace the form applies to, and after `apply` the namespace it
    /// leaves.
    pub namespace: Namespace,
}

impl<T: crate::telemetry::Telemetry> ScopeDirective<'_, T> {
    /// Applies an `alias`, `import` or `require`. A module whose interface is
    /// not yet published blocks the application, and the effects say what to
    /// wait on.
    pub(crate) fn apply(&mut self, form: &ScopeForm) -> Result<Option<JobEffects>, FatalError> {
        match form {
            ScopeForm::Alias(alias) => {
                self.apply_alias(alias);
                Ok(None)
            }
            ScopeForm::Import(import) => self.apply_import(import),
            ScopeForm::Require(import) => self.apply_require(import),
            _ => unreachable!("only alias, import and require are scope directives"),
        }
    }

    fn apply_alias(&mut self, alias: &AliasForm) {
        for binding in &alias.bindings {
            let module = self
                .world
                .reference_module(ModuleName::from_segments(binding.path.clone()));
            self.bind_module_name(&binding.as_name, module);
        }
    }

    fn bind_module_name(&mut self, name: &str, module: ModuleId) {
        self.namespace = self
            .world
            .bind_namespace(self.namespace, name.to_string(), NamespaceSymbol::Module(module));
    }

    fn apply_require(&mut self, import: &ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let required_module = self.start(import)?;
        self.bind_required_module_path(import, required_module);
        if let Some(name) = &import.as_name {
            self.bind_module_name(name, required_module);
        }
        self.namespace = self.world.bind_required_module(self.namespace, required_module);
        let macros = if self.world.module_interface_revision(required_module).is_some() {
            self.reads.push(FactKey::ModuleInterface(required_module));
            let callables = self.world.module_interface(required_module).callables().to_vec();
            self.selected_macros(import, &callables)?
        } else if let Some(ImportSelection::Listed(only)) = import.only.as_ref() {
            self.referenced_macros(import, required_module, only)
        } else {
            return Ok(Some(self.wait_for_module_interface(required_module)));
        };
        for function in macros {
            self.namespace = self.world.bind_required_macro(self.namespace, function);
        }
        Ok(None)
    }

    /// The macros a `require` makes callable by their qualified names: every
    /// macro the module exports, or the ones `only:` names or `except:` does
    /// not deny. A name that is not an exported macro is refused.
    fn selected_macros(
        &self,
        import: &ImportForm,
        callables: &[ModuleInterfaceCallable],
    ) -> Result<Vec<FunctionId>, FatalError> {
        let macros = || {
            callables
                .iter()
                .filter(|callable| callable.kind == InterfaceCallableKind::Macro)
        };
        let exported_macro = |name: &str, arity: usize| {
            macros()
                .find(|callable| callable.matches_name_arity(name, arity))
                .ok_or_else(|| self.not_an_exported_macro(import, name, arity))
        };
        match (&import.only, &import.except) {
            (Some(ImportSelection::Listed(only)), _) => only
                .iter()
                .map(|(name, arity)| exported_macro(name, *arity).map(|callable| callable.function))
                .collect(),
            (Some(ImportSelection::Kind(kind)), _) => Ok(macros()
                .filter(|callable| is_of_kind(callable, *kind))
                .map(|callable| callable.function)
                .collect()),
            (None, Some(except)) => {
                for (name, arity) in except {
                    exported_macro(name, *arity)?;
                }
                Ok(macros()
                    .filter(|callable| {
                        !except
                            .iter()
                            .any(|denied| callable.matches_name_arity(&denied.0, denied.1))
                    })
                    .map(|callable| callable.function)
                    .collect())
            }
            (None, None) => Ok(macros().map(|callable| callable.function).collect()),
        }
    }

    /// The macros an `only:` list names, as references to be resolved when the
    /// module's interface is published.
    fn referenced_macros(
        &mut self,
        import: &ImportForm,
        module: ModuleId,
        only: &[(String, usize)],
    ) -> Vec<FunctionId> {
        only.iter()
            .map(|(name, arity)| {
                self.world.reference_module_interface_callable(
                    module,
                    name.clone(),
                    *arity,
                    InterfaceCallableKind::Macro,
                    Some(self.interface_requester(import.span)),
                )
            })
            .collect()
    }

    fn not_an_exported_macro(&self, import: &ImportForm, name: &str, arity: usize) -> FatalError {
        emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::RESOLVE_UNKNOWN_IMPORT,
                format!(
                    "module `{}` does not export macro `{}/{}`",
                    import.path.join("."),
                    name,
                    arity
                ),
                import.span,
            ),
        )
    }

    /// The first step of `import` and `require`: the module the path names,
    /// which must be one this scope can load.
    fn start(&mut self, import: &ImportForm) -> Result<ModuleId, FatalError> {
        let path = ModuleName::from_segments(import.path.clone());
        let module = self.world.resolve_module_name(self.namespace, &path);
        self.refuse_module_defined_in_this_scope(import, module)?;
        let requester = self.interface_requester(import.span);
        self.world.note_module_reference_expectation(module, requester);
        Ok(module)
    }

    fn bind_required_module_path(&mut self, import: &ImportForm, module: ModuleId) {
        let Some((first, rest)) = import.path.split_first() else {
            return;
        };
        let bound_module = if rest.is_empty() {
            module
        } else {
            match self.world.lookup_namespace(self.namespace, first) {
                Some(NamespaceSymbol::Module(prefix)) => prefix,
                _ => self
                    .world
                    .reference_module(ModuleName::from_segments(vec![first.clone()])),
            }
        };
        self.bind_module_name(first, bound_module);
    }

    /// `import M` brings in what `M` exports, `only:` and `except:` choosing,
    /// and replaces what an earlier import of `M` brought in. A module whose
    /// interface is not published yet can still be imported by an `only:` list
    /// of names, which bind as references to be resolved when it is.
    fn apply_import(&mut self, import: &ImportForm) -> Result<Option<JobEffects>, FatalError> {
        let module = self.start(import)?;
        self.namespace = self.world.replace_imports_of(self.namespace, module);
        if self.world.module_interface_revision(module).is_some() {
            self.reads.push(FactKey::ModuleInterface(module));
            self.bind_interface_imports(import, module)?;
            return Ok(None);
        }
        let Some(ImportSelection::Listed(only)) = import.only.as_ref() else {
            return Ok(Some(self.wait_for_module_interface(module)));
        };
        for (name, arity) in only {
            let function = self.world.reference_module_interface_callable(
                module,
                name.clone(),
                *arity,
                InterfaceCallableKind::Callable,
                Some(self.interface_requester(import.span)),
            );
            let reference = self.world.function_ref(function).clone();
            let callable = ModuleInterfaceCallable {
                function,
                reference,
                kind: InterfaceCallableKind::Callable,
                variadic: false,
            };
            self.bind_imported(module, &callable);
        }
        Ok(None)
    }

    fn bind_imported(&mut self, module: ModuleId, callable: &ModuleInterfaceCallable) {
        self.namespace = self.world.bind_import(
            self.namespace,
            module,
            callable.reference.name(),
            callable.namespace_symbol(),
        );
    }

    /// Binds the callables an `import` selects from `module`'s published
    /// interface: the `only` list in its order, a kind of callable, or every
    /// callable `except` does not deny.
    fn bind_interface_imports(&mut self, import: &ImportForm, module: ModuleId) -> Result<(), FatalError> {
        let callables = self.world.module_interface(module).callables().to_vec();
        match (&import.only, &import.except) {
            (Some(ImportSelection::Listed(only)), _) => {
                for (name, arity) in only {
                    let callable = self.exported(import, &callables, name, *arity)?;
                    self.bind_imported(module, callable);
                }
            }
            (Some(ImportSelection::Kind(kind)), _) => {
                for callable in callables.iter().filter(|callable| is_of_kind(callable, *kind)) {
                    self.bind_imported(module, callable);
                }
            }
            (None, Some(except)) => {
                for (name, arity) in except {
                    self.exported(import, &callables, name, *arity)?;
                }
                for callable in callables.iter().filter(|callable| {
                    !except
                        .iter()
                        .any(|denied| callable.matches_name_arity(&denied.0, denied.1))
                }) {
                    self.bind_imported(module, callable);
                }
            }
            (None, None) => {
                for callable in &callables {
                    self.bind_imported(module, callable);
                }
            }
        }
        Ok(())
    }

    /// The callable of `callables` that a name and arity in an import list
    /// stands for, or the refusal that it exports none.
    fn exported<'c>(
        &self,
        import: &ImportForm,
        callables: &'c [ModuleInterfaceCallable],
        name: &str,
        arity: usize,
    ) -> Result<&'c ModuleInterfaceCallable, FatalError> {
        callables
            .iter()
            .find(|callable| callable.matches_name_arity(name, arity))
            .ok_or_else(|| {
                emit_job_diagnostic(
                    self.telemetry,
                    Diagnostic::error(
                        codes::RESOLVE_UNKNOWN_IMPORT,
                        format!(
                            "module `{}` does not export `{}/{}`",
                            import.path.join("."),
                            name,
                            arity
                        ),
                        import.span,
                    ),
                )
            })
    }

    /// A module is not loaded until the scope that defines it has finished,
    /// so that scope cannot require or import it.
    fn refuse_module_defined_in_this_scope(&self, import: &ImportForm, module: ModuleId) -> Result<(), FatalError> {
        if !self
            .world
            .module_defined_within(module, self.current_module, self.source_owner)
        {
            return Ok(());
        }
        Err(emit_job_diagnostic(
            self.telemetry,
            Diagnostic::error(
                codes::RESOLVE_MODULE_NOT_LOADED,
                format!(
                    "module {} is not loaded but was defined. This happens when you depend on a module in the same context in which it is defined. Try defining the module outside the context that uses it.",
                    self.world
                        .module_name(module)
                        .expect("a module with a recorded source has a name")
                ),
                import.span,
            ),
        ))
    }

    fn interface_requester(&self, span: Span) -> InterfaceRequester {
        InterfaceRequester {
            owner: self.source_owner,
            module: self.current_module,
            span,
        }
    }

    fn wait_for_module_interface(&self, module: ModuleId) -> JobEffects {
        // `FactKey::ModuleInterface`'s producer is demand-selected in
        // `World::demand_fact_producer` (Job::DefineModule when the module has
        // source state or is a runtime module, else Job::DefineModuleInterface).
        JobEffects::wait_on_current(FactKey::ModuleInterface(module))
    }
}

fn is_of_kind(callable: &ModuleInterfaceCallable, kind: CallableKind) -> bool {
    match kind {
        CallableKind::Macros => callable.kind == InterfaceCallableKind::Macro,
        CallableKind::Functions => callable.kind != InterfaceCallableKind::Macro,
        CallableKind::Sigils => callable.reference.name().starts_with("sigil_"),
    }
}

/// The module an `alias`, `import` or `require` names: the one a body's
/// statement is the value of. An alias group names the last of its members.
pub(crate) fn directive_module(world: &mut World, namespace: Namespace, form: &ScopeForm) -> ModuleId {
    match form {
        ScopeForm::Alias(alias) => {
            let binding = alias.bindings.last().expect("an alias binds at least one name");
            world.reference_module(ModuleName::from_segments(binding.path.clone()))
        }
        ScopeForm::Import(import) | ScopeForm::Require(import) => {
            world.resolve_module_name(namespace, &ModuleName::from_segments(import.path.clone()))
        }
        _ => unreachable!("only alias, import and require are scope directives"),
    }
}

/// What a body's scope becomes after `form`.
pub(crate) fn advance_scope<T: crate::telemetry::Telemetry>(
    mut directive: ScopeDirective<'_, T>,
    scope: ScopeSnapshot,
    form: &ScopeForm,
) -> Result<DirectedScope, FatalError> {
    directive.namespace = scope.namespace();
    Ok(match directive.apply(form)? {
        Some(effects) => DirectedScope::Blocked(Box::new(effects)),
        None => DirectedScope::Moved(scope.with_namespace(directive.namespace)),
    })
}
