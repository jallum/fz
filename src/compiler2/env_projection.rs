//! The env a macro reads as `__CALLER__`, or a body as `__ENV__`: Elixir's
//! `%Macro.Env{}`, projected from the scope it describes.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use fz_runtime::any_value::AnyValueRef;

use crate::modules::identity::ModuleName;
use crate::source::{SourceMap, Span};

use super::identity::DeclaredCallableKind;
use super::namespace::NamespaceSymbol;
use super::quoted_expander::ExpansionContext;
use super::scope::ScopeSnapshot;
use super::source::{QuotedSourceBuilder, QuotedSourceError, QuotedSourceMetadata};
use super::world::World;

/// The file `%Macro.Env{}` names when the call has no source position.
const NO_FILE: &str = "nofile";

/// Where a macro call, or a definition, is written: the file's name and the
/// 1-based line, as `%Macro.Env{}` reports them. Two calls on different
/// lines of one file expand independently, since each reads its own line.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CallSite {
    file: Arc<str>,
    line: u32,
}

impl CallSite {
    /// The site `span` locates; a span-less site is the line 0 of `nofile`
    /// that `%Macro.Env{}` defaults to.
    pub(crate) fn locate(span: Option<Span>, source_map: &SourceMap) -> Self {
        match span.filter(|span| !span.is_dummy()) {
            Some(span) => Self {
                file: source_map.name(span.source_version).unwrap_or(NO_FILE).into(),
                line: source_map.locate(span).line,
            },
            None => Self {
                file: NO_FILE.into(),
                line: 0,
            },
        }
    }
}

/// Functions or macros by the module they come from, as `%Macro.Env{}` lists
/// them: modules in atom order, each with its `{name, arity}` pairs in order.
type ImportsByModule = BTreeMap<String, BTreeSet<(String, usize)>>;

impl World {
    /// The module a scope stands in, as the alias that names it: its exact
    /// denotation rides in the alias's metadata, so a macro that unquotes it
    /// as a call target reaches that module and no other of the same display
    /// path. A bare-atom module is its atom, and no module is `nil`.
    pub(crate) fn project_module_value(
        &self,
        builder: &QuotedSourceBuilder,
        scope: ScopeSnapshot,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let Some(denotation) = self.module_denotation(scope.module_id()) else {
            return Ok(builder.nil());
        };
        if denotation.named_path().is_some_and(ModuleName::is_bare_atom) {
            return Ok(builder.atom(&denotation.atom_name()));
        }
        let metadata = QuotedSourceMetadata {
            module: Some(denotation.clone()),
            bound_callable: None,
            from_brackets: false,
            span: None,
            counter: None,
        };
        let segments = denotation.display_segments().map(String::as_str).collect::<Vec<_>>();
        builder.alias(&metadata, &segments)
    }

    pub(crate) fn project_env_value(
        &self,
        builder: &QuotedSourceBuilder,
        scope: ScopeSnapshot,
        context: ExpansionContext,
        call_site: &CallSite,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let function = match scope.function_id() {
            Some(function) => {
                let function_ref = self.function_ref(function).lexical_owner();
                builder.tuple(&[
                    builder.atom(function_ref.name()),
                    builder.int(function_ref.arity as i64),
                ])?
            }
            None => builder.nil(),
        };
        let module = self.project_module_value(builder, scope)?;
        let context_modules = match scope.module_id() {
            id if id.is_global() => builder.empty_list(),
            id => builder.list(&[self.module_atom_value(builder, id)])?,
        };
        let (functions, macros) = self.imports_in_scope(scope);
        let entries = [
            (
                "__struct__",
                builder.atom(&ModuleName::from_segments(vec!["Macro".into(), "Env".into()]).atom_name()),
            ),
            ("aliases", self.project_aliases(builder, scope)?),
            (
                "context",
                context
                    .atom_name()
                    .map_or_else(|| builder.nil(), |name| builder.atom(name)),
            ),
            ("context_modules", context_modules),
            ("file", builder.utf8_binary(&call_site.file)?),
            ("function", function),
            ("functions", project_imports(builder, &functions)?),
            ("lexical_tracker", builder.nil()),
            ("line", builder.int(i64::from(call_site.line))),
            ("macro_aliases", builder.empty_list()),
            ("macros", project_imports(builder, &macros)?),
            ("module", module),
            ("requires", self.project_requires(builder, scope, &functions, &macros)?),
            ("tracers", builder.empty_list()),
            ("versioned_vars", builder.map(&[])?),
        ];
        let entries: Vec<_> = entries
            .into_iter()
            .map(|(key, value)| (builder.atom(key), value))
            .collect();
        builder.map(&entries)
    }

    /// `[{Short, Full}]` for each module the scope binds under a name that is
    /// not the module's own: an `alias`, or a nested module's short name. In
    /// the order they were written; a name bound again keeps its first place.
    fn project_aliases(
        &self,
        builder: &QuotedSourceBuilder,
        scope: ScopeSnapshot,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let mut aliases: Vec<(&str, String)> = Vec::new();
        let bindings: Vec<_> = self.namespace_bindings(scope.namespace()).collect();
        for (name, symbol) in bindings.into_iter().rev() {
            let NamespaceSymbol::Module(module) = symbol else {
                continue;
            };
            let Some(denotation) = self.module_denotation(*module) else {
                continue;
            };
            let full = denotation.atom_name();
            if full == short_atom_name(name) {
                continue;
            }
            match aliases.iter_mut().find(|(bound, _)| *bound == name) {
                Some(entry) => entry.1 = full,
                None => aliases.push((name, full)),
            }
        }
        let pairs = aliases
            .iter()
            .map(|(name, full)| builder.tuple(&[builder.atom(&short_atom_name(name)), builder.atom(full)]))
            .collect::<Result<Vec<_>, _>>()?;
        builder.list(&pairs)
    }

    /// The modules whose macros the scope may call by qualified name: those
    /// `require`d, and those it imports from, in atom order.
    fn project_requires(
        &self,
        builder: &QuotedSourceBuilder,
        scope: ScopeSnapshot,
        functions: &ImportsByModule,
        macros: &ImportsByModule,
    ) -> Result<AnyValueRef, QuotedSourceError> {
        let required = self
            .required_modules(scope.namespace())
            .filter_map(|module| self.module_denotation(module))
            .map(|denotation| denotation.atom_name());
        let modules: BTreeSet<String> = required
            .chain(functions.keys().cloned())
            .chain(macros.keys().cloned())
            .collect();
        let atoms: Vec<_> = modules.iter().map(|module| builder.atom(module)).collect();
        builder.list(&atoms)
    }

    /// The functions and the macros the scope imports: its callable bindings
    /// owned by another module.
    fn imports_in_scope(&self, scope: ScopeSnapshot) -> (ImportsByModule, ImportsByModule) {
        let mut functions = ImportsByModule::new();
        let mut macros = ImportsByModule::new();
        for (_, symbol) in self.namespace_bindings(scope.namespace()) {
            let (NamespaceSymbol::Function(function)
            | NamespaceSymbol::Macro(function)
            | NamespaceSymbol::Callable(function)) = symbol
            else {
                continue;
            };
            let owner = self.function_module(*function);
            let Some(denotation) = self.module_denotation(owner).filter(|_| owner != scope.module_id()) else {
                continue;
            };
            let imports = match (symbol, self.declared_callable_kind(*function)) {
                (NamespaceSymbol::Function(_), _) | (_, Some(DeclaredCallableKind::Function)) => &mut functions,
                (NamespaceSymbol::Macro(_), _) | (_, Some(DeclaredCallableKind::Macro)) => &mut macros,
                _ => continue,
            };
            let reference = self.function_ref(*function);
            imports
                .entry(denotation.atom_name())
                .or_default()
                .insert((reference.name().to_string(), reference.arity));
        }
        (functions, macros)
    }
}

fn short_atom_name(name: &str) -> String {
    ModuleName::from_segments(vec![name.to_string()]).atom_name()
}

/// `[{Module, [{name, arity}]}]`.
fn project_imports(builder: &QuotedSourceBuilder, imports: &ImportsByModule) -> Result<AnyValueRef, QuotedSourceError> {
    let groups = imports
        .iter()
        .map(|(module, callables)| {
            let pairs = callables
                .iter()
                .map(|(name, arity)| builder.tuple(&[builder.atom(name), builder.int(*arity as i64)]))
                .collect::<Result<Vec<_>, _>>()?;
            builder.tuple(&[builder.atom(module), builder.list(&pairs)?])
        })
        .collect::<Result<Vec<_>, _>>()?;
    builder.list(&groups)
}
