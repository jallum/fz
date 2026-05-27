//! fz-ul4.18.1 — module resolution / flattening.
//!
//! Runs after parse and before macro expansion. Walks the parsed Program
//! and produces a flat Program where every fn lives under its
//! fully-qualified name (`Mod.fn` in .18.1; nested gets `A.B.fn` in
//! .18.2). Inside each module's bodies, bare references to sibling
//! fns/macros are rewritten to qualified names; cross-module
//! `Mod.fn(args)` calls (parsed as `Call(Dot(Var(Mod), "fn"), args)`)
//! also rewrite to `Call(Var("Mod.fn"), args)`.
//!
//! After this pass, downstream code (macro expansion, planner, eval, JIT,
//! AOT) can stay module-unaware: it sees one flat Program of
//! `Item::Fn`s with possibly-dotted names.
//!
//! Ungrouped top-level fns (those without an enclosing `defmodule`)
//! pass through with their bare names so existing un-modular fixtures
//! keep working.
//!
//! Span policy (post-.20.2): rewrites preserve the original AST node's
//! span. Replacing `helper(x)` with `M.helper(x)` keeps the call's span
//! pointing at the bare-name source position — that's the right
//! diagnostic source for "this call resolves to …".

use crate::ast::*;
use crate::diag::{Diagnostic, Span, codes};
use crate::modules::identity::{ExportKey, ModuleName, QualifiedName};
use crate::modules::interface::ModuleInterface;
use crate::protocols::{
    ImplTarget, ProtocolCallbackFact, ProtocolDecl, ProtocolImplFact, ProtocolImplKey,
    ProtocolRegistry,
};
use std::collections::BTreeMap;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Errors produced by `flatten_modules`. Each variant carries the source
/// `Span` of the offending AST node so the driver can render an underlined
/// diagnostic instead of a DUMMY-span headline. See fz-ul4.21.
#[derive(Debug, Clone)]
pub enum ResolveError {
    DuplicateModule {
        module: ModuleName,
        first_span: Span,
        duplicate_span: Span,
    },
    DuplicateExport {
        export: ExportKey,
        first_span: Span,
        duplicate_span: Span,
    },
    UnknownModule {
        module: ModuleName,
        span: Span,
    },
    UnknownImport {
        export: ExportKey,
        span: Span,
    },
    ConflictingImport {
        name: String,
        arity: usize,
        first_module: ModuleName,
        second_module: ModuleName,
        first_span: Span,
        second_span: Span,
    },
    /// fz-ul4.31.5 — Failure to build a module's `@type` env (duplicate
    /// alias, cycle, or unknown name in an alias body).
    TypeAliasError {
        msg: String,
        span: Span,
    },
    ProtocolError {
        msg: String,
        span: Span,
    },
}

impl ResolveError {
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            Self::DuplicateModule {
                module,
                first_span,
                duplicate_span,
            } => Diagnostic::error(
                codes::RESOLVE_DUPLICATE_MODULE,
                format!("module `{}` is defined more than once", module),
                *duplicate_span,
            )
            .with_secondary(*first_span, "first definition here"),
            Self::DuplicateExport {
                export,
                first_span,
                duplicate_span,
            } => Diagnostic::error(
                codes::RESOLVE_DUPLICATE_EXPORT,
                format!("export `{}` is defined more than once", export),
                *duplicate_span,
            )
            .with_secondary(*first_span, "first definition here"),
            Self::UnknownModule { module, span } => Diagnostic::error(
                codes::RESOLVE_UNKNOWN_MODULE,
                format!("module `{}` is not defined", module),
                *span,
            ),
            Self::UnknownImport { export, span } => Diagnostic::error(
                codes::RESOLVE_UNKNOWN_IMPORT,
                format!("module `{}` does not export `{}/{}`", export.module, export.name, export.arity),
                *span,
            ),
            Self::ConflictingImport {
                name,
                arity,
                first_module,
                second_module,
                first_span,
                second_span,
            } => Diagnostic::error(
                codes::RESOLVE_CONFLICTING_IMPORT,
                format!(
                    "import `{}/{}` from module `{}` conflicts with existing import from module `{}`",
                    name, arity, second_module, first_module
                ),
                *second_span,
            )
            .with_secondary(*first_span, "first import here"),
            Self::TypeAliasError { msg, span } => {
                Diagnostic::error(codes::RESOLVE_TYPE_ALIAS, msg.clone(), *span)
            }
            Self::ProtocolError { msg, span } => {
                Diagnostic::error(codes::RESOLVE_PROTOCOL, msg.clone(), *span)
            }
        }
    }
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_diagnostic().message)
    }
}

impl std::error::Error for ResolveError {}

/// REPL helper: rewrite cross-module `Mod.fn(args)` calls in a single
/// expression. No sibling-fn rewriting (the REPL has no enclosing
/// module).
#[allow(dead_code)]
pub fn rewrite_expr_top_level(e: &mut Spanned<Expr>) {
    let no_siblings: HashSet<String> = HashSet::new();
    let mut intro: HashSet<String> = HashSet::new();
    let no_paths: HashSet<String> = HashSet::new();
    let no_aliases: HashMap<String, String> = HashMap::new();
    let no_imports: ImportMap = HashMap::new();
    rewrite_expr(
        e,
        "",
        &no_siblings,
        &mut intro,
        &no_paths,
        &no_aliases,
        &no_imports,
    );
}

pub fn flatten_modules<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: Program,
) -> Result<Program, ResolveError> {
    flatten_modules_with_options(t, prog, BTreeMap::new())
}

pub fn flatten_modules_with_interface_table<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: Program,
    interface_table: InterfaceTable,
) -> Result<Program, ResolveError> {
    flatten_modules_with_options(t, prog, interface_table)
}

fn flatten_modules_with_options<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: Program,
    mut interface_table: InterfaceTable,
) -> Result<Program, ResolveError> {
    collect_module_fns(&prog)?;
    let module_macros = collect_module_macros(&prog);
    let module_interfaces = crate::modules::interface::collect_from_program(&prog);
    add_requested_runtime_interfaces(&prog, &module_interfaces, &mut interface_table);
    let external_module_interfaces = interface_table
        .iter()
        .filter(|(name, _)| !module_interfaces.contains_key(*name))
        .map(|(name, interface)| (name.clone(), interface.clone()))
        .collect::<BTreeMap<_, _>>();
    for (name, interface) in &module_interfaces {
        interface_table.insert(name.clone(), interface.clone());
    }
    let module_paths = collect_visible_module_paths(&prog, &interface_table);
    let mut out: Vec<Rc<Item>> = Vec::new();
    let mut module_docs: HashMap<String, String> = HashMap::new();
    collect_module_docs(&prog, &mut module_docs);
    // Build per-module `@type` envs. The root env includes compiler-known
    // runtime primitive types plus root aliases from the always-loaded
    // prelude, so module specs and aliases can name standard aliases such as
    // keyword/0 and keyword/1.
    let mut module_type_envs: HashMap<String, crate::type_expr::ModuleTypeEnv> = HashMap::new();
    let root_types = crate::modules::runtime_library::root_type_env(t);
    let root_type_env = root_types.env.clone();
    module_type_envs.insert(String::new(), root_type_env.clone());
    let mut opaque_inners: HashMap<String, crate::types::Ty> = root_types.opaque_inners;
    let mut brand_inners: HashMap<String, crate::types::Ty> = root_types.brand_inners;
    collect_module_type_envs(
        t,
        &prog,
        "",
        &root_type_env,
        &mut module_type_envs,
        &mut opaque_inners,
        &mut brand_inners,
    )?;
    let protocol_registry = collect_protocol_registry(t, &prog, &mut module_type_envs)?;
    let (root_aliases, root_imports) =
        collect_import_scope(&prog.items, &interface_table, &module_macros)?;
    for item in &prog.items {
        match &**item {
            Item::Fn(def) => {
                let mut new_def = def.clone();
                let no_siblings: HashSet<String> = HashSet::new();
                for clause in &mut new_def.clauses {
                    let mut intro = pattern_intro(&clause.params);
                    rewrite_expr(
                        &mut clause.body,
                        "",
                        &no_siblings,
                        &mut intro,
                        &module_paths,
                        &root_aliases,
                        &root_imports,
                    );
                    if let Some(g) = &mut clause.guard {
                        rewrite_expr(
                            g,
                            "",
                            &no_siblings,
                            &mut intro,
                            &module_paths,
                            &root_aliases,
                            &root_imports,
                        );
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(m) => flatten_module(
                m,
                None,
                &mut out,
                &module_paths,
                &interface_table,
                &module_macros,
            )?,
            Item::Alias { .. } | Item::Import { .. } => {}
            Item::MacroCall {
                name,
                name_span,
                args,
                parent_module: _,
                span,
            } => {
                let no_siblings: HashSet<String> = HashSet::new();
                let mut new_args: Vec<Spanned<Expr>> = args.clone();
                for a in &mut new_args {
                    let mut intro: HashSet<String> = HashSet::new();
                    rewrite_expr(
                        a,
                        "",
                        &no_siblings,
                        &mut intro,
                        &module_paths,
                        &root_aliases,
                        &root_imports,
                    );
                }
                out.push(Rc::new(Item::MacroCall {
                    name: name.clone(),
                    name_span: *name_span,
                    args: new_args,
                    parent_module: None,
                    span: *span,
                }));
            }
            Item::Protocol(_) => {}
            Item::ProtocolImpl(protocol_impl) => flatten_protocol_impl(
                protocol_impl,
                None,
                &mut out,
                &module_paths,
                &root_aliases,
                &root_imports,
            )?,
        }
    }
    Ok(Program {
        items: out,
        module_interfaces,
        external_module_interfaces,
        module_docs,
        module_type_envs,
        protocol_registry,
        opaque_inners,
        brand_inners,
    })
}

fn add_requested_runtime_interfaces(
    prog: &Program,
    local_interfaces: &InterfaceTable,
    interface_table: &mut InterfaceTable,
) {
    let mut requested = Vec::new();
    collect_requested_external_modules(prog, &mut requested);
    for module in requested {
        if local_interfaces.contains_key(&module) || interface_table.contains_key(&module) {
            continue;
        }
        if let Some(interface) = crate::modules::runtime_library::interface(&module) {
            interface_table.insert(module, interface);
        }
    }
}

fn collect_requested_external_modules(prog: &Program, out: &mut Vec<ModuleName>) {
    for item in &prog.items {
        match &**item {
            Item::Module(module) => collect_requested_external_modules_recursive(module, out),
            Item::Alias { full_path, .. } => out.push(full_path.clone()),
            Item::Import { path, .. } => out.push(path.clone()),
            Item::Fn(def) => {
                for clause in &def.clauses {
                    collect_top_level_qualified_calls(&clause.body, out);
                    if let Some(guard) = &clause.guard {
                        collect_top_level_qualified_calls(guard, out);
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_requested_external_modules_recursive(module: &ModuleDef, out: &mut Vec<ModuleName>) {
    for item in &module.items {
        match &**item {
            Item::Alias { full_path, .. } => out.push(full_path.clone()),
            Item::Import { path, .. } => out.push(path.clone()),
            Item::Module(inner) => collect_requested_external_modules_recursive(inner, out),
            _ => {}
        }
    }
}

fn collect_top_level_qualified_calls(expr: &Spanned<Expr>, out: &mut Vec<ModuleName>) {
    match &expr.node {
        Expr::Call(callee, args) => {
            if let Some(module) = qualified_callee_module(callee) {
                out.push(module);
            }
            collect_top_level_qualified_calls(callee, out);
            for arg in args {
                collect_top_level_qualified_calls(arg, out);
            }
        }
        Expr::FnRef { name, .. } => {
            if let Some((module, _fun)) = name.rsplit_once('.')
                && let Ok(module) = ModuleName::parse_dotted(module)
            {
                out.push(module);
            }
        }
        Expr::List(xs, tail) => {
            for x in xs {
                collect_top_level_qualified_calls(x, out);
            }
            if let Some(tail) = tail {
                collect_top_level_qualified_calls(tail, out);
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                collect_top_level_qualified_calls(x, out);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_top_level_qualified_calls(&field.value, out);
            }
        }
        Expr::Map(pairs) => {
            for (key, value) in pairs {
                collect_top_level_qualified_calls(key, out);
                collect_top_level_qualified_calls(value, out);
            }
        }
        Expr::MapUpdate(map, pairs) => {
            collect_top_level_qualified_calls(map, out);
            for (key, value) in pairs {
                collect_top_level_qualified_calls(key, out);
                collect_top_level_qualified_calls(value, out);
            }
        }
        Expr::Index(target, key) => {
            collect_top_level_qualified_calls(target, out);
            collect_top_level_qualified_calls(key, out);
        }
        Expr::BinOp(_, left, right) => {
            collect_top_level_qualified_calls(left, out);
            collect_top_level_qualified_calls(right, out);
        }
        Expr::UnOp(_, inner)
        | Expr::Ascribe(inner, _)
        | Expr::Quote(inner)
        | Expr::Unquote(inner) => {
            collect_top_level_qualified_calls(inner, out);
        }
        Expr::If(cond, then_expr, else_expr) => {
            collect_top_level_qualified_calls(cond, out);
            collect_top_level_qualified_calls(then_expr, out);
            if let Some(else_expr) = else_expr {
                collect_top_level_qualified_calls(else_expr, out);
            }
        }
        Expr::Case(scrutinee, arms) => {
            if let Some(scrutinee) = scrutinee {
                collect_top_level_qualified_calls(scrutinee, out);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_top_level_qualified_calls(guard, out);
                }
                collect_top_level_qualified_calls(&arm.body, out);
            }
        }
        Expr::Cond(pairs) => {
            for (cond, body) in pairs {
                collect_top_level_qualified_calls(cond, out);
                collect_top_level_qualified_calls(body, out);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, expr) | WithBinding::Bare(expr) => {
                        collect_top_level_qualified_calls(expr, out);
                    }
                }
            }
            collect_top_level_qualified_calls(body, out);
            for arm in else_clauses {
                if let Some(guard) = &arm.guard {
                    collect_top_level_qualified_calls(guard, out);
                }
                collect_top_level_qualified_calls(&arm.body, out);
            }
        }
        Expr::Match(_, rhs) => collect_top_level_qualified_calls(rhs, out),
        Expr::Lambda(_, body) => collect_top_level_qualified_calls(body, out),
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_top_level_qualified_calls(guard, out);
                }
                collect_top_level_qualified_calls(&clause.body, out);
            }
            if let Some(after) = after {
                collect_top_level_qualified_calls(&after.timeout, out);
                collect_top_level_qualified_calls(&after.body, out);
            }
        }
        Expr::Var(_)
        | Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil => {}
    }
}

fn qualified_callee_module(callee: &Spanned<Expr>) -> Option<ModuleName> {
    let mut path = Vec::new();
    let mut cur = &callee.node;
    loop {
        match cur {
            Expr::Index(target, key) => {
                let Expr::Atom(member) = &key.node else {
                    return None;
                };
                path.push(member.clone());
                cur = &target.node;
            }
            Expr::Var(name) if is_upper(name) => {
                if path.is_empty() {
                    return None;
                }
                path.push(name.clone());
                path.reverse();
                path.pop();
                return Some(ModuleName::from_segments(path));
            }
            _ => return None,
        }
    }
}

/// fz-ul4.31.5 — Walk every ModuleDef in `prog` (recursively into
/// nested modules) and build its `@type` env. Errors from
/// `build_module_type_env` (duplicate alias, cycle, unknown ref)
/// surface as `ResolveError::TypeAliasError`.
///
/// fz-swt.8 — also accumulates the per-module opaque-inner-type map
/// into a single program-wide map. Tags are already module-qualified
/// (e.g. `"Mod::t"`) so cross-module collisions cannot happen except
/// for the unqualified built-in `"resource"` tag, which carries no
/// inner type at this layer.
fn collect_module_type_envs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: &Program,
    parent: &str,
    base_env: &crate::type_expr::ModuleTypeEnv,
    out: &mut HashMap<String, crate::type_expr::ModuleTypeEnv>,
    o_inners: &mut HashMap<String, crate::types::Ty>,
    b_inners: &mut HashMap<String, crate::types::Ty>,
) -> Result<(), ResolveError> {
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_type_envs_recursive(t, m, parent, base_env, out, o_inners, b_inners)?;
        }
    }
    Ok(())
}

fn collect_module_type_envs_recursive<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &ModuleDef,
    parent: &str,
    base_env: &crate::type_expr::ModuleTypeEnv,
    out: &mut HashMap<String, crate::type_expr::ModuleTypeEnv>,
    o_inners: &mut HashMap<String, crate::types::Ty>,
    b_inners: &mut HashMap<String, crate::types::Ty>,
) -> Result<(), ResolveError> {
    let path = if parent.is_empty() {
        m.name.clone()
    } else {
        format!("{}.{}", parent, m.name)
    };
    let (env, opaque_inners, brand_inners) =
        crate::type_expr::build_module_type_env_for_with_base(t, &m.attrs, &path, base_env)
            .map_err(|e| ResolveError::TypeAliasError {
                msg: format!("module `{}`: {}", path, e.msg),
                span: e.span,
            })?;
    out.insert(path.clone(), env);
    o_inners.extend(opaque_inners);
    b_inners.extend(brand_inners);
    for item in &m.items {
        if let Item::Module(inner) = &**item {
            collect_module_type_envs_recursive(t, inner, &path, base_env, out, o_inners, b_inners)?;
        }
    }
    Ok(())
}

fn collect_module_docs(prog: &Program, out: &mut HashMap<String, String>) {
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_docs_recursive(m, "", out);
        }
    }
}

fn collect_module_docs_recursive(m: &ModuleDef, parent: &str, out: &mut HashMap<String, String>) {
    let path = if parent.is_empty() {
        m.name.clone()
    } else {
        format!("{}.{}", parent, m.name)
    };
    if let Some(d) = m.moduledoc() {
        out.insert(path.clone(), d.to_string());
    }
    for item in &m.items {
        if let Item::Module(inner) = &**item {
            collect_module_docs_recursive(inner, &path, out);
        }
    }
}

fn collect_protocol_registry<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    prog: &Program,
    module_type_envs: &mut HashMap<String, crate::type_expr::ModuleTypeEnv>,
) -> Result<ProtocolRegistry, ResolveError> {
    let mut registry = ProtocolRegistry::default();
    collect_protocol_registry_items(t, &prog.items, None, module_type_envs, &mut registry)?;
    validate_protocol_impls(&registry)?;
    for protocol in registry.protocols.keys() {
        let ty = protocol_domain_type(t, protocol, &registry);
        for env in module_type_envs.values_mut() {
            env.insert(format!("{}.t", protocol), ty.clone());
        }
        if let Some(env) = module_type_envs.get_mut(&protocol.dotted()) {
            env.insert("t".to_string(), ty);
        }
    }
    Ok(registry)
}

fn protocol_domain_type<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    protocol: &ModuleName,
    registry: &ProtocolRegistry,
) -> crate::types::Ty {
    let mut domain = t.opaque_of(&crate::protocols::protocol_domain_tag(protocol));
    for fact in registry
        .impls
        .values()
        .filter(|fact| fact.protocol == *protocol)
    {
        let target_ty = crate::protocols::impl_target_type(t, &fact.target);
        domain = t.union(domain, target_ty);
    }
    domain
}

fn collect_protocol_registry_items<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    items: &[Rc<Item>],
    parent: Option<&ModuleName>,
    module_type_envs: &mut HashMap<String, crate::type_expr::ModuleTypeEnv>,
    registry: &mut ProtocolRegistry,
) -> Result<(), ResolveError> {
    for item in items {
        match &**item {
            Item::Protocol(protocol) => {
                let name = qualify_module_child(parent, &protocol.name);
                let decl = protocol_decl(t, &name, protocol, module_type_envs)?;
                if registry
                    .protocols
                    .insert(name.clone(), decl.clone())
                    .is_some()
                {
                    return Err(ResolveError::ProtocolError {
                        msg: format!("protocol `{}` is defined more than once", name),
                        span: decl.span,
                    });
                }
            }
            Item::ProtocolImpl(protocol_impl) => {
                let protocol = qualify_module_child(parent, &protocol_impl.protocol);
                let target =
                    ImplTarget::module(qualify_module_child(parent, &protocol_impl.target.path));
                let callbacks = protocol_impl_callbacks(parent, protocol_impl)?;
                let fact = ProtocolImplFact {
                    protocol: protocol.clone(),
                    target: target.clone(),
                    callbacks,
                    span: protocol_impl.span,
                };
                let key = ProtocolImplKey { protocol, target };
                if registry.impls.insert(key.clone(), fact).is_some() {
                    return Err(ResolveError::ProtocolError {
                        msg: format!(
                            "protocol `{}` already has an implementation for `{}`",
                            key.protocol, key.target
                        ),
                        span: protocol_impl.span,
                    });
                }
            }
            Item::Module(module) => {
                let name = if let Some(parent) = parent {
                    parent.child(module.name.clone())
                } else {
                    ModuleName::from_segments(vec![module.name.clone()])
                };
                collect_protocol_registry_items(
                    t,
                    &module.items,
                    Some(&name),
                    module_type_envs,
                    registry,
                )?;
            }
            _ => {}
        }
    }

    Ok(())
}

fn protocol_decl<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    name: &ModuleName,
    protocol: &ProtocolDef,
    module_type_envs: &mut HashMap<String, crate::type_expr::ModuleTypeEnv>,
) -> Result<ProtocolDecl, ResolveError> {
    let mut env = crate::type_expr::ModuleTypeEnv::new();
    env.insert(
        "t".to_string(),
        t.opaque_of(&crate::protocols::protocol_domain_tag(name)),
    );
    env.insert(
        format!("{}.t", name),
        t.opaque_of(&crate::protocols::protocol_domain_tag(name)),
    );
    module_type_envs.insert(name.dotted(), env);

    let mut seen = HashMap::new();
    let mut callbacks = Vec::new();
    for callback in &protocol.callbacks {
        let key = (callback.name.clone(), callback.arity);
        if seen.insert(key.clone(), callback.span).is_some() {
            return Err(ResolveError::ProtocolError {
                msg: format!(
                    "protocol `{}` declares callback `{}/{}` more than once",
                    name, key.0, key.1
                ),
                span: callback.span,
            });
        }
        callbacks.push(ProtocolCallbackFact {
            name: callback.name.clone(),
            arity: callback.arity,
            spec: callback.attrs.iter().find_map(|attr| match attr {
                Attribute::Spec(spec) => Some(spec.clone()),
                _ => None,
            }),
            span: callback.span,
        });
    }
    callbacks.sort_by(|a, b| (&a.name, a.arity).cmp(&(&b.name, b.arity)));
    Ok(ProtocolDecl {
        callbacks,
        span: protocol.span,
    })
}

fn protocol_impl_callbacks(
    parent: Option<&ModuleName>,
    protocol_impl: &ProtocolImplDef,
) -> Result<BTreeMap<(String, usize), ExportKey>, ResolveError> {
    let mut callbacks = BTreeMap::new();
    let impl_module = qualify_module_child(parent, &protocol_impl.target.path);
    for item in &protocol_impl.items {
        match &**item {
            Item::Fn(def) => {
                let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let key = (def.name.clone(), arity);
                if callbacks
                    .insert(
                        key.clone(),
                        ExportKey::new(impl_module.clone(), def.name.clone(), arity),
                    )
                    .is_some()
                {
                    return Err(ResolveError::ProtocolError {
                        msg: format!(
                            "protocol implementation for `{}` defines `{}/{}` more than once",
                            protocol_impl.target.path, key.0, key.1
                        ),
                        span: def.name_span,
                    });
                }
            }
            _ => {
                return Err(ResolveError::ProtocolError {
                    msg: "protocol implementation bodies may only contain functions".to_string(),
                    span: protocol_impl.span,
                });
            }
        }
    }
    Ok(callbacks)
}

fn validate_protocol_impls(registry: &ProtocolRegistry) -> Result<(), ResolveError> {
    for fact in registry.impls.values() {
        let Some(protocol) = registry.protocols.get(&fact.protocol) else {
            return Err(ResolveError::ProtocolError {
                msg: format!(
                    "protocol implementation references unknown protocol `{}`",
                    fact.protocol
                ),
                span: fact.span,
            });
        };
        for callback in &protocol.callbacks {
            if !fact
                .callbacks
                .contains_key(&(callback.name.clone(), callback.arity))
            {
                return Err(ResolveError::ProtocolError {
                    msg: format!(
                        "implementation for protocol `{}` on `{}` is missing callback `{}/{}`",
                        fact.protocol, fact.target, callback.name, callback.arity
                    ),
                    span: fact.span,
                });
            }
        }
        for (name, arity) in fact.callbacks.keys() {
            if !protocol
                .callbacks
                .iter()
                .any(|callback| callback.name == *name && callback.arity == *arity)
            {
                return Err(ResolveError::ProtocolError {
                    msg: format!(
                        "implementation for protocol `{}` on `{}` provides unknown callback `{}/{}`",
                        fact.protocol, fact.target, name, arity
                    ),
                    span: fact.span,
                });
            }
        }
    }
    Ok(())
}

fn qualify_module_child(parent: Option<&ModuleName>, name: &ModuleName) -> ModuleName {
    if name.segments().len() == 1
        && let Some(parent) = parent
    {
        parent.child(name.last_segment().to_string())
    } else {
        name.clone()
    }
}

fn collect_visible_module_paths(prog: &Program, interfaces: &InterfaceTable) -> HashSet<String> {
    let mut out = HashSet::new();
    for item in &prog.items {
        match &**item {
            Item::Module(m) => collect_paths_recursive(m, "", &mut out),
            Item::Protocol(protocol) => {
                out.insert(protocol.name.dotted());
            }
            _ => {}
        }
    }
    out.extend(interfaces.keys().map(ModuleName::dotted));
    for interface in interfaces.values() {
        out.extend(
            interface
                .protocols
                .iter()
                .map(|protocol| protocol.name.dotted()),
        );
    }
    out
}

fn collect_paths_recursive(m: &ModuleDef, parent: &str, out: &mut HashSet<String>) {
    let path = if parent.is_empty() {
        m.name.clone()
    } else {
        format!("{}.{}", parent, m.name)
    };
    out.insert(path.clone());
    for item in &m.items {
        match &**item {
            Item::Module(inner) => collect_paths_recursive(inner, &path, out),
            Item::Protocol(protocol) => {
                out.insert(parent_qualified_module_name(&path, &protocol.name).dotted());
            }
            _ => {}
        }
    }
}

fn parent_qualified_module_name(parent: &str, name: &ModuleName) -> ModuleName {
    if parent.is_empty() || name.segments().len() != 1 {
        name.clone()
    } else {
        ModuleName::parse_dotted(parent)
            .expect("resolver parent paths are valid module names")
            .child(name.last_segment().to_string())
    }
}

#[derive(Clone)]
struct ModuleExports {
    span: Span,
    fns: HashMap<(String, usize), Span>,
}

type ModuleFns = HashMap<ModuleName, ModuleExports>;
type ModuleMacroExports = HashMap<ModuleName, HashSet<(String, usize)>>;
pub type InterfaceTable = BTreeMap<ModuleName, ModuleInterface>;
type ImportMap = HashMap<(String, usize), ImportBinding>;

#[derive(Clone)]
struct ImportBinding {
    module: ModuleName,
    span: Span,
}

fn collect_import_scope(
    items: &[Rc<Item>],
    module_interfaces: &InterfaceTable,
    module_macros: &ModuleMacroExports,
) -> Result<(HashMap<String, String>, ImportMap), ResolveError> {
    let mut aliases = HashMap::new();
    let mut imports = HashMap::new();
    for item in items {
        match &**item {
            Item::Alias {
                full_path,
                as_name,
                span,
            } => {
                if !module_interfaces.contains_key(full_path) {
                    return Err(ResolveError::UnknownModule {
                        module: full_path.clone(),
                        span: *span,
                    });
                }
                aliases.insert(as_name.clone(), full_path.dotted());
            }
            Item::Import {
                path,
                only,
                except,
                span,
            } => {
                collect_imports_for_item(
                    path,
                    only.as_deref(),
                    except.as_deref(),
                    *span,
                    module_interfaces,
                    module_macros,
                    &mut imports,
                )?;
            }
            _ => {}
        }
    }
    Ok((aliases, imports))
}

fn collect_imports_for_item(
    path: &ModuleName,
    only: Option<&[(String, usize)]>,
    except: Option<&[(String, usize)]>,
    span: Span,
    module_interfaces: &InterfaceTable,
    module_macros: &ModuleMacroExports,
    imports: &mut ImportMap,
) -> Result<(), ResolveError> {
    let Some(interface) = module_interfaces.get(path) else {
        return Err(ResolveError::UnknownModule {
            module: path.clone(),
            span,
        });
    };
    let target_exports = importable_exports(interface, module_macros.get(path));
    if let Some(allow) = only {
        validate_import_filter(path, allow, &target_exports, span)?;
    }
    if let Some(deny) = except {
        validate_import_filter(path, deny, &target_exports, span)?;
    }
    let pairs: Vec<(String, usize)> = if let Some(allow) = only {
        allow.to_vec()
    } else if let Some(deny) = except {
        let deny_set: HashSet<(String, usize)> = deny.iter().cloned().collect();
        target_exports
            .iter()
            .filter(|p| !deny_set.contains(*p))
            .cloned()
            .collect()
    } else {
        target_exports.iter().cloned().collect()
    };
    for (name, arity) in pairs {
        let key = (name, arity);
        if let Some(existing) = imports.get(&key)
            && existing.module != *path
        {
            return Err(ResolveError::ConflictingImport {
                name: key.0,
                arity: key.1,
                first_module: existing.module.clone(),
                second_module: path.clone(),
                first_span: existing.span,
                second_span: span,
            });
        }
        imports.insert(
            key,
            ImportBinding {
                module: path.clone(),
                span,
            },
        );
    }
    Ok(())
}

fn collect_module_fns(prog: &Program) -> Result<ModuleFns, ResolveError> {
    let mut out: ModuleFns = HashMap::new();
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_fns_recursive(m, None, &mut out)?;
        }
    }
    Ok(out)
}

fn collect_module_fns_recursive(
    m: &ModuleDef,
    parent: Option<&ModuleName>,
    out: &mut ModuleFns,
) -> Result<(), ResolveError> {
    let path = if let Some(parent) = parent {
        parent.child(m.name.clone())
    } else {
        ModuleName::from_segments(vec![m.name.clone()])
    };
    if let Some(first) = out.insert(
        path.clone(),
        ModuleExports {
            span: m.name_span,
            fns: HashMap::new(),
        },
    ) {
        return Err(ResolveError::DuplicateModule {
            module: path,
            first_span: first.span,
            duplicate_span: m.name_span,
        });
    }
    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let export = ExportKey::new(path.clone(), def.name.clone(), arity);
                let fns = &mut out.get_mut(&path).expect("module fn map was inserted").fns;
                let key = (def.name.clone(), arity);
                if let Some(first_span) = fns.insert(key, def.name_span) {
                    return Err(ResolveError::DuplicateExport {
                        export,
                        first_span,
                        duplicate_span: def.name_span,
                    });
                }
            }
            Item::Module(inner) => collect_module_fns_recursive(inner, Some(&path), out)?,
            _ => {}
        }
    }
    Ok(())
}

fn collect_module_macros(prog: &Program) -> ModuleMacroExports {
    let mut out: ModuleMacroExports = HashMap::new();
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_macros_recursive(m, None, &mut out);
        }
    }
    out
}

fn collect_module_macros_recursive(
    m: &ModuleDef,
    parent: Option<&ModuleName>,
    out: &mut ModuleMacroExports,
) {
    let path = if let Some(parent) = parent {
        parent.child(m.name.clone())
    } else {
        ModuleName::from_segments(vec![m.name.clone()])
    };
    let mut macros = HashSet::new();
    for item in &m.items {
        match &**item {
            Item::Fn(def) if def.is_macro => {
                let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                macros.insert((def.name.clone(), arity));
            }
            Item::Module(inner) => collect_module_macros_recursive(inner, Some(&path), out),
            _ => {}
        }
    }
    out.insert(path, macros);
}

fn flatten_module(
    m: &ModuleDef,
    parent_path: Option<&ModuleName>,
    out: &mut Vec<Rc<Item>>,
    module_paths: &HashSet<String>,
    module_interfaces: &InterfaceTable,
    module_macros: &ModuleMacroExports,
) -> Result<(), ResolveError> {
    let module_name = if let Some(parent) = parent_path {
        parent.child(m.name.clone())
    } else {
        ModuleName::from_segments(vec![m.name.clone()])
    };
    let module_path = module_name.dotted();
    let mut siblings: HashSet<String> = HashSet::new();
    let mut aliases: HashMap<String, String> = HashMap::new();
    let mut imports: ImportMap = HashMap::new();
    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                siblings.insert(def.name.clone());
            }
            Item::Alias {
                full_path,
                as_name,
                span,
            } => {
                if !module_interfaces.contains_key(full_path) {
                    return Err(ResolveError::UnknownModule {
                        module: full_path.clone(),
                        span: *span,
                    });
                }
                aliases.insert(as_name.clone(), full_path.dotted());
            }
            Item::Import {
                path,
                only,
                except,
                span,
            } => {
                let Some(interface) = module_interfaces.get(path) else {
                    return Err(ResolveError::UnknownModule {
                        module: path.clone(),
                        span: *span,
                    });
                };
                let target_exports = importable_exports(interface, module_macros.get(path));
                if let Some(allow) = only {
                    validate_import_filter(path, allow, &target_exports, *span)?;
                }
                if let Some(deny) = except {
                    validate_import_filter(path, deny, &target_exports, *span)?;
                }
                let pairs: Vec<(String, usize)> = if let Some(allow) = only {
                    allow.clone()
                } else if let Some(deny) = except {
                    let deny_set: HashSet<(String, usize)> = deny.iter().cloned().collect();
                    target_exports
                        .iter()
                        .filter(|p| !deny_set.contains(*p))
                        .cloned()
                        .collect()
                } else {
                    target_exports.iter().cloned().collect()
                };
                for (name, arity) in pairs {
                    let key = (name, arity);
                    if let Some(existing) = imports.get(&key)
                        && existing.module != *path
                    {
                        return Err(ResolveError::ConflictingImport {
                            name: key.0,
                            arity: key.1,
                            first_module: existing.module.clone(),
                            second_module: path.clone(),
                            first_span: existing.span,
                            second_span: *span,
                        });
                    }
                    imports.insert(
                        key,
                        ImportBinding {
                            module: path.clone(),
                            span: *span,
                        },
                    );
                }
            }
            Item::Module(_)
            | Item::Protocol(_)
            | Item::ProtocolImpl(_)
            | Item::MacroCall { .. } => {}
        }
    }

    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                let qualified_name =
                    QualifiedName::in_module(module_name.clone(), def.name.clone()).dotted();
                let mut new_def = def.clone();
                new_def.name = qualified_name;
                for clause in &mut new_def.clauses {
                    let mut intro = pattern_intro(&clause.params);
                    rewrite_expr(
                        &mut clause.body,
                        &module_path,
                        &siblings,
                        &mut intro,
                        module_paths,
                        &aliases,
                        &imports,
                    );
                    if let Some(g) = &mut clause.guard {
                        rewrite_expr(
                            g,
                            &module_path,
                            &siblings,
                            &mut intro,
                            module_paths,
                            &aliases,
                            &imports,
                        );
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(inner) => {
                flatten_module(
                    inner,
                    Some(&module_name),
                    out,
                    module_paths,
                    module_interfaces,
                    module_macros,
                )?;
            }
            Item::Alias { .. } | Item::Import { .. } => {}
            Item::MacroCall {
                name,
                name_span,
                args,
                parent_module: _,
                span,
            } => {
                let mut new_args: Vec<Spanned<Expr>> = args.clone();
                for a in &mut new_args {
                    let mut intro: HashSet<String> = HashSet::new();
                    rewrite_expr(
                        a,
                        &module_path,
                        &siblings,
                        &mut intro,
                        module_paths,
                        &aliases,
                        &imports,
                    );
                }
                out.push(Rc::new(Item::MacroCall {
                    name: name.clone(),
                    name_span: *name_span,
                    args: new_args,
                    parent_module: Some(module_path.clone()),
                    span: *span,
                }));
            }
            Item::Protocol(_) => {}
            Item::ProtocolImpl(protocol_impl) => flatten_protocol_impl(
                protocol_impl,
                Some(&module_name),
                out,
                module_paths,
                &aliases,
                &imports,
            )?,
        }
    }
    Ok(())
}

fn flatten_protocol_impl(
    protocol_impl: &ProtocolImplDef,
    parent_path: Option<&ModuleName>,
    out: &mut Vec<Rc<Item>>,
    module_paths: &HashSet<String>,
    aliases: &HashMap<String, String>,
    imports: &ImportMap,
) -> Result<(), ResolveError> {
    let impl_module = qualify_module_child(parent_path, &protocol_impl.target.path);
    let module_path = impl_module.dotted();
    let siblings = protocol_impl
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Fn(def) => Some(def.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    for item in &protocol_impl.items {
        if let Item::Fn(def) = &**item {
            let qualified_name =
                QualifiedName::in_module(impl_module.clone(), def.name.clone()).dotted();
            let mut new_def = def.clone();
            new_def.name = qualified_name;
            for clause in &mut new_def.clauses {
                let mut intro = pattern_intro(&clause.params);
                rewrite_expr(
                    &mut clause.body,
                    &module_path,
                    &siblings,
                    &mut intro,
                    module_paths,
                    aliases,
                    imports,
                );
                if let Some(g) = &mut clause.guard {
                    rewrite_expr(
                        g,
                        &module_path,
                        &siblings,
                        &mut intro,
                        module_paths,
                        aliases,
                        imports,
                    );
                }
            }
            out.push(Rc::new(Item::Fn(new_def)));
        }
    }
    Ok(())
}

fn importable_exports(
    interface: &ModuleInterface,
    local_macros: Option<&HashSet<(String, usize)>>,
) -> HashSet<(String, usize)> {
    let mut out: HashSet<(String, usize)> = interface
        .exports
        .iter()
        .map(|export| ((export.name.clone(), export.arity), export))
        .map(|(key, _)| key)
        .collect();
    if let Some(macros) = local_macros {
        out.extend(macros.iter().cloned());
    }
    out
}

fn validate_import_filter(
    module: &ModuleName,
    filter: &[(String, usize)],
    target_exports: &HashSet<(String, usize)>,
    span: Span,
) -> Result<(), ResolveError> {
    for (name, arity) in filter {
        if !target_exports.contains(&(name.clone(), *arity)) {
            return Err(ResolveError::UnknownImport {
                export: ExportKey::new(module.clone(), name.clone(), *arity),
                span,
            });
        }
    }
    Ok(())
}

fn pattern_intro(params: &[Spanned<Pattern>]) -> HashSet<String> {
    let mut s = HashSet::new();
    for p in params {
        collect_pattern_vars(&p.node, &mut s);
    }
    s
}

fn collect_pattern_vars(p: &Pattern, out: &mut HashSet<String>) {
    match p {
        Pattern::Var(n) => {
            out.insert(n.clone());
        }
        Pattern::As(n, inner) => {
            out.insert(n.clone());
            collect_pattern_vars(&inner.node, out);
        }
        Pattern::Tuple(xs) => {
            for x in xs {
                collect_pattern_vars(&x.node, out);
            }
        }
        Pattern::List(xs, tail) => {
            for x in xs {
                collect_pattern_vars(&x.node, out);
            }
            if let Some(t) = tail {
                collect_pattern_vars(&t.node, out);
            }
        }
        Pattern::Map(pairs) => {
            for (_, v) in pairs {
                collect_pattern_vars(&v.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for f in fields {
                collect_pattern_vars(&f.value.node, out);
            }
        }
        _ => {}
    }
}

fn rewrite_expr(
    e: &mut Spanned<Expr>,
    module_path: &str,
    siblings: &HashSet<String>,
    intro: &mut HashSet<String>,
    module_paths: &HashSet<String>,
    aliases: &HashMap<String, String>,
    imports: &ImportMap,
) {
    match &mut e.node {
        Expr::Var(n) => {
            if siblings.contains(n) && !intro.contains(n) {
                *n = format!("{}.{}", module_path, n);
            }
        }
        // fz-swt.5: `&name/arity` follows the same name-resolution rules
        // as a bare call target — sibling rewriting, then import
        // resolution, then alias-qualified paths. We treat the `name`
        // string identically: if it's a bare ident matching a sibling,
        // prefix the module path; if it's a bare ident matching an
        // arity-specific import, prefix the import target; if it's a
        // dotted path with a leading alias, expand the alias.
        Expr::FnRef { name, arity } => {
            // Bare names get sibling / import treatment.
            if !name.contains('.') && !intro.contains(name) {
                if siblings.contains(name) {
                    *name = format!("{}.{}", module_path, name);
                } else if let Some(target) = imports.get(&(name.clone(), *arity)) {
                    *name = format!("{}.{}", target.module, name);
                }
            } else if name.contains('.') {
                // Dotted: split, expand leading alias if present.
                let parts: Vec<&str> = name.split('.').collect();
                if let Some(full) = aliases.get(parts[0]) {
                    let rest = parts[1..].join(".");
                    *name = if rest.is_empty() {
                        full.clone()
                    } else {
                        format!("{}.{}", full, rest)
                    };
                }
            }
        }
        Expr::Call(callee, args) => {
            if let Some(q) = qualify_callee(callee, intro, module_path, module_paths, aliases) {
                callee.node = Expr::Var(q);
            } else if let Expr::Var(n) = &callee.node
                && !intro.contains(n)
                && !siblings.contains(n)
                && let Some(target) = imports.get(&(n.clone(), args.len()))
            {
                callee.node = Expr::Var(format!("{}.{}", target.module, n));
            }
            rewrite_expr(
                callee,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            for a in args {
                rewrite_expr(
                    a,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::List(xs, tail) => {
            for x in xs {
                rewrite_expr(
                    x,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
            if let Some(t) = tail {
                rewrite_expr(
                    t,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                rewrite_expr(
                    x,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Bitstring(fields) => {
            for f in fields {
                rewrite_expr(
                    &mut f.value,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                rewrite_expr(
                    k,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
                rewrite_expr(
                    v,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::MapUpdate(m, pairs) => {
            rewrite_expr(
                m,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            for (k, v) in pairs {
                rewrite_expr(
                    k,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
                rewrite_expr(
                    v,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Index(o, i) => {
            rewrite_expr(
                o,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            rewrite_expr(
                i,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
        }
        Expr::BinOp(_, l, r) => {
            rewrite_expr(
                l,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            rewrite_expr(
                r,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
        }
        Expr::UnOp(_, x) | Expr::Ascribe(x, _) => rewrite_expr(
            x,
            module_path,
            siblings,
            intro,
            module_paths,
            aliases,
            imports,
        ),
        Expr::If(c, t, els) => {
            rewrite_expr(
                c,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            rewrite_expr(
                t,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            if let Some(e) = els {
                rewrite_expr(
                    e,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Case(scr, arms) => {
            if let Some(scr) = scr {
                rewrite_expr(
                    scr,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
            for arm in arms {
                let mut nested = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut nested);
                if let Some(g) = &mut arm.guard {
                    rewrite_expr(
                        g,
                        module_path,
                        siblings,
                        &mut nested,
                        module_paths,
                        aliases,
                        imports,
                    );
                }
                rewrite_expr(
                    &mut arm.body,
                    module_path,
                    siblings,
                    &mut nested,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                rewrite_expr(
                    c,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
                rewrite_expr(
                    b,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            let mut nested = intro.clone();
            for b in bindings {
                match b {
                    WithBinding::Match(p, e) => {
                        rewrite_expr(
                            e,
                            module_path,
                            siblings,
                            &mut nested,
                            module_paths,
                            aliases,
                            imports,
                        );
                        collect_pattern_vars(&p.node, &mut nested);
                    }
                    WithBinding::Bare(e) => rewrite_expr(
                        e,
                        module_path,
                        siblings,
                        &mut nested,
                        module_paths,
                        aliases,
                        imports,
                    ),
                }
            }
            rewrite_expr(
                body,
                module_path,
                siblings,
                &mut nested,
                module_paths,
                aliases,
                imports,
            );
            for arm in else_clauses {
                let mut a_intro = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut a_intro);
                if let Some(g) = &mut arm.guard {
                    rewrite_expr(
                        g,
                        module_path,
                        siblings,
                        &mut a_intro,
                        module_paths,
                        aliases,
                        imports,
                    );
                }
                rewrite_expr(
                    &mut arm.body,
                    module_path,
                    siblings,
                    &mut a_intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Match(pat, rhs) => {
            rewrite_expr(
                rhs,
                module_path,
                siblings,
                intro,
                module_paths,
                aliases,
                imports,
            );
            collect_pattern_vars(&pat.node, intro);
        }
        Expr::Lambda(params, body) => {
            let mut nested = intro.clone();
            for p in params {
                collect_pattern_vars(&p.node, &mut nested);
            }
            rewrite_expr(
                body,
                module_path,
                siblings,
                &mut nested,
                module_paths,
                aliases,
                imports,
            );
        }
        Expr::Quote(inner) => rewrite_expr(
            inner,
            module_path,
            siblings,
            intro,
            module_paths,
            aliases,
            imports,
        ),
        Expr::Unquote(inner) => rewrite_expr(
            inner,
            module_path,
            siblings,
            intro,
            module_paths,
            aliases,
            imports,
        ),
        // fz-5vj — receive: each clause introduces pattern vars into a
        // nested scope (bound names from the pattern, including the names
        // shadowed by `^name` pins which are *not* binding sites — they
        // reference the outer scope). After parses in the outer scope
        // (no pattern), but its body sees no bound vars either.
        Expr::Receive { clauses, after } => {
            for arm in clauses {
                let mut nested = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut nested);
                if let Some(g) = &mut arm.guard {
                    rewrite_expr(
                        g,
                        module_path,
                        siblings,
                        &mut nested,
                        module_paths,
                        aliases,
                        imports,
                    );
                }
                rewrite_expr(
                    &mut arm.body,
                    module_path,
                    siblings,
                    &mut nested,
                    module_paths,
                    aliases,
                    imports,
                );
            }
            if let Some(af) = after {
                rewrite_expr(
                    &mut af.timeout,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
                rewrite_expr(
                    &mut af.body,
                    module_path,
                    siblings,
                    intro,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil => {}
    }
}

fn qualify_callee(
    callee: &Spanned<Expr>,
    intro: &HashSet<String>,
    module_path: &str,
    module_paths: &HashSet<String>,
    aliases: &HashMap<String, String>,
) -> Option<String> {
    let mut path: Vec<String> = Vec::new();
    let mut cur = &callee.node;
    loop {
        match cur {
            Expr::Index(target, key) => {
                let member = match &key.node {
                    Expr::Atom(n) => n.clone(),
                    _ => return None,
                };
                path.push(member);
                cur = &target.node;
            }
            Expr::Var(m) if is_upper(m) && !intro.contains(m) => {
                if path.is_empty() {
                    return None;
                }
                path.push(m.clone());
                path.reverse();
                let leading = &path[0];
                if let Some(full) = aliases.get(leading) {
                    let rest: String = path[1..].join(".");
                    return Some(if rest.is_empty() {
                        full.clone()
                    } else {
                        format!("{}.{}", full, rest)
                    });
                }
                if !module_path.is_empty() {
                    let candidate = format!("{}.{}", module_path, leading);
                    if module_paths.contains(&candidate) {
                        let rest: String = path[1..].join(".");
                        return Some(format!("{}.{}", candidate, rest));
                    }
                }
                let module = path[..path.len() - 1].join(".");
                if module_paths.contains(&module) {
                    return Some(path.join("."));
                }
                return None;
            }
            _ => return None,
        }
    }
}

fn is_upper(s: &str) -> bool {
    s.chars()
        .next()
        .map(|c| c.is_ascii_uppercase())
        .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::types::Types;

    fn parse(src: &str) -> Program {
        let toks = Lexer::new(src).tokenize().expect("lex");
        Parser::new(toks).parse_program().expect("parse")
    }

    fn flatten(src: &str) -> Program {
        let mut ct = crate::types::ConcreteTypes;
        flatten_modules(&mut ct, parse(src)).expect("flatten")
    }

    fn fn_names(p: &Program) -> Vec<String> {
        p.items
            .iter()
            .filter_map(|it| match &**it {
                Item::Fn(d) => Some(d.name.clone()),
                _ => None,
            })
            .collect()
    }

    fn callee_name(body: &Spanned<Expr>) -> &str {
        match &body.node {
            Expr::Call(callee, _) => match &callee.node {
                Expr::Var(n) => n.as_str(),
                other => panic!("expected Var callee, got {:?}", other),
            },
            other => panic!("expected Call, got {:?}", other),
        }
    }

    #[test]
    fn module_qualifies_fn_names() {
        let p = flatten("defmodule M do; fn f(x), do: x + 1 end");
        assert_eq!(fn_names(&p), vec!["M.f"]);
    }

    #[test]
    fn ungrouped_fns_keep_bare_names() {
        let p = flatten("fn helper(x), do: x + 1");
        assert_eq!(fn_names(&p), vec!["helper"]);
    }

    #[test]
    fn sibling_call_in_module_rewrites() {
        let p = flatten(
            r#"
defmodule M do
  fn helper(x), do: x + 1
  fn use_helper(x), do: helper(x)
end
"#,
        );
        let names = fn_names(&p);
        assert!(names.contains(&"M.helper".to_string()));
        assert!(names.contains(&"M.use_helper".to_string()));
        let use_helper = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "M.use_helper" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&use_helper.clauses[0].body), "M.helper");
    }

    #[test]
    fn cross_module_call_rewrites() {
        let p = flatten(
            r#"
defmodule A do
  fn ping(), do: 1
end
defmodule B do
  fn caller(), do: A.ping()
end
"#,
        );
        let caller = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "B.caller" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&caller.clauses[0].body), "A.ping");
    }

    #[test]
    fn local_param_does_not_qualify() {
        let p = flatten(
            r#"
defmodule M do
  fn helper(x), do: x
  fn shadow(helper), do: helper
end
"#,
        );
        let shadow = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "M.shadow" => Some(d),
                _ => None,
            })
            .unwrap();
        match &shadow.clauses[0].body.node {
            Expr::Var(n) => assert_eq!(n, "helper"),
            other => panic!("expected Var('helper'), got {:?}", other),
        }
    }

    #[test]
    fn nested_module_qualifies_with_dotted_path() {
        let p = flatten(
            r#"
defmodule A do
  defmodule B do
    fn f(x), do: x + 1
  end
end
"#,
        );
        assert_eq!(fn_names(&p), vec!["A.B.f"]);
    }

    #[test]
    fn nested_call_from_outside_rewrites() {
        let p = flatten(
            r#"
defmodule A do
  defmodule B do
    fn f(x), do: x
  end
end
fn main() do A.B.f(99) end
"#,
        );
        let main_fn = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&main_fn.clauses[0].body), "A.B.f");
    }

    #[test]
    fn alias_inside_module_resolves() {
        let p = flatten(
            r#"
defmodule Long do
  defmodule Path do
    fn f(x), do: x
  end
end
defmodule User do
  alias Long.Path
  fn caller(), do: Path.f(7)
end
"#,
        );
        let caller = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.caller" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&caller.clauses[0].body), "Long.Path.f");
    }

    #[test]
    fn alias_with_as_renames() {
        let p = flatten(
            r#"
defmodule Long do
  defmodule Path do
    fn f(x), do: x
  end
end
defmodule User do
  alias Long.Path, as: P
  fn caller(), do: P.f(9)
end
"#,
        );
        let caller = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.caller" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&caller.clauses[0].body), "Long.Path.f");
    }

    #[test]
    fn import_unfiltered_pulls_all_names() {
        let p = flatten(
            r#"
defmodule Math do
  fn add(x, y), do: x + y
  fn mul(x, y), do: x * y
end
defmodule User do
  import Math
  fn run(x, y), do: add(x, y)
end
"#,
        );
        let run = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.run" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&run.clauses[0].body), "Math.add");
    }

    #[test]
    fn import_only_filters_names() {
        let p = flatten(
            r#"
defmodule Math do
  fn add(x, y), do: x + y
  fn mul(x, y), do: x * y
end
defmodule User do
  import Math, only: [add: 2]
  fn r1(x, y), do: add(x, y)
  fn r2(x, y), do: mul(x, y)
end
"#,
        );
        let r1 = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.r1" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&r1.clauses[0].body), "Math.add");
        let r2 = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.r2" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&r2.clauses[0].body), "mul");
    }

    #[test]
    fn local_fn_shadows_import() {
        let p = flatten(
            r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  import Math
  fn add(x, y), do: x - y
  fn use_local(), do: add(10, 4)
end
"#,
        );
        let use_local = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.use_local" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&use_local.clauses[0].body), "User.add");
    }

    #[test]
    fn import_unknown_module_errors() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule User do
  import Missing
  fn run(), do: nil
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_UNKNOWN_MODULE);
        assert_eq!(d.message, "module `Missing` is not defined");
        assert_ne!(d.primary.span, Span::DUMMY);
    }

    #[test]
    fn alias_unknown_module_errors() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule User do
  alias Missing.Path
  fn run(), do: nil
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_UNKNOWN_MODULE);
        assert_eq!(d.message, "module `Missing.Path` is not defined");
    }

    #[test]
    fn import_unknown_arity_errors() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  import Math, only: [add: 1]
  fn run(x), do: add(x)
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_UNKNOWN_IMPORT);
        assert_eq!(d.message, "module `Math` does not export `add/1`");
    }

    #[test]
    fn import_except_unknown_arity_errors() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  import Math, except: [add: 1]
  fn run(x, y), do: add(x, y)
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_UNKNOWN_IMPORT);
        assert_eq!(d.message, "module `Math` does not export `add/1`");
    }

    #[test]
    fn import_resolves_from_external_interface_table() {
        let mut ct = crate::types::ConcreteTypes;
        let math = ModuleName::from_segments(vec!["Math".to_string()]);
        let mut interfaces = InterfaceTable::new();
        interfaces.insert(
            math.clone(),
            ModuleInterface {
                name: math,
                abi_version: crate::modules::interface::FZ_INTERFACE_ABI_VERSION,
                imports: Vec::new(),
                exports: vec![crate::modules::interface::InterfaceFn {
                    name: "add".to_string(),
                    arity: 2,
                    spec: None,
                    name_span: Span::DUMMY,
                }],
                types: Vec::new(),
                protocols: Vec::new(),
                protocol_impls: Vec::new(),
                docs: None,
                fingerprint_inputs: Vec::new(),
            },
        );
        let p = flatten_modules_with_interface_table(
            &mut ct,
            parse(
                r#"
defmodule User do
  import Math, only: [add: 2]
  fn run(x, y), do: add(x, y)
end
"#,
            ),
            interfaces,
        )
        .expect("flatten");
        let run = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.run" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&run.clauses[0].body), "Math.add");
    }

    #[test]
    fn import_resolves_from_runtime_library_interfaces_by_default() {
        let mut ct = crate::types::ConcreteTypes;
        let p = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#,
            ),
        )
        .expect("flatten");

        let run = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.run" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&run.clauses[0].body), "Utf8.valid?");
        assert!(
            !p.module_interfaces
                .contains_key(&ModuleName::from_segments(vec!["Utf8".to_string()]))
        );
    }

    #[test]
    fn alias_resolves_from_runtime_library_interfaces_on_demand() {
        let mut ct = crate::types::ConcreteTypes;
        let p = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule User do
  alias Utf8, as: U
  fn run(bytes), do: U.valid?(bytes)
end
"#,
            ),
        )
        .expect("flatten");

        let run = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.run" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&run.clauses[0].body), "Utf8.valid?");
        assert!(
            p.external_module_interfaces
                .contains_key(&ModuleName::from_segments(vec!["Utf8".to_string()]))
        );
        assert!(
            !p.external_module_interfaces
                .contains_key(&ModuleName::from_segments(vec!["Process".to_string()]))
        );
    }

    #[test]
    fn unrequested_runtime_module_is_not_a_visible_module_path() {
        let p = flatten(
            r#"
defmodule User do
  fn run(bytes), do: Utf8.valid?(bytes)
end
"#,
        );
        let run = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.run" => Some(d),
                _ => None,
            })
            .unwrap();
        match &run.clauses[0].body.node {
            Expr::Call(callee, _) => {
                assert!(
                    !matches!(&callee.node, Expr::Var(name) if name == "Utf8.valid?"),
                    "unimported runtime module call was rewritten as an ambient module call"
                );
            }
            other => panic!("expected call, got {:?}", other),
        }
        assert!(p.external_module_interfaces.is_empty());
    }

    #[test]
    fn import_non_exported_name_errors() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule Math do
  fn visible(), do: 1
end
defmodule User do
  import Math, only: [hidden: 0]
  fn run(), do: hidden()
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_UNKNOWN_IMPORT);
        assert_eq!(d.message, "module `Math` does not export `hidden/0`");
    }

    #[test]
    fn conflicting_imports_error() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule A do
  fn f(), do: 1
end
defmodule B do
  fn f(), do: 2
end
defmodule User do
  import A
  import B
  fn run(), do: f()
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_CONFLICTING_IMPORT);
        assert_eq!(
            d.message,
            "import `f/0` from module `B` conflicts with existing import from module `A`"
        );
        assert_eq!(d.secondaries.len(), 1);
    }

    #[test]
    fn duplicate_same_module_import_is_idempotent() {
        let p = flatten(
            r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  import Math, only: [add: 2]
  import Math, only: [add: 2]
  fn run(x, y), do: add(x, y)
end
"#,
        );
        let run = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "User.run" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&run.clauses[0].body), "Math.add");
    }

    #[test]
    fn top_level_import_rewrites_top_level_functions() {
        let p = flatten(
            r#"
defmodule Math do
  fn add(x, y), do: x + y
end
import Math, only: [add: 2]
fn main(), do: add(20, 22)
"#,
        );
        let main = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&main.clauses[0].body), "Math.add");
    }

    #[test]
    fn top_level_alias_rewrites_top_level_functions() {
        let p = flatten(
            r#"
defmodule Outer do
  defmodule Inner do
    fn value(), do: 42
  end
end
alias Outer.Inner, as: I
fn main(), do: I.value()
"#,
        );
        let main = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&main.clauses[0].body), "Outer.Inner.value");
    }

    #[test]
    fn duplicate_module_diag_has_primary_and_first_definition_spans() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defmodule M do
  fn one(), do: 1
end
defmodule M do
  fn two(), do: 2
end
"#,
            ),
        )
        .unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_DUPLICATE_MODULE);
        assert_ne!(d.primary.span, Span::DUMMY);
        assert_eq!(d.secondaries.len(), 1);
        assert_ne!(d.secondaries[0].span, Span::DUMMY);
    }

    #[test]
    fn duplicate_export_diag_names_module_function_and_arity() {
        let parsed = parse(
            r#"
fn f(x), do: x
fn g(y), do: y
"#,
        );
        let mut defs: Vec<FnDef> = parsed
            .items
            .iter()
            .filter_map(|item| match &**item {
                Item::Fn(def) => Some(def.clone()),
                _ => None,
            })
            .collect();
        defs[1].name = "f".to_string();
        let module = ModuleDef {
            name: "M".to_string(),
            name_span: Span::DUMMY,
            items: vec![
                Rc::new(Item::Fn(defs[0].clone())),
                Rc::new(Item::Fn(defs[1].clone())),
            ],
            attrs: Vec::new(),
            span: Span::DUMMY,
        };
        let prog = Program {
            items: vec![Rc::new(Item::Module(module))],
            module_interfaces: Default::default(),
            ..Program::default()
        };
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(&mut ct, prog).unwrap_err();
        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_DUPLICATE_EXPORT);
        assert_eq!(d.message, "export `M.f/1` is defined more than once");
        assert_ne!(d.primary.span, Span::DUMMY);
        assert_eq!(d.secondaries.len(), 1);
    }

    #[test]
    fn moduledoc_and_doc_parse() {
        let prog = parse(
            r#"
defmodule Greeter do
  @moduledoc "Greets people."

  @doc "Says hi."
  fn hi(name), do: name
end
"#,
        );
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        assert_eq!(m.moduledoc(), Some("Greets people."));
        let hi = m
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "hi" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(hi.doc(), Some("Says hi."));
    }

    #[test]
    fn type_alias_attribute_parses_with_module() {
        // .31.3 — `@type` inside a defmodule attaches a TypeAlias to
        // the module's attrs. The body tokens are captured for later
        // resolution by `type_expr::build_module_type_env`.
        let prog = parse(
            r#"
defmodule M do
  @type id :: integer
  @type pair :: {id, id}
  @type keyword(t) :: [{atom, t}]
  fn one(), do: 1
end
"#,
        );
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        let aliases: Vec<&str> = m
            .attrs
            .iter()
            .filter_map(|a| match a {
                Attribute::TypeAlias(d) => Some(d.name.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(aliases, vec!["id", "pair", "keyword"]);
        let keyword = m
            .attrs
            .iter()
            .find_map(|a| match a {
                Attribute::TypeAlias(d) if d.name == "keyword" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(keyword.params, vec!["t"]);
        // Build env and verify resolution end-to-end.
        let mut ct = crate::types::ConcreteTypes;
        let env = crate::type_expr::build_module_type_env(&mut ct, &m.attrs).unwrap();
        let int = ct.int();
        assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
        let expected = ct.tuple(&[int.clone(), int]);
        assert!(ct.is_equivalent(env.get("pair").unwrap(), &expected));
        let keyword_int = crate::type_expr::parse_type_expr(
            &mut ct,
            &crate::lexer::Lexer::new("keyword(integer)")
                .tokenize()
                .unwrap(),
            &env,
        )
        .unwrap()
        .0;
        let atom = ct.atom();
        let int = ct.int();
        let pair = ct.tuple(&[atom, int]);
        let expected_keyword = ct.list(pair);
        assert!(ct.is_equivalent(&keyword_int, &expected_keyword));
    }

    #[test]
    fn module_type_aliases_can_use_runtime_root_aliases() {
        let prog = parse(
            r#"
defmodule M do
  @type opts :: keyword(integer)
  @spec run(opts) :: nil
  fn run(_), do: nil
end
"#,
        );
        let mut ct = crate::types::ConcreteTypes;
        let flat = flatten_modules(&mut ct, prog).expect("flatten");
        let env = flat.module_type_envs.get("M").expect("module env");
        let opts = env.get("opts").expect("opts alias");
        let atom = ct.atom();
        let int = ct.int();
        let pair = ct.tuple(&[atom, int]);
        let expected = ct.list(pair);
        assert!(ct.is_equivalent(opts, &expected));
    }

    #[test]
    fn module_specs_can_use_runtime_root_aliases_without_local_types() {
        let prog = parse(
            r#"
defmodule M do
  @spec run(keyword(integer)) :: nil
  fn run(_), do: nil
end
"#,
        );
        let mut ct = crate::types::ConcreteTypes;
        let flat = flatten_modules(&mut ct, prog).expect("flatten");
        let def = flat
            .items
            .iter()
            .find_map(|item| match &**item {
                Item::Fn(def) if def.name == "M.run" => Some(def),
                _ => None,
            })
            .expect("M.run");
        let spec = def
            .attrs
            .iter()
            .find_map(|attr| match attr {
                Attribute::Spec(spec) => Some(spec),
                _ => None,
            })
            .expect("spec");
        let env = flat.module_type_envs.get("M").expect("module env");
        let resolved =
            crate::type_expr::resolve_spec_decl(&mut ct, spec, env).expect("resolve spec");
        let atom = ct.atom();
        let int = ct.int();
        let pair = ct.tuple(&[atom, int]);
        let expected = ct.list(pair);
        assert!(ct.is_equivalent(&resolved.params[0], &expected));
    }

    // ----- fz-ul4.31.4: @spec parser + AST attachment -----

    #[test]
    fn spec_attribute_parses_and_attaches_to_fn() {
        let prog = parse(
            r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#,
        );
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        let add1 = m
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "add1" => Some(d),
                _ => None,
            })
            .unwrap();
        let spec = add1
            .attrs
            .iter()
            .find_map(|a| match a {
                Attribute::Spec(s) => Some(s),
                _ => None,
            })
            .expect("@spec attached to fn");
        assert_eq!(spec.name, "add1");
        assert_eq!(spec.param_body_tokens.len(), 1);
        // Resolve and verify types.
        let env = crate::type_expr::ModuleTypeEnv::new();
        use crate::types::Types;
        let mut ct = crate::types::ConcreteTypes;
        let resolved = crate::type_expr::resolve_spec_decl(&mut ct, spec, &env).unwrap();
        let int = ct.int();
        assert!(ct.is_equivalent(&resolved.params[0], &int));
        assert!(ct.is_equivalent(&resolved.result, &int));
    }

    #[test]
    fn spec_zero_arity_parses() {
        let prog = parse(
            r#"
defmodule M do
  @spec one() :: integer
  fn one(), do: 1
end
"#,
        );
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        let one = m
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "one" => Some(d),
                _ => None,
            })
            .unwrap();
        let spec = one
            .attrs
            .iter()
            .find_map(|a| match a {
                Attribute::Spec(s) => Some(s),
                _ => None,
            })
            .expect("@spec attached to zero-arity fn");
        assert_eq!(spec.param_body_tokens.len(), 0);
    }

    #[test]
    fn spec_arity_mismatch_errors_at_parse_time() {
        let toks = crate::lexer::Lexer::new(
            "defmodule M do\n\
              @spec add1(integer, integer) :: integer\n\
              fn add1(n), do: n + 1\n\
            end\n",
        )
        .tokenize()
        .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err(), "arity mismatch must error");
        let msg = format!("{:?}", r.unwrap_err());
        assert!(msg.contains("arity"), "expected arity diag, got: {}", msg);
    }

    #[test]
    fn spec_name_mismatch_errors_at_parse_time() {
        let toks = crate::lexer::Lexer::new(
            "defmodule M do\n\
              @spec other(integer) :: integer\n\
              fn add1(n), do: n + 1\n\
            end\n",
        )
        .tokenize()
        .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err(), "name mismatch must error");
        let msg = format!("{:?}", r.unwrap_err());
        assert!(
            msg.contains("doesn't match"),
            "expected name-mismatch diag, got: {}",
            msg
        );
    }

    #[test]
    fn spec_without_following_fn_errors() {
        // @spec at the end of a module with no fn following it.
        let toks = crate::lexer::Lexer::new(
            "defmodule M do\n\
              @spec lonely(integer) :: integer\n\
            end\n",
        )
        .tokenize()
        .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err(), "spec without fn must error");
    }

    #[test]
    fn multiple_spec_on_one_fn_errors() {
        let toks = crate::lexer::Lexer::new(
            "defmodule M do\n\
              @spec add1(integer) :: integer\n\
              @spec add1(float) :: float\n\
              fn add1(n), do: n + 1\n\
            end\n",
        )
        .tokenize()
        .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err(), "duplicate @spec must error");
        let msg = format!("{:?}", r.unwrap_err());
        assert!(
            msg.contains("multiple"),
            "expected multiple-spec diag, got: {}",
            msg
        );
    }

    #[test]
    fn spec_unknown_type_errors_at_resolve_time() {
        let prog = parse(
            r#"
defmodule M do
  @spec add1(unknown_thing) :: integer
  fn add1(n), do: n + 1
end
"#,
        );
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        let add1 = m
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "add1" => Some(d),
                _ => None,
            })
            .unwrap();
        let spec = add1
            .attrs
            .iter()
            .find_map(|a| match a {
                Attribute::Spec(s) => Some(s),
                _ => None,
            })
            .expect("@spec parsed");
        let mut ct = crate::types::ConcreteTypes;
        let env = crate::type_expr::build_module_type_env(&mut ct, &m.attrs).unwrap();
        let r = crate::type_expr::resolve_spec_decl(&mut ct, spec, &env);
        assert!(r.is_err(), "unknown type must error on resolve");
        let e = r.unwrap_err();
        assert!(
            e.msg.contains("unknown type name"),
            "expected unknown-name diag, got: {}",
            e.msg
        );
    }

    #[test]
    fn spec_resolves_against_module_type_env() {
        let prog = parse(
            r#"
defmodule M do
  @type id :: integer
  @spec lookup(id) :: id
  fn lookup(x), do: x
end
"#,
        );
        let m = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Module(m) => Some(m),
                _ => None,
            })
            .unwrap();
        let lookup = m
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "lookup" => Some(d),
                _ => None,
            })
            .unwrap();
        let spec = lookup
            .attrs
            .iter()
            .find_map(|a| match a {
                Attribute::Spec(s) => Some(s),
                _ => None,
            })
            .expect("@spec parsed");
        use crate::types::Types;
        let mut ct = crate::types::ConcreteTypes;
        let env = crate::type_expr::build_module_type_env(&mut ct, &m.attrs).unwrap();
        let resolved = crate::type_expr::resolve_spec_decl(&mut ct, spec, &env).unwrap();
        let int = ct.int();
        assert!(ct.is_equivalent(&resolved.params[0], &int));
        assert!(ct.is_equivalent(&resolved.result, &int));
    }

    #[test]
    fn type_alias_at_top_level_errors() {
        let toks = crate::lexer::Lexer::new("@type id :: integer\nfn main(), do: nil")
            .tokenize()
            .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err(), "@type at top level must error; got {:?}", r);
    }

    #[test]
    fn unknown_attribute_errors() {
        let toks = crate::lexer::Lexer::new("@bogus \"x\"\nfn main(), do: nil")
            .tokenize()
            .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err());
    }

    #[test]
    fn moduledoc_at_top_level_errors() {
        let toks = crate::lexer::Lexer::new("@moduledoc \"x\"\nfn main(), do: nil")
            .tokenize()
            .unwrap();
        let r = Parser::new(toks).parse_program();
        assert!(r.is_err());
    }

    #[test]
    fn doc_survives_flatten() {
        let p = flatten(
            r#"
defmodule M do
  @doc "doubles"
  fn d(x), do: x * 2
end
"#,
        );
        let d = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "M.d" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(d.doc(), Some("doubles"));
    }

    #[test]
    fn outer_sibling_not_shadowed_by_inner_same_name() {
        let p = flatten(
            r#"
defmodule A do
  fn f(x), do: x
  fn caller(x), do: f(x)
  defmodule B do
    fn f(x), do: x + 100
  end
end
"#,
        );
        let names = fn_names(&p);
        assert!(names.contains(&"A.f".to_string()));
        assert!(names.contains(&"A.B.f".to_string()));
        let caller = p
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "A.caller" => Some(d),
                _ => None,
            })
            .unwrap();
        assert_eq!(callee_name(&caller.clauses[0].body), "A.f");
    }

    // ----- .20.3: span preservation through qualification -----

    /// Sibling-fn rewriting (`f` → `M.f` inside module M) must NOT alter
    /// the source span on the rewritten Var. The renamed reference still
    /// occupies the same byte range in the user's source.
    #[test]
    fn sibling_rewrite_preserves_var_span() {
        let src = "defmodule M do\n  fn f(x), do: x\n  fn g(x), do: f(x)\nend";
        let pre = parse(src);

        // Find the `f` inside `g`'s body BEFORE flattening.
        let pre_span = {
            let Item::Module(m) = &*pre.items[0] else {
                panic!()
            };
            let Item::Fn(g) = &*m
                .items
                .iter()
                .find_map(|it| match &**it {
                    Item::Fn(d) if d.name == "g" => Some(it.clone()),
                    _ => None,
                })
                .unwrap()
            else {
                panic!()
            };
            // body is Call(callee=Var("f"), [Var("x")])
            let body = &g.clauses[0].body;
            let Expr::Call(callee, _) = &body.node else {
                panic!()
            };
            callee.span
        };

        let mut ct = crate::types::ConcreteTypes;
        let post = flatten_modules(&mut ct, pre).expect("flatten");
        let g = post
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "M.g" => Some(d),
                _ => None,
            })
            .unwrap();
        // The bare `f` has been rewritten to `M.f`; the callee span should
        // still point at the original `f` token in source.
        let Expr::Call(callee, _) = &g.clauses[0].body.node else {
            panic!()
        };
        match &callee.node {
            Expr::Var(n) => assert_eq!(n, "M.f"),
            other => panic!("expected Var('M.f'), got {:?}", other),
        }
        assert_eq!(
            callee.span, pre_span,
            "callee span should be preserved through sibling rewrite"
        );
    }

    /// Cross-module rewriting: `M.helper(x)` (parsed as `Index(Var(M),
    /// Atom("helper"))`) becomes `Var("M.helper")`. The resulting Var's
    /// span should still cover the original source `M.helper` region.
    #[test]
    fn cross_module_rewrite_preserves_call_span() {
        let src = r#"
defmodule M do
  fn helper(x), do: x + 1
end
defmodule N do
  fn use_it(), do: M.helper(7)
end
"#;
        let pre = parse(src);
        let pre_call_span = {
            let n_mod = pre
                .items
                .iter()
                .find_map(|it| match &**it {
                    Item::Module(m) if m.name == "N" => Some(m.clone()),
                    _ => None,
                })
                .unwrap();
            let Item::Fn(u) = &*n_mod
                .items
                .iter()
                .find_map(|it| match &**it {
                    Item::Fn(d) if d.name == "use_it" => Some(it.clone()),
                    _ => None,
                })
                .unwrap()
            else {
                panic!()
            };
            let Expr::Call(callee, _) = &u.clauses[0].body.node else {
                panic!()
            };
            callee.span
        };

        let mut ct = crate::types::ConcreteTypes;
        let post = flatten_modules(&mut ct, pre).expect("flatten");
        let u = post
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "N.use_it" => Some(d),
                _ => None,
            })
            .unwrap();
        let Expr::Call(callee, _) = &u.clauses[0].body.node else {
            panic!()
        };
        match &callee.node {
            Expr::Var(n) => assert_eq!(n, "M.helper"),
            other => panic!("expected Var('M.helper'), got {:?}", other),
        }
        assert_eq!(
            callee.span, pre_call_span,
            "callee span should be preserved through cross-module rewrite"
        );
    }

    #[test]
    fn protocol_registry_records_declarations_impls_and_domain_types() {
        let mut ct = crate::types::ConcreteTypes;
        let p = flatten_modules(
            &mut ct,
            parse(
                r#"
defprotocol Enumerable do
  @spec reduce(t(a), acc, (a, acc) -> acc) :: acc
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: acc
end

defmodule Consumer do
  @spec use(Enumerable.t(integer)) :: integer
  fn use(xs), do: 1
end
"#,
            ),
        )
        .expect("flatten");

        let enumerable = ModuleName::from_segments(vec!["Enumerable".to_string()]);
        let list = ModuleName::from_segments(vec!["List".to_string()]);
        let registry = &p.protocol_registry;
        assert!(registry.protocols.contains_key(&enumerable));
        let implementation = registry
            .impls
            .get(&ProtocolImplKey {
                protocol: enumerable.clone(),
                target: ImplTarget::module(list.clone()),
            })
            .expect("impl fact");
        assert_eq!(
            implementation.callbacks[&("reduce".to_string(), 3)],
            ExportKey::new(list, "reduce", 3)
        );
        let protocol_ty = p.module_type_envs["Consumer"]
            .get("Enumerable.t")
            .expect("protocol domain type");
        let any = ct.any();
        assert!(
            !ct.is_equivalent(protocol_ty, &any),
            "Protocol.t must not resolve as any"
        );
        let list_any = ct.list(any.clone());
        let int = ct.int();
        assert!(ct.is_subtype(&list_any, protocol_ty));
        assert!(ct.is_disjoint(&int, protocol_ty));
    }

    #[test]
    fn protocol_impl_must_cover_declared_callbacks() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defprotocol P do
  fn each(x)
end

defimpl P, for: List do
  fn other(x), do: x
end
"#,
            ),
        )
        .expect_err("missing callback must fail");

        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_PROTOCOL);
        assert!(d.message.contains("missing callback `each/1`"));
    }

    #[test]
    fn duplicate_protocol_impls_are_rejected() {
        let mut ct = crate::types::ConcreteTypes;
        let err = flatten_modules(
            &mut ct,
            parse(
                r#"
defprotocol P do
  fn each(x)
end

defimpl P, for: List do
  fn each(x), do: x
end

defimpl P, for: List do
  fn each(x), do: x
end
"#,
            ),
        )
        .expect_err("duplicate impl must fail");

        let d = err.to_diagnostic();
        assert_eq!(d.code, codes::RESOLVE_PROTOCOL);
        assert!(d.message.contains("already has an implementation"));
    }
}
