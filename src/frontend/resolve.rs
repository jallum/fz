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
use crate::compiler::{Compiler, CompilerWorld, ModuleId, ModuleOrigin};
use crate::diag::{Diagnostic, Span, codes};
use crate::frontend::protocols::{
    ImplTarget, PROTOCOL_ELEM_VAR, ProtocolCallbackFact, ProtocolDecl, ProtocolImplFact, ProtocolImplKey,
    ProtocolRegistry, impl_target_type, impl_target_type_with_element, protocol_domain_tag,
};
use crate::modules::identity::{ExportKey, Mfa, ModuleName, QualifiedName};
use crate::modules::interface::{ModuleInterface, collect_from_program};
use crate::modules::runtime_library::{interface, root_type_env};
use crate::telemetry::Telemetry;
use crate::type_expr::{
    ModuleTypeEnv, build_module_type_env_for_with_base, builtin_type_env, resolve_spec_decl_positions,
};
use crate::types::{Ty, Types};
use crate::{measurements, metadata};
use std::collections::{BTreeMap, BTreeSet};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
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
    /// A protocol has two implementations for the same target. Carries both
    /// the first and the duplicate site so the diagnostic can point at each.
    DuplicateProtocolImpl {
        protocol: ModuleName,
        target: ImplTarget,
        first_span: Span,
        duplicate_span: Span,
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
                format!(
                    "module `{}` does not export `{}/{}`",
                    export.module, export.name, export.arity
                ),
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
            Self::TypeAliasError { msg, span } => Diagnostic::error(codes::RESOLVE_TYPE_ALIAS, msg.clone(), *span),
            Self::ProtocolError { msg, span } => Diagnostic::error(codes::RESOLVE_PROTOCOL, msg.clone(), *span),
            Self::DuplicateProtocolImpl {
                protocol,
                target,
                first_span,
                duplicate_span,
            } => Diagnostic::error(
                codes::RESOLVE_PROTOCOL,
                format!("protocol `{}` already has an implementation for `{}`", protocol, target),
                *duplicate_span,
            )
            .with_secondary(*first_span, "first implementation here"),
        }
    }
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_diagnostic().message)
    }
}

impl Error for ResolveError {}

pub fn flatten_modules<T: Types<Ty = Ty>>(t: &mut T, prog: Program) -> Result<Program, ResolveError> {
    let mut compiler = Compiler::new();
    flatten_modules_with_compiler(
        t,
        compiler.world_mut(),
        None,
        prog,
        BTreeMap::new(),
        &crate::telemetry::NullTelemetry,
    )
}

pub fn flatten_modules_with_compiler<T: Types<Ty = Ty>>(
    t: &mut T,
    compiler: &mut CompilerWorld,
    root_source: Option<ModuleId>,
    prog: Program,
    interface_table: InterfaceTable,
    tel: &dyn Telemetry,
) -> Result<Program, ResolveError> {
    let prog = inject_module_info(prog);
    collect_module_fns(&prog)?;
    let module_macros = collect_module_macros(compiler, root_source, &prog, tel)?;
    let (module_interfaces, external_module_interfaces) =
        preload_module_contracts(compiler, root_source, &prog, interface_table, tel)?;
    let mut all_interfaces = module_interfaces.clone();
    all_interfaces.extend(external_module_interfaces.clone());
    let module_paths = collect_visible_module_paths(&prog, &module_interfaces, &external_module_interfaces);
    let mut out: Vec<Rc<Item>> = Vec::new();
    let mut module_docs: HashMap<String, String> = HashMap::new();
    collect_module_docs(&prog, &mut module_docs);
    // Build per-module `@type` envs. The root env includes compiler-known
    // runtime primitive types plus root aliases from the always-loaded
    // prelude, so module specs and aliases can name standard aliases such as
    // keyword/0 and keyword/1.
    let mut module_type_envs: HashMap<String, ModuleTypeEnv> = HashMap::new();
    let root_types = root_type_env(compiler, t, tel);
    let root_type_env = root_types.env.clone();
    module_type_envs.insert(String::new(), root_type_env.clone());
    let mut opaque_inners: HashMap<String, Ty> = root_types.opaque_inners;
    let mut brand_inners: HashMap<String, Ty> = root_types.brand_inners;
    collect_module_type_envs(
        t,
        &prog,
        "",
        &root_type_env,
        &mut module_type_envs,
        &mut opaque_inners,
        &mut brand_inners,
    )?;
    let protocol_registry = collect_protocol_registry(t, &prog, &external_module_interfaces, &mut module_type_envs)?;
    compiler.record_protocol_facts(&protocol_registry);
    let mut structs = BTreeMap::new();
    let (root_aliases, root_imports) = collect_import_scope(&prog.items, &all_interfaces, &module_macros)?;
    if let Some(root_id) = root_source {
        record_imported_visible_callables(compiler, root_id, &root_imports, &all_interfaces);
    }
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
                compiler,
                m,
                None,
                &mut out,
                &mut structs,
                &module_paths,
                &all_interfaces,
                &module_macros,
            )?,
            Item::Struct(s) => {
                structs.insert(s.module.clone(), s.fields.clone());
            }
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
                &HashSet::new(),
            )?,
        }
    }
    let struct_field_types = collect_struct_field_types(&module_type_envs, &structs)?;
    Ok(Program {
        items: out,
        module_interfaces,
        external_module_interfaces,
        module_docs,
        module_type_envs,
        opaque_inners,
        brand_inners,
        structs,
        struct_field_types,
    })
}

/// Synthesize a literal `__info__/1` reflection fn for every `defmodule`, so
/// `M.__info__(:functions | :macros | :module)` resolves and runs like any
/// other module fn. The body is pure literals (atoms, ints, tuples, lists), so
/// it flows through flatten, lowering, and codegen unchanged. A user-defined
/// `__info__` is left untouched.
fn inject_module_info(prog: Program) -> Program {
    let items = inject_info_into_items(prog.items);
    Program { items, ..prog }
}

fn inject_info_into_items(items: Vec<Rc<Item>>) -> Vec<Rc<Item>> {
    items
        .into_iter()
        .map(|item| match &*item {
            Item::Module(m) => {
                let mut m = m.clone();
                m.items = inject_info_into_items(m.items);
                if let Some(info) = build_module_info_fn(&m) {
                    m.items.push(Rc::new(Item::Fn(info)));
                }
                Rc::new(Item::Module(m))
            }
            _ => item,
        })
        .collect()
}

fn build_module_info_fn(m: &ModuleDef) -> Option<FnDef> {
    if m.items
        .iter()
        .any(|it| matches!(&**it, Item::Fn(f) if f.name == "__info__"))
    {
        return None;
    }
    let mut functions: Vec<(String, usize)> = Vec::new();
    let mut macros: Vec<(String, usize)> = Vec::new();
    for it in &m.items {
        let Item::Fn(f) = &**it else { continue };
        if f.extern_abi.is_some() {
            continue;
        }
        let Some(arity) = f.clauses.first().map(|c| c.params.len()) else {
            continue;
        };
        if f.is_macro {
            macros.push((f.name.clone(), arity));
        } else if !f.is_private {
            functions.push((f.name.clone(), arity));
        }
    }

    let pair_list = |pairs: &[(String, usize)]| -> Spanned<Expr> {
        let elems = pairs
            .iter()
            .map(|(name, arity)| {
                Spanned::dummy(Expr::Tuple(vec![
                    Spanned::dummy(Expr::Atom(name.clone())),
                    Spanned::dummy(Expr::Int(*arity as i64)),
                ]))
            })
            .collect();
        Spanned::dummy(Expr::List(elems, None))
    };
    let clause = |pat: Pattern, body: Spanned<Expr>| FnClause {
        params: vec![Spanned::dummy(pat)],
        param_annotations: vec![None],
        guard: None,
        body,
        span: Span::DUMMY,
    };

    let clauses = vec![
        clause(Pattern::Atom("functions".to_string()), pair_list(&functions)),
        clause(Pattern::Atom("macros".to_string()), pair_list(&macros)),
        clause(
            Pattern::Atom("module".to_string()),
            Spanned::dummy(Expr::Atom(m.name.clone())),
        ),
        clause(Pattern::Wildcard, Spanned::dummy(Expr::Nil)),
    ];

    Some(FnDef {
        name: "__info__".to_string(),
        name_span: Span::DUMMY,
        clauses,
        is_macro: false,
        is_private: false,
        extern_abi: None,
        extern_params: vec![],
        extern_ret_tokens: TypeExprBody(vec![]),
        variadic: false,
        attrs: vec![],
        span: Span::DUMMY,
    })
}

#[cfg(test)]
pub fn flatten_modules_with_interface_table<T: Types<Ty = Ty>>(
    t: &mut T,
    prog: Program,
    interface_table: InterfaceTable,
) -> Result<Program, ResolveError> {
    let mut compiler = Compiler::new();
    flatten_modules_with_compiler(
        t,
        compiler.world_mut(),
        None,
        prog,
        interface_table,
        &crate::telemetry::NullTelemetry,
    )
}

fn collect_struct_field_types(
    module_type_envs: &HashMap<String, ModuleTypeEnv>,
    structs: &BTreeMap<ModuleName, Vec<String>>,
) -> Result<BTreeMap<ModuleName, Vec<(String, Ty)>>, ResolveError> {
    let mut out = BTreeMap::new();
    for env in module_type_envs.values() {
        for (_alias, record) in env.struct_records() {
            let Some(schema) = structs.get(&record.module) else {
                return Err(ResolveError::TypeAliasError {
                    msg: format!("struct type references unknown struct `{}`", record.module),
                    span: record.span,
                });
            };
            let schema_fields = schema.iter().cloned().collect::<BTreeSet<_>>();
            let mut seen = BTreeSet::new();
            for field in &record.fields {
                if !schema_fields.contains(&field.name) {
                    return Err(ResolveError::TypeAliasError {
                        msg: format!("struct `{}` has no field `{}`", record.module, field.name),
                        span: record.span,
                    });
                }
                if !seen.insert(field.name.clone()) {
                    return Err(ResolveError::TypeAliasError {
                        msg: format!(
                            "struct type for `{}` declares field `{}` more than once",
                            record.module, field.name
                        ),
                        span: record.span,
                    });
                }
            }
            for field in schema {
                if !seen.contains(field) {
                    return Err(ResolveError::TypeAliasError {
                        msg: format!("struct type for `{}` is missing field `{}`", record.module, field),
                        span: record.span,
                    });
                }
            }
            if out
                .insert(
                    record.module.clone(),
                    record
                        .fields
                        .iter()
                        .map(|field| (field.name.clone(), field.ty.clone()))
                        .collect(),
                )
                .is_some()
            {
                return Err(ResolveError::TypeAliasError {
                    msg: format!("struct `{}` has more than one record type", record.module),
                    span: record.span,
                });
            }
        }
    }
    Ok(out)
}

#[derive(Clone, Debug)]
struct ModuleContractRequest {
    requester_module: String,
    target_module: ModuleName,
    cause: &'static str,
    span: Span,
}

fn preload_module_contracts(
    compiler: &mut CompilerWorld,
    root_source: Option<ModuleId>,
    prog: &Program,
    external_interfaces: InterfaceTable,
    tel: &dyn Telemetry,
) -> Result<(InterfaceTable, InterfaceTable), ResolveError> {
    let local_interfaces = match root_source {
        Some(root_source) => compiler
            .ensure_source_module_interfaces(root_source, tel)
            .expect("source-backed interface collection must succeed"),
        None => collect_from_program(prog),
    };
    let mut external_interfaces = external_interfaces;
    let mut requested = Vec::new();
    collect_requested_module_references(prog, &mut requested);
    for request in requested {
        match require_module_contract(compiler, &local_interfaces, &mut external_interfaces, &request, tel) {
            Ok(()) => {}
            Err(ResolveError::UnknownModule { .. }) if request.cause == "qualified_reference" => {}
            Err(err) => return Err(err),
        }
    }
    Ok((local_interfaces, external_interfaces))
}

fn require_module_contract(
    compiler: &mut CompilerWorld,
    local_interfaces: &InterfaceTable,
    external_interfaces: &mut InterfaceTable,
    request: &ModuleContractRequest,
    tel: &dyn Telemetry,
) -> Result<(), ResolveError> {
    note_contract_request(request, tel);
    if local_interfaces.contains_key(&request.target_module) {
        note_contract_ready(
            request,
            compiler
                .module_id_for_name(&request.target_module)
                .map(|module_id| compiler.module(module_id).origin),
            tel,
        );
        return Ok(());
    }
    if external_interfaces.contains_key(&request.target_module) {
        note_contract_ready(
            request,
            compiler
                .module_id_for_name(&request.target_module)
                .map(|module_id| compiler.module(module_id).origin),
            tel,
        );
        return Ok(());
    }
    let Some(interface) =
        interface(compiler, &request.target_module, tel).expect("runtime interface lookup must succeed")
    else {
        return Err(ResolveError::UnknownModule {
            module: request.target_module.clone(),
            span: request.span,
        });
    };
    note_contract_ready(
        request,
        compiler
            .module_id_for_name(&request.target_module)
            .map(|module_id| compiler.module(module_id).origin),
        tel,
    );
    external_interfaces.insert(request.target_module.clone(), interface.clone());
    let mut deps = Vec::new();
    enqueue_runtime_interface_dependency_requests(&interface, &request.target_module.dotted(), &mut deps);
    for dependency in deps {
        require_module_contract(compiler, local_interfaces, external_interfaces, &dependency, tel)?;
    }
    Ok(())
}

fn note_contract_request(request: &ModuleContractRequest, tel: &dyn Telemetry) {
    tel.execute(
        &["fz", "resolve", "module_contract_requested"],
        &measurements! {
            span_start: request.span.start as u64,
            span_end: request.span.end as u64,
        },
        &metadata! {
            requester_module: request.requester_module.clone(),
            target_module: request.target_module.dotted(),
            cause: request.cause,
        },
    );
}

fn note_contract_ready(request: &ModuleContractRequest, origin: Option<ModuleOrigin>, tel: &dyn Telemetry) {
    tel.execute(
        &["fz", "resolve", "module_contract_ready"],
        &measurements! {
            span_start: request.span.start as u64,
            span_end: request.span.end as u64,
        },
        &metadata! {
            requester_module: request.requester_module.clone(),
            target_module: request.target_module.dotted(),
            cause: request.cause,
            compiler_owned: origin.is_some(),
            contract_origin: origin.map(|origin| origin.kind()).unwrap_or("supplemental"),
        },
    );
}

pub(crate) fn add_macro_requested_runtime_interfaces(
    compiler: &mut CompilerWorld,
    prog: &mut Program,
    tel: &dyn Telemetry,
) {
    let mut requested = Vec::new();
    collect_requested_module_references(prog, &mut requested);
    while let Some(request) = requested.pop() {
        if prog.module_interfaces.contains_key(&request.target_module)
            || prog.external_module_interfaces.contains_key(&request.target_module)
        {
            continue;
        }
        if let Some(interface) =
            interface(compiler, &request.target_module, tel).expect("runtime interface lookup must succeed")
        {
            enqueue_runtime_interface_dependency_requests(&interface, &request.target_module.dotted(), &mut requested);
            prog.external_module_interfaces.insert(request.target_module, interface);
        }
    }
}

fn enqueue_runtime_interface_dependency_requests(
    interface: &ModuleInterface,
    requester_module: &str,
    out: &mut Vec<ModuleContractRequest>,
) {
    for import in &interface.imports {
        out.push(ModuleContractRequest {
            requester_module: requester_module.to_string(),
            target_module: import.module.clone(),
            cause: "runtime_dependency",
            span: Span::DUMMY,
        });
    }
    for protocol_impl in &interface.protocol_impls {
        out.push(ModuleContractRequest {
            requester_module: requester_module.to_string(),
            target_module: protocol_impl.protocol.clone(),
            cause: "runtime_dependency",
            span: Span::DUMMY,
        });
    }
}

fn collect_requested_module_references(prog: &Program, out: &mut Vec<ModuleContractRequest>) {
    for item in &prog.items {
        match &**item {
            Item::Module(module) => collect_requested_module_references_recursive(module, None, out),
            Item::Alias { full_path, span, .. } => out.push(ModuleContractRequest {
                requester_module: String::new(),
                target_module: full_path.clone(),
                cause: "alias",
                span: *span,
            }),
            Item::Import { path, span, .. } => out.push(ModuleContractRequest {
                requester_module: String::new(),
                target_module: path.clone(),
                cause: "import",
                span: *span,
            }),
            Item::Fn(def) => {
                for clause in &def.clauses {
                    collect_top_level_qualified_calls(&clause.body, "", out);
                    if let Some(guard) = &clause.guard {
                        collect_top_level_qualified_calls(guard, "", out);
                    }
                }
            }
            Item::ProtocolImpl(protocol_impl) => out.push(ModuleContractRequest {
                requester_module: String::new(),
                target_module: protocol_impl.protocol.clone(),
                cause: "protocol_impl_protocol",
                span: protocol_impl.span,
            }),
            _ => {}
        }
    }
}

fn collect_requested_module_references_recursive(
    module: &ModuleDef,
    parent: Option<&ModuleName>,
    out: &mut Vec<ModuleContractRequest>,
) {
    let module_name = if let Some(parent) = parent {
        parent.child(module.name.clone())
    } else {
        ModuleName::from_segments(vec![module.name.clone()])
    };
    let requester_module = module_name.dotted();
    let local_protocols = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Protocol(protocol) if protocol.name.segments().len() == 1 => {
                Some(protocol.name.last_segment().to_string())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    for item in &module.items {
        match &**item {
            Item::Alias { full_path, span, .. } => out.push(ModuleContractRequest {
                requester_module: requester_module.clone(),
                target_module: full_path.clone(),
                cause: "alias",
                span: *span,
            }),
            Item::Import { path, span, .. } => out.push(ModuleContractRequest {
                requester_module: requester_module.clone(),
                target_module: path.clone(),
                cause: "import",
                span: *span,
            }),
            Item::Fn(def) => {
                for clause in &def.clauses {
                    collect_top_level_qualified_calls(&clause.body, &requester_module, out);
                    if let Some(guard) = &clause.guard {
                        collect_top_level_qualified_calls(guard, &requester_module, out);
                    }
                }
            }
            Item::Module(inner) => collect_requested_module_references_recursive(inner, Some(&module_name), out),
            Item::ProtocolImpl(protocol_impl) => {
                let is_local_protocol = protocol_impl.protocol.segments().len() == 1
                    && (protocol_impl.protocol.last_segment() == module_name.last_segment()
                        || local_protocols.contains(protocol_impl.protocol.last_segment()));
                if !is_local_protocol {
                    out.push(ModuleContractRequest {
                        requester_module: requester_module.clone(),
                        target_module: qualify_impl_protocol_name(
                            Some(&module_name),
                            &protocol_impl.protocol,
                            &local_protocols,
                        ),
                        cause: "protocol_impl_protocol",
                        span: protocol_impl.span,
                    });
                }
            }
            _ => {}
        }
    }
}

fn collect_top_level_qualified_calls(
    expr: &Spanned<Expr>,
    requester_module: &str,
    out: &mut Vec<ModuleContractRequest>,
) {
    match &expr.node {
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            if let Some(module) = qualified_callee_module(callee) {
                out.push(ModuleContractRequest {
                    requester_module: requester_module.to_string(),
                    target_module: module,
                    cause: "qualified_reference",
                    span: callee.span,
                });
            }
            collect_top_level_qualified_calls(callee, requester_module, out);
            for arg in args {
                collect_top_level_qualified_calls(arg, requester_module, out);
            }
        }
        // fz-g58.2.6 — recurse into the `&(...)` body for qualified calls;
        // `&N` is a leaf.
        Expr::Capture(body) => collect_top_level_qualified_calls(body, requester_module, out),
        Expr::CaptureArg(_) => {}
        Expr::FnRef { name, .. } => {
            if let Some((module, _fun)) = name.rsplit_once('.')
                && let Ok(module) = ModuleName::parse_dotted(module)
            {
                out.push(ModuleContractRequest {
                    requester_module: requester_module.to_string(),
                    target_module: module,
                    cause: "qualified_reference",
                    span: expr.span,
                });
            }
        }
        Expr::List(xs, tail) => {
            for x in xs {
                collect_top_level_qualified_calls(x, requester_module, out);
            }
            if let Some(tail) = tail {
                collect_top_level_qualified_calls(tail, requester_module, out);
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                collect_top_level_qualified_calls(x, requester_module, out);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_top_level_qualified_calls(&field.value, requester_module, out);
            }
        }
        Expr::Map(pairs) => {
            for (key, value) in pairs {
                collect_top_level_qualified_calls(key, requester_module, out);
                collect_top_level_qualified_calls(value, requester_module, out);
            }
        }
        Expr::MapUpdate(map, pairs) => {
            collect_top_level_qualified_calls(map, requester_module, out);
            for (key, value) in pairs {
                collect_top_level_qualified_calls(key, requester_module, out);
                collect_top_level_qualified_calls(value, requester_module, out);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_top_level_qualified_calls(value, requester_module, out);
            }
        }
        Expr::Index(target, key) => {
            collect_top_level_qualified_calls(target, requester_module, out);
            collect_top_level_qualified_calls(key, requester_module, out);
        }
        Expr::BinOp(_, left, right) => {
            collect_top_level_qualified_calls(left, requester_module, out);
            collect_top_level_qualified_calls(right, requester_module, out);
        }
        Expr::UnOp(_, inner) | Expr::Ascribe(inner, _) | Expr::Quote(inner) | Expr::Unquote(inner) => {
            collect_top_level_qualified_calls(inner, requester_module, out);
        }
        Expr::If(cond, then_expr, else_expr) => {
            collect_top_level_qualified_calls(cond, requester_module, out);
            collect_top_level_qualified_calls(then_expr, requester_module, out);
            if let Some(else_expr) = else_expr {
                collect_top_level_qualified_calls(else_expr, requester_module, out);
            }
        }
        Expr::Case(scrutinee, arms) => {
            if let Some(scrutinee) = scrutinee {
                collect_top_level_qualified_calls(scrutinee, requester_module, out);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_top_level_qualified_calls(guard, requester_module, out);
                }
                collect_top_level_qualified_calls(&arm.body, requester_module, out);
            }
        }
        Expr::Cond(pairs) => {
            for (cond, body) in pairs {
                collect_top_level_qualified_calls(cond, requester_module, out);
                collect_top_level_qualified_calls(body, requester_module, out);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, expr) | WithBinding::Bare(expr) => {
                        collect_top_level_qualified_calls(expr, requester_module, out);
                    }
                }
            }
            collect_top_level_qualified_calls(body, requester_module, out);
            for arm in else_clauses {
                if let Some(guard) = &arm.guard {
                    collect_top_level_qualified_calls(guard, requester_module, out);
                }
                collect_top_level_qualified_calls(&arm.body, requester_module, out);
            }
        }
        Expr::Match(_, rhs) => collect_top_level_qualified_calls(rhs, requester_module, out),
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_top_level_qualified_calls(guard, requester_module, out);
                }
                collect_top_level_qualified_calls(&clause.body, requester_module, out);
            }
        }
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_top_level_qualified_calls(guard, requester_module, out);
                }
                collect_top_level_qualified_calls(&clause.body, requester_module, out);
            }
            if let Some(after) = after {
                collect_top_level_qualified_calls(&after.timeout, requester_module, out);
                collect_top_level_qualified_calls(&after.body, requester_module, out);
            }
        }
        Expr::Var(_) | Expr::Int(_) | Expr::Float(_) | Expr::Binary(_) | Expr::Atom(_) | Expr::Bool(_) | Expr::Nil => {}
    }
}

fn qualified_callee_module(callee: &Spanned<Expr>) -> Option<ModuleName> {
    if let Expr::Var(name) = &callee.node
        && let Some((module, _fun)) = name.rsplit_once('.')
    {
        return ModuleName::parse_dotted(module).ok();
    }

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
fn collect_module_type_envs<T: Types<Ty = Ty>>(
    t: &mut T,
    prog: &Program,
    parent: &str,
    base_env: &ModuleTypeEnv,
    out: &mut HashMap<String, ModuleTypeEnv>,
    o_inners: &mut HashMap<String, Ty>,
    b_inners: &mut HashMap<String, Ty>,
) -> Result<(), ResolveError> {
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_type_envs_recursive(t, m, parent, base_env, out, o_inners, b_inners)?;
        }
    }
    Ok(())
}

fn collect_module_type_envs_recursive<T: Types<Ty = Ty>>(
    t: &mut T,
    m: &ModuleDef,
    parent: &str,
    base_env: &ModuleTypeEnv,
    out: &mut HashMap<String, ModuleTypeEnv>,
    o_inners: &mut HashMap<String, Ty>,
    b_inners: &mut HashMap<String, Ty>,
) -> Result<(), ResolveError> {
    let path = if parent.is_empty() {
        m.name.clone()
    } else {
        format!("{}.{}", parent, m.name)
    };
    let (env, opaque_inners, brand_inners) = build_module_type_env_for_with_base(t, &m.attrs, &path, base_env)
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

fn collect_protocol_registry<T: Types<Ty = Ty>>(
    t: &mut T,
    prog: &Program,
    external_module_interfaces: &InterfaceTable,
    module_type_envs: &mut HashMap<String, ModuleTypeEnv>,
) -> Result<ProtocolRegistry, ResolveError> {
    let mut registry = ProtocolRegistry::default();
    collect_protocol_declarations(t, &prog.items, None, module_type_envs, &mut registry)?;
    collect_protocol_implementations(&prog.items, None, &mut registry)?;
    registry.extend_interfaces(external_module_interfaces);
    validate_protocol_impls(&registry)?;
    for protocol in registry.protocols.keys() {
        let ty = protocol_domain_type(t, protocol, &registry);
        // Element-refining template: `Protocol.t(elem)` instantiates
        // PROTOCOL_ELEM_VAR with `elem`, so a `List` target refines from
        // `list(any)` to `list(elem)`. The bare `Protocol.t` (arity 0) stays
        // the `element = any` domain above.
        let element = t.type_var(PROTOCOL_ELEM_VAR);
        let template = protocol_domain_template(t, protocol, &registry, element);
        for env in module_type_envs.values_mut() {
            env.insert(format!("{}.t", protocol), ty.clone());
            env.insert_protocol_domain(format!("{}.t", protocol), template.clone());
        }
        if let Some(env) = module_type_envs.get_mut(&protocol.dotted()) {
            env.insert("t".to_string(), ty);
            env.insert_protocol_domain("t".to_string(), template);
        }
    }
    validate_protocol_callback_specs(t, &registry, module_type_envs)?;
    Ok(registry)
}

fn protocol_domain_type<T: Types<Ty = Ty>>(t: &mut T, protocol: &ModuleName, registry: &ProtocolRegistry) -> Ty {
    let any = t.any();
    protocol_domain_template(t, protocol, registry, any)
}

/// The protocol's domain — its domain tag unioned with each implementing
/// target's type — with `element` threaded into element-parametric targets.
/// `protocol_domain_type` is the `element = any` case; the registration loop
/// passes `PROTOCOL_ELEM_VAR` to build the refining template.
fn protocol_domain_template<T: Types<Ty = Ty>>(
    t: &mut T,
    protocol: &ModuleName,
    registry: &ProtocolRegistry,
    element: Ty,
) -> Ty {
    let mut domain = t.opaque_of(&protocol_domain_tag(protocol));
    for fact in registry.impls.values().filter(|fact| fact.protocol == *protocol) {
        let target_ty = impl_target_type_with_element(t, &fact.target, element.clone());
        domain = t.union(domain, target_ty);
    }
    domain
}

fn collect_protocol_declarations<T: Types<Ty = Ty>>(
    t: &mut T,
    items: &[Rc<Item>],
    parent: Option<&ModuleName>,
    module_type_envs: &mut HashMap<String, ModuleTypeEnv>,
    registry: &mut ProtocolRegistry,
) -> Result<(), ResolveError> {
    for item in items {
        match &**item {
            Item::Protocol(protocol) => {
                let name = qualify_protocol_name(parent, &protocol.name);
                let decl = protocol_decl(t, &name, protocol, module_type_envs)?;
                if registry.protocols.insert(name.clone(), decl.clone()).is_some() {
                    return Err(ResolveError::ProtocolError {
                        msg: format!("protocol `{}` is defined more than once", name),
                        span: decl.span,
                    });
                }
            }
            Item::ProtocolImpl(protocol_impl) => {
                let _ = protocol_impl;
            }
            Item::Module(module) => {
                let name = if let Some(parent) = parent {
                    parent.child(module.name.clone())
                } else {
                    ModuleName::from_segments(vec![module.name.clone()])
                };
                collect_protocol_declarations(t, &module.items, Some(&name), module_type_envs, registry)?;
            }
            _ => {}
        }
    }

    Ok(())
}

fn collect_protocol_implementations(
    items: &[Rc<Item>],
    parent: Option<&ModuleName>,
    registry: &mut ProtocolRegistry,
) -> Result<(), ResolveError> {
    for item in items {
        match &**item {
            Item::ProtocolImpl(protocol_impl) => {
                let protocol = resolve_impl_protocol_name(parent, &protocol_impl.protocol, registry);
                let target_module = qualify_module_child(parent, &protocol_impl.target.path);
                let target = ImplTarget::module(target_module.clone());
                let impl_module = protocol_impl_module(&protocol, &target_module);
                let (callbacks, callback_specs) = protocol_impl_callbacks(&impl_module, protocol_impl)?;
                let fact = ProtocolImplFact {
                    protocol: protocol.clone(),
                    target: target.clone(),
                    callbacks,
                    callback_specs,
                    span: protocol_impl.span,
                };
                let key = ProtocolImplKey { protocol, target };
                if let Some(existing) = registry.impls.get(&key) {
                    return Err(ResolveError::DuplicateProtocolImpl {
                        protocol: key.protocol.clone(),
                        target: key.target.clone(),
                        first_span: existing.span,
                        duplicate_span: protocol_impl.span,
                    });
                }
                registry.impls.insert(key, fact);
            }
            Item::Module(module) => {
                let name = if let Some(parent) = parent {
                    parent.child(module.name.clone())
                } else {
                    ModuleName::from_segments(vec![module.name.clone()])
                };
                collect_protocol_implementations(&module.items, Some(&name), registry)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn protocol_decl<T: Types<Ty = Ty>>(
    t: &mut T,
    name: &ModuleName,
    protocol: &ProtocolDef,
    module_type_envs: &mut HashMap<String, ModuleTypeEnv>,
) -> Result<ProtocolDecl, ResolveError> {
    let mut env = ModuleTypeEnv::new();
    env.insert("t".to_string(), t.opaque_of(&protocol_domain_tag(name)));
    env.insert(format!("{}.t", name), t.opaque_of(&protocol_domain_tag(name)));
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
            specs: callback
                .attrs
                .iter()
                .filter_map(|attr| match attr {
                    Attribute::Spec(spec) => Some(spec.clone()),
                    _ => None,
                })
                .collect(),
        });
    }
    callbacks.sort_by(|a, b| (&a.name, a.arity).cmp(&(&b.name, b.arity)));
    Ok(ProtocolDecl {
        callbacks,
        span: protocol.span,
    })
}

type ProtocolImplCallbacks = (
    BTreeMap<(String, usize), ExportKey>,
    BTreeMap<(String, usize), Vec<SpecDecl>>,
);

fn protocol_impl_callbacks(
    impl_module: &ModuleName,
    protocol_impl: &ProtocolImplDef,
) -> Result<ProtocolImplCallbacks, ResolveError> {
    let mut callbacks = BTreeMap::new();
    let mut callback_specs = BTreeMap::new();
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
                let specs = def
                    .attrs
                    .iter()
                    .filter_map(|attr| match attr {
                        Attribute::Spec(spec) => Some(spec.clone()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                if !specs.is_empty() {
                    callback_specs.insert(key, specs);
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
    Ok((callbacks, callback_specs))
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
            if fact.callbacks.contains_key(&(callback.name.clone(), callback.arity)) {
                continue;
            }
            // The protocol declares `name/arity` but the impl does not provide it
            // at that arity. If the impl provides the same name at a *different*
            // arity, that is an arity mismatch (a more precise diagnosis than a
            // bare missing callback), so name both the declared and provided
            // arities. Otherwise the callback is simply absent.
            let provided_arity = fact
                .callbacks
                .keys()
                .find(|(name, _)| *name == callback.name)
                .map(|(_, arity)| *arity);
            return Err(ResolveError::ProtocolError {
                msg: match provided_arity {
                    Some(provided) => format!(
                        "implementation for protocol `{}` on `{}` implements callback `{}` at arity {} but the protocol declares `{}/{}`",
                        fact.protocol, fact.target, callback.name, provided, callback.name, callback.arity
                    ),
                    None => format!(
                        "implementation for protocol `{}` on `{}` is missing callback `{}/{}`",
                        fact.protocol, fact.target, callback.name, callback.arity
                    ),
                },
                span: fact.span,
            });
        }
        for (name, arity) in fact.callbacks.keys() {
            // A name the protocol does not declare at all is unknown. A name the
            // protocol declares only at another arity is already reported above
            // as an arity mismatch, so it is not re-reported here.
            if protocol.callbacks.iter().any(|callback| callback.name == *name) {
                continue;
            }
            return Err(ResolveError::ProtocolError {
                msg: format!(
                    "implementation for protocol `{}` on `{}` provides unknown callback `{}/{}`",
                    fact.protocol, fact.target, name, arity
                ),
                span: fact.span,
            });
        }
    }
    Ok(())
}

/// Reject an impl callback whose declared `@spec` is incompatible with the
/// protocol's declared callback spec. The protocol callback spec is read with
/// its domain variable `t` bound to the impl's concrete target type; a callback
/// position fails only when the protocol-side and impl-side types are
/// set-theoretically disjoint (empty intersection), so free type variables and
/// `any` never produce a false positive. Callbacks without a declared spec on
/// either side are not checked.
fn validate_protocol_callback_specs<T: Types<Ty = Ty>>(
    t: &mut T,
    registry: &ProtocolRegistry,
    module_type_envs: &HashMap<String, ModuleTypeEnv>,
) -> Result<(), ResolveError> {
    for fact in registry.impls.values() {
        if fact.callback_specs.is_empty() {
            continue;
        }
        let Some(protocol) = registry.protocols.get(&fact.protocol) else {
            continue;
        };
        let target_ty = impl_target_type(t, &fact.target);
        let mut proto_env = module_type_envs
            .get(&fact.protocol.dotted())
            .cloned()
            .unwrap_or_else(|| builtin_type_env(t));
        proto_env.insert("t".to_string(), target_ty.clone());
        proto_env.insert(format!("{}.t", fact.protocol), target_ty);
        for callback in &protocol.callbacks {
            if callback.specs.is_empty() {
                continue;
            }
            let key = (callback.name.clone(), callback.arity);
            let Some(impl_specs) = fact.callback_specs.get(&key) else {
                continue;
            };
            let impl_env = fact
                .callbacks
                .get(&key)
                .and_then(|export| module_type_envs.get(&export.module.dotted()))
                .cloned()
                .unwrap_or_else(|| builtin_type_env(t));
            let incompatible = impl_specs.iter().find_map(|impl_spec| {
                let mut first_incompatibility = None;
                for proto_spec in &callback.specs {
                    match protocol_spec_pair_incompatibility(t, proto_spec, &proto_env, impl_spec, &impl_env) {
                        None => return None,
                        Some(position) if first_incompatibility.is_none() => {
                            first_incompatibility = Some(position);
                        }
                        Some(_) => {}
                    }
                }
                first_incompatibility
            });
            if let Some(position) = incompatible {
                return Err(ResolveError::ProtocolError {
                    msg: format!(
                        "implementation of protocol `{}` for `{}`: callback `{}/{}` {} is incompatible with the protocol's declared spec",
                        fact.protocol, fact.target, callback.name, callback.arity, position
                    ),
                    span: fact.span,
                });
            }
        }
    }
    Ok(())
}

fn protocol_spec_pair_incompatibility<T: Types<Ty = Ty>>(
    t: &mut T,
    proto_spec: &SpecDecl,
    proto_env: &ModuleTypeEnv,
    impl_spec: &SpecDecl,
    impl_env: &ModuleTypeEnv,
) -> Option<String> {
    // Per-position so a domain-applied position (`t(a)`) that does not
    // resolve yet does not mask the result and other params.
    let (proto_params, proto_result) = resolve_spec_decl_positions(t, proto_spec, proto_env);
    let (impl_params, impl_result) = resolve_spec_decl_positions(t, impl_spec, impl_env);
    if proto_params.len() != impl_params.len() {
        return None;
    }
    for (i, (proto_param, impl_param)) in proto_params.iter().zip(impl_params.iter()).enumerate() {
        if let (Some(p), Some(q)) = (proto_param, impl_param)
            && t.is_disjoint(p, q)
        {
            return Some(format!("parameter {}", i + 1));
        }
    }
    if let (Some(p), Some(q)) = (&proto_result, &impl_result)
        && t.is_disjoint(p, q)
    {
        return Some("result".to_string());
    }
    None
}

fn qualify_module_child(parent: Option<&ModuleName>, name: &ModuleName) -> ModuleName {
    if name.segments().len() == 1
        && let Some(parent) = parent
    {
        if name.last_segment() == parent.last_segment() {
            parent.clone()
        } else {
            parent.child(name.last_segment().to_string())
        }
    } else {
        name.clone()
    }
}

fn resolve_impl_protocol_name(
    parent: Option<&ModuleName>,
    name: &ModuleName,
    registry: &ProtocolRegistry,
) -> ModuleName {
    if name.segments().len() != 1 {
        return name.clone();
    }
    if let Some(parent) = parent {
        let nested = if name.last_segment() == parent.last_segment() {
            parent.clone()
        } else {
            parent.child(name.last_segment().to_string())
        };
        if registry.protocols.contains_key(&nested) {
            return nested;
        }
    }
    name.clone()
}

fn protocol_impl_module(protocol: &ModuleName, target: &ModuleName) -> ModuleName {
    protocol.child(target.last_segment().to_string())
}

fn qualify_protocol_name(parent: Option<&ModuleName>, name: &ModuleName) -> ModuleName {
    if name.segments().len() == 1
        && let Some(parent) = parent
    {
        if name.last_segment() == parent.last_segment() {
            parent.clone()
        } else {
            parent.child(name.last_segment().to_string())
        }
    } else {
        name.clone()
    }
}

fn collect_visible_module_paths(
    prog: &Program,
    local_interfaces: &InterfaceTable,
    external_interfaces: &InterfaceTable,
) -> HashSet<String> {
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
    out.extend(local_interfaces.keys().map(ModuleName::dotted));
    out.extend(external_interfaces.keys().map(ModuleName::dotted));
    for interface in local_interfaces.values().chain(external_interfaces.values()) {
        out.extend(interface.protocols.iter().map(|protocol| protocol.name.dotted()));
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

fn collect_module_macros(
    compiler: &mut CompilerWorld,
    root_source: Option<ModuleId>,
    prog: &Program,
    tel: &dyn Telemetry,
) -> Result<ModuleMacroExports, ResolveError> {
    if let Some(root_source) = root_source {
        let exports = compiler
            .ensure_source_module_macro_exports(root_source, tel)
            .expect("root source macro exports should come from parsed compiler state");
        return Ok(exports.modules);
    }

    let mut out: ModuleMacroExports = HashMap::new();
    for item in &prog.items {
        if let Item::Module(m) = &**item {
            collect_module_macros_recursive(m, None, &mut out);
        }
    }
    Ok(out)
}

fn collect_module_macros_recursive(m: &ModuleDef, parent: Option<&ModuleName>, out: &mut ModuleMacroExports) {
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
    compiler: &mut CompilerWorld,
    m: &ModuleDef,
    parent_path: Option<&ModuleName>,
    out: &mut Vec<Rc<Item>>,
    structs: &mut BTreeMap<ModuleName, Vec<String>>,
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
    let mut local_protocols: HashSet<String> = HashSet::new();
    let mut aliases: HashMap<String, String> = HashMap::new();
    let mut imports: ImportMap = HashMap::new();
    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                siblings.insert(def.name.clone());
            }
            Item::Protocol(protocol) if protocol.name.segments().len() == 1 => {
                local_protocols.insert(protocol.name.last_segment().to_string());
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
            Item::Module(_) | Item::Struct(_) | Item::Protocol(_) | Item::ProtocolImpl(_) | Item::MacroCall { .. } => {}
        }
    }
    if let Some(module_id) = compiler.module_id_for_name(&module_name) {
        record_imported_visible_callables(compiler, module_id, &imports, module_interfaces);
    }

    for item in &m.items {
        match &**item {
            Item::Fn(def) => {
                let qualified_name = QualifiedName::in_module(module_name.clone(), def.name.clone()).dotted();
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
                        rewrite_expr(g, &module_path, &siblings, &mut intro, module_paths, &aliases, &imports);
                    }
                }
                out.push(Rc::new(Item::Fn(new_def)));
            }
            Item::Module(inner) => {
                flatten_module(
                    compiler,
                    inner,
                    Some(&module_name),
                    out,
                    structs,
                    module_paths,
                    module_interfaces,
                    module_macros,
                )?;
            }
            Item::Struct(def) => {
                let mut def = def.clone();
                def.module = module_name.clone();
                structs.insert(def.module.clone(), def.fields.clone());
                out.push(Rc::new(Item::Struct(def)));
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
                    rewrite_expr(a, &module_path, &siblings, &mut intro, module_paths, &aliases, &imports);
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
                &local_protocols,
            )?,
        }
    }
    Ok(())
}

fn record_imported_visible_callables(
    compiler: &mut CompilerWorld,
    module_id: ModuleId,
    imports: &ImportMap,
    interfaces: &InterfaceTable,
) {
    for ((name, arity), binding) in imports {
        let Some(interface) = interfaces.get(&binding.module) else {
            continue;
        };
        if !interface
            .exports
            .iter()
            .any(|export| export.name == *name && export.arity == *arity)
        {
            continue;
        }
        let Some(target_module_id) = compiler.module_id_for_name(&binding.module) else {
            continue;
        };
        compiler.record_visible_callable_alias(
            module_id,
            name.clone(),
            *arity,
            Mfa::new(target_module_id, name.clone(), *arity),
        );
    }
}

fn flatten_protocol_impl(
    protocol_impl: &ProtocolImplDef,
    parent_path: Option<&ModuleName>,
    out: &mut Vec<Rc<Item>>,
    module_paths: &HashSet<String>,
    aliases: &HashMap<String, String>,
    imports: &ImportMap,
    local_protocols: &HashSet<String>,
) -> Result<(), ResolveError> {
    let protocol = qualify_impl_protocol_name(parent_path, &protocol_impl.protocol, local_protocols);
    let target_module = qualify_module_child(parent_path, &protocol_impl.target.path);
    let impl_module = protocol_impl_module(&protocol, &target_module);
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
            let qualified_name = QualifiedName::in_module(impl_module.clone(), def.name.clone()).dotted();
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
                    rewrite_expr(g, &module_path, &siblings, &mut intro, module_paths, aliases, imports);
                }
            }
            out.push(Rc::new(Item::Fn(new_def)));
        }
    }
    Ok(())
}

fn qualify_impl_protocol_name(
    parent: Option<&ModuleName>,
    name: &ModuleName,
    local_protocols: &HashSet<String>,
) -> ModuleName {
    if name.segments().len() != 1 {
        return name.clone();
    }
    if let Some(parent) = parent
        && (name.last_segment() == parent.last_segment() || local_protocols.contains(name.last_segment()))
    {
        return qualify_protocol_name(Some(parent), name);
    }
    name.clone()
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
        // fz-g58.2.6 — sibling/import rewriting recurses into the `&(...)`
        // body; `&N` is a leaf with no name to resolve.
        Expr::Capture(body) => rewrite_expr(body, module_path, siblings, intro, module_paths, aliases, imports),
        Expr::CaptureArg(_) => {}
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
            rewrite_expr(callee, module_path, siblings, intro, module_paths, aliases, imports);
            for a in args {
                rewrite_expr(a, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::ClosureCall(callee, args) => {
            rewrite_expr(callee, module_path, siblings, intro, module_paths, aliases, imports);
            for a in args {
                rewrite_expr(a, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::List(xs, tail) => {
            for x in xs {
                rewrite_expr(x, module_path, siblings, intro, module_paths, aliases, imports);
            }
            if let Some(t) = tail {
                rewrite_expr(t, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                rewrite_expr(x, module_path, siblings, intro, module_paths, aliases, imports);
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
                rewrite_expr(k, module_path, siblings, intro, module_paths, aliases, imports);
                rewrite_expr(v, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::MapUpdate(m, pairs) => {
            rewrite_expr(m, module_path, siblings, intro, module_paths, aliases, imports);
            for (k, v) in pairs {
                rewrite_expr(k, module_path, siblings, intro, module_paths, aliases, imports);
                rewrite_expr(v, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, v) in fields {
                rewrite_expr(v, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::Index(o, i) => {
            rewrite_expr(o, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(i, module_path, siblings, intro, module_paths, aliases, imports);
        }
        Expr::BinOp(_, l, r) => {
            rewrite_expr(l, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(r, module_path, siblings, intro, module_paths, aliases, imports);
        }
        Expr::UnOp(_, x) | Expr::Ascribe(x, _) => {
            rewrite_expr(x, module_path, siblings, intro, module_paths, aliases, imports)
        }
        Expr::If(c, t, els) => {
            rewrite_expr(c, module_path, siblings, intro, module_paths, aliases, imports);
            rewrite_expr(t, module_path, siblings, intro, module_paths, aliases, imports);
            if let Some(e) = els {
                rewrite_expr(e, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::Case(scr, arms) => {
            if let Some(scr) = scr {
                rewrite_expr(scr, module_path, siblings, intro, module_paths, aliases, imports);
            }
            for arm in arms {
                let mut nested = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut nested);
                if let Some(g) = &mut arm.guard {
                    rewrite_expr(g, module_path, siblings, &mut nested, module_paths, aliases, imports);
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
                rewrite_expr(c, module_path, siblings, intro, module_paths, aliases, imports);
                rewrite_expr(b, module_path, siblings, intro, module_paths, aliases, imports);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            let mut nested = intro.clone();
            for b in bindings {
                match b {
                    WithBinding::Match(p, e) => {
                        rewrite_expr(e, module_path, siblings, &mut nested, module_paths, aliases, imports);
                        collect_pattern_vars(&p.node, &mut nested);
                    }
                    WithBinding::Bare(e) => {
                        rewrite_expr(e, module_path, siblings, &mut nested, module_paths, aliases, imports)
                    }
                }
            }
            rewrite_expr(body, module_path, siblings, &mut nested, module_paths, aliases, imports);
            for arm in else_clauses {
                let mut a_intro = intro.clone();
                collect_pattern_vars(&arm.pattern.node, &mut a_intro);
                if let Some(g) = &mut arm.guard {
                    rewrite_expr(g, module_path, siblings, &mut a_intro, module_paths, aliases, imports);
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
            rewrite_expr(rhs, module_path, siblings, intro, module_paths, aliases, imports);
            collect_pattern_vars(&pat.node, intro);
        }
        Expr::Lambda(clauses) => {
            for clause in clauses {
                let mut nested = intro.clone();
                for p in &clause.params {
                    collect_pattern_vars(&p.node, &mut nested);
                }
                if let Some(guard) = &mut clause.guard {
                    rewrite_expr(
                        guard,
                        module_path,
                        siblings,
                        &mut nested,
                        module_paths,
                        aliases,
                        imports,
                    );
                }
                rewrite_expr(
                    &mut clause.body,
                    module_path,
                    siblings,
                    &mut nested,
                    module_paths,
                    aliases,
                    imports,
                );
            }
        }
        Expr::Quote(inner) => rewrite_expr(inner, module_path, siblings, intro, module_paths, aliases, imports),
        Expr::Unquote(inner) => rewrite_expr(inner, module_path, siblings, intro, module_paths, aliases, imports),
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
                    rewrite_expr(g, module_path, siblings, &mut nested, module_paths, aliases, imports);
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
        Expr::Int(_) | Expr::Float(_) | Expr::Binary(_) | Expr::Atom(_) | Expr::Bool(_) | Expr::Nil => {}
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
    s.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
}

#[cfg(test)]
#[path = "resolve_test.rs"]
mod resolve_test;
