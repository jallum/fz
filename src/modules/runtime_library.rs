//! Built-in runtime library modules as lazily discovered source modules.
//!
//! The language runtime has two layers:
//!
//! - primitive extern contracts implemented by Rust/C runtime symbols;
//! - ordinary FZ modules, such as `Utf8` and `Process`, implemented in
//!   per-module source files and loaded through the compiler's source-backed
//!   module state.
use crate::ast::{Attribute, Expr, Item, Spanned, WithBinding};
use crate::compiler::CompilerWorld;
use crate::diag::Diagnostic;
use crate::modules::identity::ModuleName;
use crate::modules::interface::ModuleInterface;
use crate::telemetry::Telemetry;
use crate::type_expr::{
    BrandInnerTypes, ModuleTypeEnv, OpaqueInnerTypes, build_module_type_env_for_with_base, builtin_brand_inners,
    builtin_opaque_inners, builtin_type_env,
};
use crate::types::{Ty, Types};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

pub(crate) const RUNTIME_PRELUDE_FZ: &str = include_str!("runtime_library/runtime.fz");

pub(crate) struct RuntimeModuleSource {
    pub(crate) name: &'static str,
    pub(crate) source: &'static str,
}

pub(crate) const RUNTIME_MODULE_SOURCES: &[RuntimeModuleSource] = &[
    RuntimeModuleSource {
        name: "Kernel",
        source: include_str!("runtime_library/kernel.fz"),
    },
    RuntimeModuleSource {
        name: "Enumerable",
        source: include_str!("runtime_library/enumerable.fz"),
    },
    RuntimeModuleSource {
        name: "Range",
        source: include_str!("runtime_library/range.fz"),
    },
    RuntimeModuleSource {
        name: "Process",
        source: include_str!("runtime_library/process.fz"),
    },
    RuntimeModuleSource {
        name: "List",
        source: include_str!("runtime_library/list.fz"),
    },
    RuntimeModuleSource {
        name: "Map",
        source: include_str!("runtime_library/map.fz"),
    },
    RuntimeModuleSource {
        name: "Enum",
        source: include_str!("runtime_library/enum.fz"),
    },
    RuntimeModuleSource {
        name: "Utf8",
        source: include_str!("runtime_library/utf8.fz"),
    },
];

pub struct RuntimeRootTypes {
    pub env: ModuleTypeEnv,
    pub opaque_inners: OpaqueInnerTypes,
    pub brand_inners: BrandInnerTypes,
}

pub fn root_type_env<T: Types<Ty = Ty>>(
    compiler: &mut CompilerWorld,
    t: &mut T,
    tel: &dyn Telemetry,
) -> RuntimeRootTypes {
    let prelude_id = compiler.discover_primitive_prelude(tel);
    let prelude = compiler
        .ensure_prelude(prelude_id, tel)
        .expect("runtime.fz parse error (bug in built-in prelude)");
    root_type_env_from_attrs(t, &prelude.attrs)
}

pub fn root_type_env_from_attrs<T: Types<Ty = Ty>>(t: &mut T, attrs: &[Attribute]) -> RuntimeRootTypes {
    let builtin_env = builtin_type_env(t);
    let (env, declared_opaque_inners, declared_brand_inners) =
        build_module_type_env_for_with_base(t, attrs, "", &builtin_env)
            .expect("runtime.fz @type error (bug in built-in prelude)");
    let mut opaque_inners = builtin_opaque_inners(t);
    opaque_inners.extend(declared_opaque_inners);
    let mut brand_inners = builtin_brand_inners(t);
    brand_inners.extend(declared_brand_inners);
    RuntimeRootTypes {
        env,
        opaque_inners,
        brand_inners,
    }
}

pub fn interface(
    compiler: &mut CompilerWorld,
    module: &ModuleName,
    tel: &dyn Telemetry,
) -> Result<Option<ModuleInterface>, Diagnostic> {
    compiler.ensure_runtime_module_interface(module, tel)
}

pub fn implementation_dependencies(
    compiler: &mut CompilerWorld,
    module: &ModuleName,
    tel: &dyn Telemetry,
) -> Result<Vec<ModuleName>, Diagnostic> {
    let Some(module_id) = compiler.discover_runtime_module(module, tel) else {
        return Ok(Vec::new());
    };
    let items = compiler.ensure_prelude(module_id, tel)?.items;
    let prelude_imports = primitive_prelude_import_modules(compiler, tel)?;
    let mut deps = BTreeSet::new();
    collect_runtime_implementation_dependencies(&items, &prelude_imports, &mut deps);
    deps.remove(module);
    Ok(deps.into_iter().collect())
}

fn primitive_prelude_import_modules(
    compiler: &mut CompilerWorld,
    tel: &dyn Telemetry,
) -> Result<BTreeMap<(String, usize), ModuleName>, Diagnostic> {
    let prelude_id = compiler.discover_primitive_prelude(tel);
    let prelude = compiler.ensure_prelude(prelude_id, tel)?;
    let mut imports = BTreeMap::new();
    for item in &prelude.items {
        let Item::Import { path, only, except, .. } = &**item else {
            continue;
        };
        let interface = interface(compiler, path, tel)?
            .unwrap_or_else(|| panic!("runtime.fz imports unknown built-in runtime module `{path}`"));
        let mut exports = interface
            .exports
            .iter()
            .map(|export| (export.name.clone(), export.arity))
            .collect::<Vec<_>>();
        if let Some(only) = only {
            exports = only.to_vec();
        }
        if let Some(except) = except {
            exports.retain(|export| !except.contains(export));
        }
        for (name, arity) in exports {
            imports.insert((name, arity), path.clone());
        }
    }
    Ok(imports)
}

fn collect_runtime_implementation_dependencies(
    items: &[Rc<Item>],
    prelude_imports: &BTreeMap<(String, usize), ModuleName>,
    out: &mut BTreeSet<ModuleName>,
) {
    for item in items {
        match &**item {
            Item::Import { path, .. } | Item::Alias { full_path: path, .. } => {
                out.insert(path.clone());
            }
            Item::Fn(def) => {
                for clause in &def.clauses {
                    collect_expr_dependencies(&clause.body, prelude_imports, out);
                    if let Some(guard) = &clause.guard {
                        collect_expr_dependencies(guard, prelude_imports, out);
                    }
                }
            }
            Item::Module(module) => {
                collect_runtime_implementation_dependencies(&module.items, prelude_imports, out);
            }
            _ => {}
        }
    }
}

fn collect_expr_dependencies(
    expr: &Spanned<Expr>,
    prelude_imports: &BTreeMap<(String, usize), ModuleName>,
    out: &mut BTreeSet<ModuleName>,
) {
    match &expr.node {
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            if let Some(module) = qualified_callee_module(callee) {
                out.insert(module);
            } else if let Expr::Var(name) = &callee.node
                && let Some(module) = prelude_imports.get(&(name.clone(), args.len()))
            {
                out.insert(module.clone());
            }
            collect_expr_dependencies(callee, prelude_imports, out);
            for arg in args {
                collect_expr_dependencies(arg, prelude_imports, out);
            }
        }
        Expr::FnRef { name, arity } => {
            if let Some((module, _fun)) = name.rsplit_once('.')
                && let Ok(module) = ModuleName::parse_dotted(module)
            {
                out.insert(module);
            } else if let Some(module) = prelude_imports.get(&(name.clone(), *arity)) {
                out.insert(module.clone());
            }
        }
        Expr::Capture(body) | Expr::Quote(body) | Expr::Unquote(body) | Expr::Ascribe(body, _) => {
            collect_expr_dependencies(body, prelude_imports, out);
        }
        Expr::CaptureArg(_) => {}
        Expr::List(items, tail) => {
            for item in items {
                collect_expr_dependencies(item, prelude_imports, out);
            }
            if let Some(tail) = tail {
                collect_expr_dependencies(tail, prelude_imports, out);
            }
        }
        Expr::Tuple(items) | Expr::Block(items) => {
            for item in items {
                collect_expr_dependencies(item, prelude_imports, out);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_expr_dependencies(&field.value, prelude_imports, out);
            }
        }
        Expr::Map(pairs) => {
            for (key, value) in pairs {
                collect_expr_dependencies(key, prelude_imports, out);
                collect_expr_dependencies(value, prelude_imports, out);
            }
        }
        Expr::MapUpdate(map, pairs) => {
            collect_expr_dependencies(map, prelude_imports, out);
            for (key, value) in pairs {
                collect_expr_dependencies(key, prelude_imports, out);
                collect_expr_dependencies(value, prelude_imports, out);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_field, value) in fields {
                collect_expr_dependencies(value, prelude_imports, out);
            }
        }
        Expr::Index(target, key) => {
            collect_expr_dependencies(target, prelude_imports, out);
            collect_expr_dependencies(key, prelude_imports, out);
        }
        Expr::BinOp(_, left, right) => {
            collect_expr_dependencies(left, prelude_imports, out);
            collect_expr_dependencies(right, prelude_imports, out);
        }
        Expr::UnOp(_, inner) => collect_expr_dependencies(inner, prelude_imports, out),
        Expr::If(cond, then_expr, else_expr) => {
            collect_expr_dependencies(cond, prelude_imports, out);
            collect_expr_dependencies(then_expr, prelude_imports, out);
            if let Some(else_expr) = else_expr {
                collect_expr_dependencies(else_expr, prelude_imports, out);
            }
        }
        Expr::Case(scrutinee, arms) => {
            if let Some(scrutinee) = scrutinee {
                collect_expr_dependencies(scrutinee, prelude_imports, out);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_dependencies(guard, prelude_imports, out);
                }
                collect_expr_dependencies(&arm.body, prelude_imports, out);
            }
        }
        Expr::Cond(pairs) => {
            for (cond, body) in pairs {
                collect_expr_dependencies(cond, prelude_imports, out);
                collect_expr_dependencies(body, prelude_imports, out);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, value) => collect_expr_dependencies(value, prelude_imports, out),
                    WithBinding::Bare(value) => collect_expr_dependencies(value, prelude_imports, out),
                }
            }
            collect_expr_dependencies(body, prelude_imports, out);
            for clause in else_clauses {
                if let Some(guard) = &clause.guard {
                    collect_expr_dependencies(guard, prelude_imports, out);
                }
                collect_expr_dependencies(&clause.body, prelude_imports, out);
            }
        }
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_expr_dependencies(guard, prelude_imports, out);
                }
                collect_expr_dependencies(&clause.body, prelude_imports, out);
            }
            if let Some(after) = after {
                collect_expr_dependencies(&after.timeout, prelude_imports, out);
                collect_expr_dependencies(&after.body, prelude_imports, out);
            }
        }
        Expr::Match(_pattern, rhs) => collect_expr_dependencies(rhs, prelude_imports, out),
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_expr_dependencies(guard, prelude_imports, out);
                }
                collect_expr_dependencies(&clause.body, prelude_imports, out);
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

fn is_upper(s: &str) -> bool {
    s.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
}

#[cfg(test)]
pub fn primitive_prelude_program(compiler: &mut CompilerWorld, tel: &dyn Telemetry) -> crate::ast::Program {
    let prelude_id = compiler.discover_primitive_prelude(tel);
    let items = compiler
        .ensure_prelude(prelude_id, tel)
        .expect("runtime.fz parse error (bug in built-in prelude)")
        .items;
    crate::ast::Program {
        items,
        module_interfaces: BTreeMap::new(),
        external_module_interfaces: BTreeMap::new(),
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        protocol_registry: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
        structs: Default::default(),
        struct_field_types: Default::default(),
    }
}

#[cfg(test)]
#[path = "runtime_library_test.rs"]
mod runtime_library_test;
