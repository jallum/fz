//! Built-in runtime library modules as separate-compilation inputs.
//!
//! The language runtime has two layers:
//!
//! - primitive extern contracts implemented by Rust/C runtime symbols;
//! - ordinary FZ modules, such as `Utf8` and `Process`, implemented in
//!   per-module source files and consumed through module interfaces.
//!
//! This module exposes the second layer as in-memory module interfaces plus
//! source text so resolver and linker work can depend on the same facts a user
//! library would provide.
use crate::ast::{Attribute, Expr, Item, Program, Spanned, WithBinding};
#[cfg(test)]
use crate::frontend::compile_source_with_interface_table;
#[cfg(test)]
use crate::frontend::resolve::InterfaceTable;
use crate::modules::identity::ModuleName;
use crate::modules::interface::{ModuleInterface, collect_from_program};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::Telemetry;
use crate::type_expr::{
    BrandInnerTypes, ModuleTypeEnv, OpaqueInnerTypes, build_module_type_env_for_with_base, builtin_brand_inners,
    builtin_opaque_inners, builtin_type_env,
};
use crate::types::{Ty, Types};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

const RUNTIME_PRELUDE_FZ: &str = include_str!("runtime_library/runtime.fz");

struct RuntimeModuleSource {
    name: &'static str,
    source: &'static str,
    role: RuntimeModuleRole,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RuntimeModuleRole {
    CorePrelude,
    Library,
}

const RUNTIME_MODULE_SOURCES: &[RuntimeModuleSource] = &[
    RuntimeModuleSource {
        name: "Kernel",
        source: include_str!("runtime_library/kernel.fz"),
        role: RuntimeModuleRole::CorePrelude,
    },
    RuntimeModuleSource {
        name: "Enumerable",
        source: include_str!("runtime_library/enumerable.fz"),
        role: RuntimeModuleRole::CorePrelude,
    },
    RuntimeModuleSource {
        name: "Range",
        source: include_str!("runtime_library/range.fz"),
        role: RuntimeModuleRole::CorePrelude,
    },
    RuntimeModuleSource {
        name: "Process",
        source: include_str!("runtime_library/process.fz"),
        role: RuntimeModuleRole::Library,
    },
    RuntimeModuleSource {
        name: "List",
        source: include_str!("runtime_library/list.fz"),
        role: RuntimeModuleRole::CorePrelude,
    },
    RuntimeModuleSource {
        name: "Map",
        source: include_str!("runtime_library/map.fz"),
        role: RuntimeModuleRole::CorePrelude,
    },
    RuntimeModuleSource {
        name: "Enum",
        source: include_str!("runtime_library/enum.fz"),
        role: RuntimeModuleRole::Library,
    },
    RuntimeModuleSource {
        name: "Utf8",
        source: include_str!("runtime_library/utf8.fz"),
        role: RuntimeModuleRole::Library,
    },
];

pub struct RuntimeRootTypes {
    pub env: ModuleTypeEnv,
    pub opaque_inners: OpaqueInnerTypes,
    pub brand_inners: BrandInnerTypes,
}

pub fn prelude_source() -> &'static str {
    RUNTIME_PRELUDE_FZ
}

pub fn root_type_env<T: Types<Ty = Ty>>(t: &mut T, tel: &dyn Telemetry) -> RuntimeRootTypes {
    let toks = Lexer::with_source_name(prelude_source(), "runtime:runtime.fz")
        .tokenize(tel)
        .expect("runtime.fz lex error (bug in built-in prelude)");
    let (_items, attrs) = Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in prelude)");
    root_type_env_from_attrs(t, &attrs)
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

pub fn core_prelude_module_sources() -> impl Iterator<Item = (&'static str, &'static str)> {
    RUNTIME_MODULE_SOURCES
        .iter()
        .filter(|source| source.role == RuntimeModuleRole::CorePrelude)
        .map(|source| (source.name, source.source))
}

pub fn is_core_prelude_module(module: &ModuleName) -> bool {
    RUNTIME_MODULE_SOURCES
        .iter()
        .any(|source| source.role == RuntimeModuleRole::CorePrelude && source.name == module.dotted())
}

pub fn prelude_required_modules(tel: &dyn Telemetry) -> Vec<ModuleName> {
    let core_modules = RUNTIME_MODULE_SOURCES
        .iter()
        .filter(|source| source.role == RuntimeModuleRole::CorePrelude)
        .map(|source| ModuleName::from_segments(vec![source.name.to_string()]))
        .collect::<BTreeSet<_>>();
    primitive_prelude_program(tel)
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Import { path, .. } if !core_modules.contains(path) => Some(path.clone()),
            _ => None,
        })
        .collect()
}

pub fn parsed_program(tel: &dyn Telemetry) -> Program {
    let mut items = Vec::new();
    for module_source in RUNTIME_MODULE_SOURCES {
        let source_name = runtime_source_name(module_source.name);
        let toks = Lexer::with_source_name(module_source.source, source_name.clone())
            .tokenize(tel)
            .unwrap_or_else(|_| panic!("{}.fz lex error (bug in built-in runtime library)", module_source.name));
        let (mut parsed_items, _attrs) = Parser::new(toks).parse_prelude().unwrap_or_else(|err| {
            panic!(
                "{}.fz parse error (bug in built-in runtime library): {} at {:?}",
                module_source.name, err, err.span
            )
        });
        items.append(&mut parsed_items);
    }
    Program {
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
pub fn interface_table(tel: &dyn Telemetry) -> InterfaceTable {
    interfaces(tel)
}

pub fn interfaces(tel: &dyn Telemetry) -> BTreeMap<ModuleName, ModuleInterface> {
    collect_from_program(&parsed_program(tel))
}

pub fn interface(module: &ModuleName, tel: &dyn Telemetry) -> Option<ModuleInterface> {
    interfaces(tel).remove(module)
}

pub fn implementation_dependencies(module: &ModuleName, tel: &dyn Telemetry) -> Vec<ModuleName> {
    let Some(source) = runtime_module_source(module) else {
        return Vec::new();
    };
    let toks = Lexer::with_source_name(source, runtime_source_name(module.dotted()))
        .tokenize(tel)
        .unwrap_or_else(|_| panic!("{}.fz lex error (bug in built-in runtime library)", module));
    let (items, _attrs) = Parser::new(toks).parse_prelude().unwrap_or_else(|err| {
        panic!(
            "{}.fz parse error (bug in built-in runtime library): {} at {:?}",
            module, err, err.span
        )
    });
    let mut deps = BTreeSet::new();
    collect_runtime_implementation_dependencies(&items, &mut deps);
    deps.remove(module);
    deps.into_iter().collect()
}

pub fn source(module: &ModuleName) -> Option<&'static str> {
    runtime_module_source(module)
}

fn collect_runtime_implementation_dependencies(items: &[Rc<Item>], out: &mut BTreeSet<ModuleName>) {
    for item in items {
        match &**item {
            Item::Import { path, .. } | Item::Alias { full_path: path, .. } => {
                out.insert(path.clone());
            }
            Item::Fn(def) => {
                for clause in &def.clauses {
                    collect_expr_dependencies(&clause.body, out);
                    if let Some(guard) = &clause.guard {
                        collect_expr_dependencies(guard, out);
                    }
                }
            }
            Item::Module(module) => {
                collect_runtime_implementation_dependencies(&module.items, out);
            }
            _ => {}
        }
    }
}

fn collect_expr_dependencies(expr: &Spanned<Expr>, out: &mut BTreeSet<ModuleName>) {
    match &expr.node {
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            if let Some(module) = qualified_callee_module(callee) {
                out.insert(module);
            }
            collect_expr_dependencies(callee, out);
            for arg in args {
                collect_expr_dependencies(arg, out);
            }
        }
        Expr::FnRef { name, .. } => {
            if let Some((module, _fun)) = name.rsplit_once('.')
                && let Ok(module) = ModuleName::parse_dotted(module)
            {
                out.insert(module);
            }
        }
        Expr::Capture(body) | Expr::Quote(body) | Expr::Unquote(body) | Expr::Ascribe(body, _) => {
            collect_expr_dependencies(body, out);
        }
        Expr::CaptureArg(_) => {}
        Expr::List(items, tail) => {
            for item in items {
                collect_expr_dependencies(item, out);
            }
            if let Some(tail) = tail {
                collect_expr_dependencies(tail, out);
            }
        }
        Expr::Tuple(items) | Expr::Block(items) => {
            for item in items {
                collect_expr_dependencies(item, out);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_expr_dependencies(&field.value, out);
            }
        }
        Expr::Map(pairs) => {
            for (key, value) in pairs {
                collect_expr_dependencies(key, out);
                collect_expr_dependencies(value, out);
            }
        }
        Expr::MapUpdate(map, pairs) => {
            collect_expr_dependencies(map, out);
            for (key, value) in pairs {
                collect_expr_dependencies(key, out);
                collect_expr_dependencies(value, out);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_field, value) in fields {
                collect_expr_dependencies(value, out);
            }
        }
        Expr::Index(target, key) => {
            collect_expr_dependencies(target, out);
            collect_expr_dependencies(key, out);
        }
        Expr::BinOp(_, left, right) => {
            collect_expr_dependencies(left, out);
            collect_expr_dependencies(right, out);
        }
        Expr::UnOp(_, inner) => collect_expr_dependencies(inner, out),
        Expr::If(cond, then_expr, else_expr) => {
            collect_expr_dependencies(cond, out);
            collect_expr_dependencies(then_expr, out);
            if let Some(else_expr) = else_expr {
                collect_expr_dependencies(else_expr, out);
            }
        }
        Expr::Case(scrutinee, arms) => {
            if let Some(scrutinee) = scrutinee {
                collect_expr_dependencies(scrutinee, out);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_dependencies(guard, out);
                }
                collect_expr_dependencies(&arm.body, out);
            }
        }
        Expr::Cond(pairs) => {
            for (cond, body) in pairs {
                collect_expr_dependencies(cond, out);
                collect_expr_dependencies(body, out);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, value) => collect_expr_dependencies(value, out),
                    WithBinding::Bare(value) => collect_expr_dependencies(value, out),
                }
            }
            collect_expr_dependencies(body, out);
            for clause in else_clauses {
                if let Some(guard) = &clause.guard {
                    collect_expr_dependencies(guard, out);
                }
                collect_expr_dependencies(&clause.body, out);
            }
        }
        Expr::Receive { clauses, after } => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_expr_dependencies(guard, out);
                }
                collect_expr_dependencies(&clause.body, out);
            }
            if let Some(after) = after {
                collect_expr_dependencies(&after.timeout, out);
                collect_expr_dependencies(&after.body, out);
            }
        }
        Expr::Match(_pattern, rhs) => collect_expr_dependencies(rhs, out),
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    collect_expr_dependencies(guard, out);
                }
                collect_expr_dependencies(&clause.body, out);
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

fn runtime_module_source(name: &ModuleName) -> Option<&'static str> {
    RUNTIME_MODULE_SOURCES
        .iter()
        .find(|source| source.name == name.dotted())
        .map(|source| source.source)
}

pub fn primitive_prelude_program(tel: &dyn Telemetry) -> Program {
    let toks = Lexer::with_source_name(RUNTIME_PRELUDE_FZ, "runtime:runtime.fz")
        .tokenize(tel)
        .expect("runtime.fz lex error (bug in built-in prelude)");
    let (items, _attrs) = Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in prelude)");
    Program {
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

fn runtime_source_name(name: impl AsRef<str>) -> String {
    let name = name.as_ref();
    if name.ends_with(".fz") {
        format!("runtime:{name}")
    } else {
        format!("runtime:{name}.fz")
    }
}

#[cfg(test)]
pub fn primitive_contract_names(tel: &dyn Telemetry) -> Vec<String> {
    let mut names = Vec::new();
    collect_primitive_contract_names(&primitive_prelude_program(tel).items, &mut names);
    for module in parsed_program(tel).items {
        if let Item::Module(module) = &*module {
            collect_primitive_contract_names(&module.items, &mut names);
        }
    }
    names.sort();
    names
}

#[cfg(test)]
fn collect_primitive_contract_names(items: &[Rc<Item>], names: &mut Vec<String>) {
    for item in items {
        if let Item::Fn(def) = &**item
            && def.extern_abi.is_some()
        {
            let arity = def.extern_params.len();
            names.push(format!("{}/{}", def.name, arity));
        }
        if let Item::Module(module) = &**item {
            collect_primitive_contract_names(&module.items, names);
        }
    }
}

#[cfg(test)]
#[path = "runtime_library_test.rs"]
mod runtime_library_test;
