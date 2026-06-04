//! Built-in runtime library modules as separate-compilation inputs.
//!
//! The language runtime has two layers:
//!
//! - primitive extern contracts implemented by Rust/C runtime symbols;
//! - ordinary FZ modules, such as `Utf8` and `Process`, implemented in
//!   per-module source files and consumed through module interfaces.
//!
//! This module exposes the second layer as deterministic `.fzi`/`.fzo`
//! artifact envelopes so resolver and linker work can depend on the same
//! facts a user library would provide.
use crate::ast::{Attribute, Expr, Item, ModuleDef, Program, ProtocolDef, Spanned, WithBinding};
#[cfg(test)]
use crate::frontend::compile_source_with_interface_table;
#[cfg(test)]
use crate::frontend::resolve::InterfaceTable;
use crate::modules::artifact::{
    FZ_ARTIFACT_ABI_VERSION, FZ_RUNTIME_ARTIFACT_ABI_VERSION, FziArtifact, FzoArtifact, FzoUnitPayload, payload_digest,
};
#[cfg(test)]
use crate::modules::artifact_store::ArtifactStore;
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{ModuleInterface, collect_from_program, fingerprint_digest};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
#[cfg(test)]
use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry};
use crate::type_expr::{
    BrandInnerTypes, ModuleTypeEnv, OpaqueInnerTypes, build_module_type_env_for_with_base, builtin_brand_inners,
    builtin_opaque_inners, builtin_type_env,
};
use crate::types::{Ty, Types};
use std::collections::{BTreeMap, BTreeSet};
#[cfg(test)]
use std::env::temp_dir;
#[cfg(test)]
use std::fs::remove_dir_all;
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeLibraryModuleArtifact {
    pub module: ModuleName,
    pub interface: ModuleInterface,
    pub fzi: FziArtifact,
    pub fzo: FzoArtifact,
}

pub struct RuntimeRootTypes {
    pub env: ModuleTypeEnv,
    pub opaque_inners: OpaqueInnerTypes,
    pub brand_inners: BrandInnerTypes,
}

pub fn prelude_source() -> &'static str {
    RUNTIME_PRELUDE_FZ
}

pub fn root_type_env<T: Types<Ty = Ty>>(t: &mut T) -> RuntimeRootTypes {
    let toks = Lexer::new(prelude_source())
        .tokenize()
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

pub fn prelude_required_modules() -> Vec<ModuleName> {
    let core_modules = RUNTIME_MODULE_SOURCES
        .iter()
        .filter(|source| source.role == RuntimeModuleRole::CorePrelude)
        .map(|source| ModuleName::from_segments(vec![source.name.to_string()]))
        .collect::<BTreeSet<_>>();
    primitive_prelude_program()
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Import { path, .. } if !core_modules.contains(path) => Some(path.clone()),
            _ => None,
        })
        .collect()
}

pub fn parsed_program() -> Program {
    let mut items = Vec::new();
    for module_source in RUNTIME_MODULE_SOURCES {
        let toks = Lexer::new(module_source.source)
            .tokenize()
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
pub fn interface_table() -> InterfaceTable {
    interfaces()
}

pub fn interfaces() -> BTreeMap<ModuleName, ModuleInterface> {
    RUNTIME_MODULE_SOURCES
        .iter()
        .filter_map(|source| {
            let module = ModuleName::from_segments(vec![source.name.to_string()]);
            interface(&module).map(|interface| (module, interface))
        })
        .collect()
}

pub fn interface(module: &ModuleName) -> Option<ModuleInterface> {
    artifact(module).map(|artifact| artifact.interface)
}

pub fn implementation_dependencies(module: &ModuleName) -> Vec<ModuleName> {
    let Some(source) = runtime_module_source(module) else {
        return Vec::new();
    };
    let toks = Lexer::new(source)
        .tokenize()
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

pub fn artifact(module: &ModuleName) -> Option<RuntimeLibraryModuleArtifact> {
    artifacts().into_iter().find(|artifact| artifact.module == *module)
}

pub fn artifacts() -> Vec<RuntimeLibraryModuleArtifact> {
    let prog = parsed_program();
    let interfaces = collect_from_program(&prog);
    let mut out = Vec::new();
    for item in &prog.items {
        match &**item {
            Item::Module(module) => collect_artifacts_recursive(module, None, &interfaces, &mut out),
            Item::Protocol(protocol) => collect_protocol_artifact(protocol, &interfaces, &mut out),
            _ => {}
        }
    }
    out
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

fn collect_protocol_artifact(
    protocol: &ProtocolDef,
    interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    out: &mut Vec<RuntimeLibraryModuleArtifact>,
) {
    let name = protocol.name.clone();
    if let Some(interface) = interfaces.get(&name) {
        let fzi = FziArtifact::new(interface.clone());
        let fzo = runtime_unit_fzo(
            &name,
            interface,
            vec!["kind=runtime-library-protocol".to_string(), format!("module={}", name)],
        );
        out.push(RuntimeLibraryModuleArtifact {
            module: name,
            interface: interface.clone(),
            fzi,
            fzo,
        });
    }
}

fn collect_artifacts_recursive(
    module: &ModuleDef,
    parent: Option<&ModuleName>,
    interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    out: &mut Vec<RuntimeLibraryModuleArtifact>,
) {
    let name = if let Some(parent) = parent {
        parent.child(module.name.clone())
    } else {
        ModuleName::from_segments(vec![module.name.clone()])
    };
    if let Some(interface) = interfaces.get(&name) {
        let fzi = FziArtifact::new(interface.clone());
        let fzo = runtime_module_fzo(module, &name, interface);
        out.push(RuntimeLibraryModuleArtifact {
            module: name.clone(),
            interface: interface.clone(),
            fzi,
            fzo,
        });
    }
    for item in &module.items {
        if let Item::Module(inner) = &**item {
            collect_artifacts_recursive(inner, Some(&name), interfaces, out);
        }
    }
}

fn runtime_module_fzo(module: &ModuleDef, name: &ModuleName, interface: &ModuleInterface) -> FzoArtifact {
    runtime_unit_fzo(name, interface, runtime_implementation_fingerprint(name, module))
}

fn runtime_unit_fzo(
    name: &ModuleName,
    interface: &ModuleInterface,
    implementation_fingerprint: Vec<String>,
) -> FzoArtifact {
    let interface_fingerprint = interface.fingerprint_inputs.clone();
    let unit_payload =
        FzoUnitPayload::runtime_module(runtime_module_source(name).expect("runtime module source is registered"));
    let implementation_fingerprint_digest = payload_digest(&unit_payload);
    FzoArtifact {
        compiler_abi_version: FZ_ARTIFACT_ABI_VERSION,
        runtime_abi_version: FZ_RUNTIME_ARTIFACT_ABI_VERSION,
        module: Some(name.clone()),
        unit_payload,
        required_imports: interface_imports(interface),
        implementation_fingerprint,
        implementation_fingerprint_digest,
        interface_fingerprint_digest: fingerprint_digest(&interface_fingerprint),
        interface_fingerprint,
    }
}

fn interface_imports(interface: &ModuleInterface) -> Vec<ExportKey> {
    interface
        .imports
        .iter()
        .flat_map(|import| {
            import
                .only
                .iter()
                .map(|f| ExportKey::new(import.module.clone(), f.name.clone(), f.arity))
                .collect::<Vec<_>>()
        })
        .collect()
}

fn runtime_implementation_fingerprint(name: &ModuleName, module: &ModuleDef) -> Vec<String> {
    let mut out = vec!["kind=runtime-library-module".to_string(), format!("module={}", name)];
    for item in &module.items {
        if let Item::Fn(def) = &**item {
            let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            let kind = if def.extern_abi.is_some() { "primitive" } else { "fz" };
            out.push(format!("fn={}/{}:{}", def.name, arity, kind));
        }
    }
    out
}

fn runtime_module_source(name: &ModuleName) -> Option<&'static str> {
    RUNTIME_MODULE_SOURCES
        .iter()
        .find(|source| source.name == name.dotted())
        .map(|source| source.source)
}

pub fn primitive_prelude_program() -> Program {
    let toks = Lexer::new(RUNTIME_PRELUDE_FZ)
        .tokenize()
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

#[cfg(test)]
pub fn primitive_contract_names() -> Vec<String> {
    let mut names = Vec::new();
    collect_primitive_contract_names(&primitive_prelude_program().items, &mut names);
    for module in parsed_program().items {
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
mod tests {
    use super::*;

    #[test]
    fn runtime_library_interfaces_expose_fz_functions_not_primitive_externs() {
        let interfaces = interface_table();
        let utf8 = interfaces
            .get(&ModuleName::from_segments(vec!["Utf8".to_string()]))
            .expect("Utf8 interface");

        let exports = utf8
            .exports
            .iter()
            .map(|f| format!("{}/{}", f.name, f.arity))
            .collect::<Vec<_>>();
        assert_eq!(exports, vec!["from_bytes/1", "from_bytes!/1", "to_bytes/1", "valid?/1"]);
        assert!(!exports.iter().any(|name| name.starts_with("fz_")));

        let enumerable = interfaces
            .get(&ModuleName::from_segments(vec!["Enumerable".to_string()]))
            .expect("Enumerable interface");
        assert!(
            enumerable
                .protocols
                .iter()
                .any(|protocol| protocol.name.dotted() == "Enumerable")
        );
        assert!(enumerable.exports.is_empty());
        let list_module = interfaces
            .get(&ModuleName::from_segments(vec!["List".to_string()]))
            .expect("List interface");
        let range_module = interfaces
            .get(&ModuleName::from_segments(vec!["Range".to_string()]))
            .expect("Range interface");
        let map_module = interfaces
            .get(&ModuleName::from_segments(vec!["Map".to_string()]))
            .expect("Map interface");

        assert!(list_module.protocol_impls.iter().any(|protocol_impl| {
            protocol_impl.protocol.dotted() == "Enumerable"
                && protocol_impl.target.display_name() == "List"
                && protocol_impl
                    .callbacks
                    .iter()
                    .any(|callback| callback.module.dotted() == "Enumerable.List")
        }));
        assert!(range_module.protocol_impls.iter().any(|protocol_impl| {
            protocol_impl.protocol.dotted() == "Enumerable"
                && protocol_impl.target.display_name() == "Range"
                && protocol_impl
                    .callbacks
                    .iter()
                    .any(|callback| callback.module.dotted() == "Enumerable.Range")
        }));
        assert!(map_module.protocol_impls.iter().any(|protocol_impl| {
            protocol_impl.protocol.dotted() == "Enumerable"
                && protocol_impl.target.display_name() == "Map"
                && protocol_impl
                    .callbacks
                    .iter()
                    .any(|callback| callback.module.dotted() == "Enumerable.Map")
        }));
        assert!(
            !interfaces
                .keys()
                .any(|module| module.dotted() == "Enumerable.Enumerable")
        );
        let enumerable_artifact =
            artifact(&ModuleName::from_segments(vec!["Enumerable".to_string()])).expect("Enumerable artifact");
        assert!(
            enumerable_artifact
                .fzo
                .unit_payload
                .body
                .trim_start()
                .starts_with("defprotocol Enumerable")
        );

        let enum_module = interfaces
            .get(&ModuleName::from_segments(vec!["Enum".to_string()]))
            .expect("Enum interface");
        let enum_exports = enum_module
            .exports
            .iter()
            .map(|f| format!("{}/{}", f.name, f.arity))
            .collect::<Vec<_>>();
        for export in ["count/1", "member?/2", "reduce/3", "slice/1", "sort/1", "sort/2"] {
            assert!(enum_exports.contains(&export.to_string()));
        }

        let kernel = interfaces
            .get(&ModuleName::from_segments(vec!["Kernel".to_string()]))
            .expect("Kernel interface");
        let kernel_exports = kernel
            .exports
            .iter()
            .map(|f| format!("{}/{}", f.name, f.arity))
            .collect::<Vec<_>>();
        for export in ["+/2", "-/2", "*/2", "//2", "%/2"] {
            assert!(
                kernel_exports.contains(&export.to_string()),
                "Kernel should export arithmetic operator {export}; exports: {kernel_exports:?}"
            );
        }

        let list_exports = list_module
            .exports
            .iter()
            .map(|f| format!("{}/{}", f.name, f.arity))
            .collect::<Vec<_>>();
        assert_eq!(
            list_exports,
            vec![
                "concat/2",
                "count/1",
                "member?/2",
                "reduce/3",
                "reverse/2",
                "subtract/2"
            ]
        );

        assert_eq!(
            utf8.docs.as_deref(),
            Some("UTF-8 validation and branding for byte-aligned binaries.")
        );
        let specs = utf8
            .exports
            .iter()
            .map(|export| {
                let spec = export.specs.first().expect("runtime export spec");
                (
                    format!("{}/{}", export.name, export.arity),
                    spec.params.clone(),
                    spec.result.clone(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            specs,
            vec![
                (
                    "from_bytes/1".to_string(),
                    vec!["Ident(\"binary\")".to_string()],
                    "LBrace Atom(\"ok\") Comma Ident(\"utf8\") RBrace Bar LBrace Atom(\"error\") Comma Atom(\"invalid_utf8\") RBrace".to_string(),
                ),
                (
                    "from_bytes!/1".to_string(),
                    vec!["Ident(\"binary\")".to_string()],
                    "Ident(\"utf8\")".to_string(),
                ),
                (
                    "to_bytes/1".to_string(),
                    vec!["Ident(\"utf8\")".to_string()],
                    "Ident(\"binary\")".to_string(),
                ),
                (
                    "valid?/1".to_string(),
                    vec!["Ident(\"binary\")".to_string()],
                    "Ident(\"bool\")".to_string(),
                ),
            ]
        );

        assert_eq!(
            primitive_contract_names(),
            vec![
                "fz_binary_concat/2",
                "fz_bitstring_valid_utf8/1",
                "fz_brand_bitstring_as_utf8/1",
                "fz_dbg_value/1",
                "fz_make_ref/0",
                "fz_make_resource/2",
                "fz_map_count/1",
                "fz_map_entry_key/2",
                "fz_map_entry_value/2",
                "fz_panic/1",
                "fz_process_heap_alloc_stats/0",
                "fz_self/0",
                "fz_send/2",
                "fz_spawn/1",
                "fz_spawn_opt/2",
            ]
        );
    }

    #[test]
    fn runtime_library_artifacts_round_trip_deterministically() {
        let artifacts = artifacts();
        assert!(!artifacts.is_empty());

        for artifact in artifacts {
            let fzi_text = artifact.fzi.serialize();
            let fzi = FziArtifact::deserialize(
                &NullTelemetry,
                None,
                &fzi_text,
                Some(&artifact.interface.fingerprint_inputs),
            )
            .expect("fzi roundtrip");
            assert_eq!(fzi.interface.name, artifact.interface.name);
            assert_eq!(fzi.interface.imports, artifact.interface.imports);
            assert_eq!(fzi.interface.types, artifact.interface.types);
            assert_eq!(
                fzi.interface
                    .exports
                    .iter()
                    .map(|f| (&f.name, f.arity, &f.specs))
                    .collect::<Vec<_>>(),
                artifact
                    .interface
                    .exports
                    .iter()
                    .map(|f| (&f.name, f.arity, &f.specs))
                    .collect::<Vec<_>>()
            );

            let fzo_text = artifact.fzo.serialize();
            let fzo = FzoArtifact::deserialize(
                &NullTelemetry,
                None,
                &fzo_text,
                Some(&artifact.fzo.interface_fingerprint),
            )
            .expect("fzo roundtrip");
            assert_eq!(fzo.module, Some(artifact.module));
            assert_eq!(fzo.interface_fingerprint, artifact.interface.fingerprint_inputs);
        }
    }

    #[test]
    fn runtime_library_artifacts_write_load_and_import_like_user_artifacts() {
        let root = temp_dir().join(format!("fz-runtime-artifacts-{}-write-load", std::process::id()));
        let _ = remove_dir_all(&root);
        let store = ArtifactStore::new(&root);
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&["fz", "module"], capture.handler());
        let artifacts = artifacts();
        let interfaces = artifacts
            .iter()
            .map(|artifact| (artifact.module.clone(), artifact.interface.clone()))
            .collect::<BTreeMap<_, _>>();

        let fzi_paths = store.write_fzi_artifacts(&tel, &interfaces).expect("write fzi");
        let fzo_paths = store
            .write_fzo_artifacts(&tel, artifacts.iter().map(|artifact| &artifact.fzo))
            .expect("write fzo");
        assert_eq!(fzi_paths.len(), artifacts.len());
        assert_eq!(fzo_paths.len(), artifacts.len());

        let utf8 = ModuleName::from_segments(vec!["Utf8".to_string()]);
        let loaded_interfaces = store.load_interface_table(&tel, [&utf8]).expect("load fzi");
        assert!(
            loaded_interfaces[&utf8]
                .exports
                .iter()
                .any(|export| { export.name == "valid?" && export.arity == 1 && !export.specs.is_empty() })
        );
        let loaded_fzo = store
            .load_fzo_artifact(&tel, &utf8, Some(&loaded_interfaces[&utf8].fingerprint_inputs))
            .expect("load fzo");
        assert_eq!(loaded_fzo.module, Some(utf8));
        assert_eq!(loaded_fzo.unit_payload.format, "fz-runtime-module-v1");

        let mut t = crate::types::new();
        let consumer = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  @spec accepts(any) :: bool
  fn accepts(bytes), do: valid?(bytes)
end
"#;
        match compile_source_with_interface_table(
            &mut t,
            consumer.to_string(),
            "consumer.fz".to_string(),
            loaded_interfaces,
            &NullTelemetry,
        ) {
            Ok(_) => {}
            Err(_) => panic!("runtime artifact interface resolves like a user artifact"),
        }
        assert!(capture.contains(&["fz", "module", "fzi_written"]));
        assert!(capture.contains(&["fz", "module", "fzo_written"]));
        assert!(capture.contains(&["fz", "module", "fzi_loaded"]));
        assert!(capture.contains(&["fz", "module", "fzo_loaded"]));

        let _ = remove_dir_all(&root);
    }

    #[test]
    fn primitive_prelude_imports_kernel_without_defmodule_body() {
        let prelude = primitive_prelude_program();
        assert!(prelude.items.iter().all(|item| !matches!(&**item, Item::Module(_))));
        assert!(
            prelude
                .items
                .iter()
                .any(|item| matches!(&**item, Item::Import { path, .. } if path.dotted() == "Kernel"))
        );
    }
}
