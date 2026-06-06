//! Module interface emission.
//!
//! Interfaces are generated from the source-level module AST and carried
//! alongside the flattened program. Resolvers, dumps, and LTO
//! validation consume them as public module contracts.

use crate::ast::{
    Attribute, FnDef, Item, ModuleDef, Program, ProtocolDef, ProtocolImplDef, SpecDecl, TypeAliasDecl, TypeExprBody,
};
use crate::diag::{Diagnostic, Span, codes};
use crate::frontend::protocols::{ImplTarget, InterfaceProtocol, InterfaceProtocolCallback, InterfaceProtocolImpl};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::parser::lexer::Tok;
use std::collections::BTreeMap;
use std::rc::Rc;

pub const FZ_INTERFACE_ABI_VERSION: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleInterface {
    pub name: ModuleName,
    pub abi_version: u32,
    pub imports: Vec<InterfaceImport>,
    pub exports: Vec<InterfaceFn>,
    pub types: Vec<InterfaceType>,
    pub protocols: Vec<InterfaceProtocol>,
    pub protocol_impls: Vec<InterfaceProtocolImpl>,
    pub docs: Option<String>,
    /// Deterministic semantic inputs used for interface compatibility checks
    /// and human-readable interface dumps. This is not a digest yet; keeping
    /// the inputs visible makes interface tests easier to audit.
    pub fingerprint_inputs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceImport {
    pub module: ModuleName,
    pub only: Vec<InterfaceImportFn>,
    pub except: Vec<InterfaceImportFn>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceImportFn {
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceFn {
    pub name: String,
    pub arity: usize,
    pub specs: Vec<InterfaceSpec>,
    pub name_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceSpec {
    pub params: Vec<String>,
    pub result: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InterfaceTypeKind {
    Alias,
    Opaque,
    Refines,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceType {
    pub name: String,
    pub kind: InterfaceTypeKind,
    pub body: String,
}

pub fn collect_from_program(prog: &Program) -> BTreeMap<ModuleName, ModuleInterface> {
    let mut out = BTreeMap::new();
    for item in &prog.items {
        match &**item {
            Item::Module(m) => collect_module(m, None, &mut out),
            Item::Protocol(protocol) => collect_protocol_unit(protocol, &mut out),
            _ => {}
        }
    }
    out
}

fn collect_protocol_unit(protocol: &ProtocolDef, out: &mut BTreeMap<ModuleName, ModuleInterface>) {
    let name = protocol.name.clone();
    let protocols = vec![interface_protocol(protocol, None)];
    let fingerprint_inputs = fingerprint_inputs(&name, &[], &[], &[], &protocols, &[], None);
    out.insert(
        name.clone(),
        ModuleInterface {
            name,
            abi_version: FZ_INTERFACE_ABI_VERSION,
            imports: Vec::new(),
            exports: Vec::new(),
            types: Vec::new(),
            protocols,
            protocol_impls: Vec::new(),
            docs: None,
            fingerprint_inputs,
        },
    );
}

fn collect_module(module: &ModuleDef, parent: Option<&ModuleName>, out: &mut BTreeMap<ModuleName, ModuleInterface>) {
    let name = if let Some(parent) = parent {
        parent.child(module.name.clone())
    } else {
        ModuleName::from_segments(vec![module.name.clone()])
    };

    let mut imports = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Import { path, only, except, .. } => Some(InterfaceImport {
                module: path.clone(),
                only: import_filter(only.as_deref()),
                except: import_filter(except.as_deref()),
            }),
            _ => None,
        })
        .collect::<Vec<_>>();
    imports.sort();

    let mut exports = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            // `__info__/1` is an implicit reflection builtin, not a declared
            // export: it is callable as `M.__info__` within a program
            // but is excluded from the module interface, so it is not imported
            // and not subject to strict @spec validation.
            Item::Fn(def) if !def.is_macro && !def.is_private && def.extern_abi.is_none() && def.name != "__info__" => {
                Some(interface_fn(def))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    exports.sort_by(|a, b| (&a.name, a.arity).cmp(&(&b.name, b.arity)));

    let mut types = module
        .attrs
        .iter()
        .filter_map(|attr| match attr {
            Attribute::TypeAlias(decl) => Some(interface_type(decl)),
            _ => None,
        })
        .collect::<Vec<_>>();
    types.sort();

    let mut protocols = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Protocol(protocol) => Some(interface_protocol(protocol, Some(&name))),
            _ => None,
        })
        .collect::<Vec<_>>();
    protocols.sort_by(|a, b| a.name.cmp(&b.name));

    let mut protocol_impls = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::ProtocolImpl(protocol_impl) => {
                Some(interface_protocol_impl(protocol_impl, Some(&name), &module.items))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    protocol_impls.sort_by(|a, b| (&a.protocol, &a.target, &a.callbacks).cmp(&(&b.protocol, &b.target, &b.callbacks)));

    let docs = module.moduledoc().map(ToOwned::to_owned);
    let fingerprint_inputs = fingerprint_inputs(
        &name,
        &imports,
        &exports,
        &types,
        &protocols,
        &protocol_impls,
        docs.as_deref(),
    );
    out.insert(
        name.clone(),
        ModuleInterface {
            name: name.clone(),
            abi_version: FZ_INTERFACE_ABI_VERSION,
            imports,
            exports,
            types,
            protocols,
            protocol_impls,
            docs,
            fingerprint_inputs,
        },
    );

    for item in &module.items {
        if let Item::Module(inner) = &**item {
            collect_module(inner, Some(&name), out);
        }
    }
}

fn import_filter(filter: Option<&[(String, usize)]>) -> Vec<InterfaceImportFn> {
    let mut out = filter
        .unwrap_or(&[])
        .iter()
        .map(|(name, arity)| InterfaceImportFn {
            name: name.clone(),
            arity: *arity,
        })
        .collect::<Vec<_>>();
    out.sort();
    out
}

fn interface_fn(def: &FnDef) -> InterfaceFn {
    let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
    InterfaceFn {
        name: def.name.clone(),
        arity,
        specs: interface_specs(&def.attrs),
        name_span: def.name_span,
    }
}

fn interface_specs(attrs: &[Attribute]) -> Vec<InterfaceSpec> {
    attrs
        .iter()
        .filter_map(|attr| match attr {
            Attribute::Spec(spec) => Some(interface_spec(spec)),
            _ => None,
        })
        .collect()
}

fn interface_spec(spec: &SpecDecl) -> InterfaceSpec {
    InterfaceSpec {
        params: spec.param_body_tokens.iter().map(render_type_body).collect(),
        result: render_type_body(&spec.result_body_tokens),
    }
}

fn interface_protocol(protocol: &ProtocolDef, parent: Option<&ModuleName>) -> InterfaceProtocol {
    let name = qualify_protocol_name(parent, &protocol.name);
    let mut callbacks = protocol
        .callbacks
        .iter()
        .map(|callback| InterfaceProtocolCallback {
            name: callback.name.clone(),
            arity: callback.arity,
            specs: interface_specs(&callback.attrs),
        })
        .collect::<Vec<_>>();
    callbacks.sort();
    InterfaceProtocol { name, callbacks }
}

fn interface_protocol_impl(
    protocol_impl: &ProtocolImplDef,
    parent: Option<&ModuleName>,
    siblings: &[Rc<Item>],
) -> InterfaceProtocolImpl {
    let protocol = interface_impl_protocol_name(parent, &protocol_impl.protocol, siblings);
    let target = qualify_module_child(parent, &protocol_impl.target.path);
    let impl_module = protocol_impl_module(&protocol, &target);
    let callbacks = protocol_impl
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Fn(def) => Some(ExportKey::new(
                impl_module.clone(),
                def.name.clone(),
                def.clauses.first().map(|c| c.params.len()).unwrap_or(0),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    InterfaceProtocolImpl {
        protocol,
        target: ImplTarget::module(target),
        callbacks,
    }
}

fn interface_impl_protocol_name(parent: Option<&ModuleName>, name: &ModuleName, siblings: &[Rc<Item>]) -> ModuleName {
    if name.segments().len() != 1 {
        return name.clone();
    }
    if let Some(parent) = parent {
        let has_local_protocol = siblings.iter().any(|item| {
            matches!(
                &**item,
                Item::Protocol(protocol)
                    if protocol.name.segments().len() == 1
                        && protocol.name.last_segment() == name.last_segment()
            )
        });
        if has_local_protocol || name.last_segment() == parent.last_segment() {
            return if name.last_segment() == parent.last_segment() {
                parent.clone()
            } else {
                parent.child(name.last_segment().to_string())
            };
        }
    }
    name.clone()
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

fn protocol_impl_module(protocol: &ModuleName, target: &ModuleName) -> ModuleName {
    protocol.child(target.last_segment().to_string())
}

fn interface_type(decl: &TypeAliasDecl) -> InterfaceType {
    InterfaceType {
        name: decl.name.clone(),
        kind: type_kind(&decl.body_tokens),
        body: render_type_body(&decl.body_tokens),
    }
}

fn type_kind(body: &TypeExprBody) -> InterfaceTypeKind {
    match body.0.first().map(|t| &t.tok) {
        Some(Tok::Ident(name)) if name == "opaque" => InterfaceTypeKind::Opaque,
        Some(Tok::Ident(name)) if name == "refines" => InterfaceTypeKind::Refines,
        _ => InterfaceTypeKind::Alias,
    }
}

fn render_type_body(body: &TypeExprBody) -> String {
    body.0
        .iter()
        .map(|token| token.tok.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

fn fingerprint_inputs(
    name: &ModuleName,
    imports: &[InterfaceImport],
    exports: &[InterfaceFn],
    types: &[InterfaceType],
    protocols: &[InterfaceProtocol],
    protocol_impls: &[InterfaceProtocolImpl],
    docs: Option<&str>,
) -> Vec<String> {
    let mut inputs = vec![format!("abi={}", FZ_INTERFACE_ABI_VERSION), format!("module={}", name)];
    if let Some(docs) = docs {
        inputs.push(format!("moduledoc={}", docs));
    }
    for import in imports {
        inputs.push(format!(
            "import={}:only=[{}]:except=[{}]",
            import.module,
            render_import_filter(&import.only),
            render_import_filter(&import.except)
        ));
    }
    for ty in types {
        inputs.push(format!("type={}:{:?}:{}", ty.name, ty.kind, ty.body));
    }
    for export in exports {
        inputs.push(format!(
            "fn={}/{}:specs=[{}]",
            export.name,
            export.arity,
            render_interface_specs(&export.specs)
        ));
    }
    for protocol in protocols {
        let callbacks = protocol
            .callbacks
            .iter()
            .map(|callback| {
                format!(
                    "{}/{}:specs=[{}]",
                    callback.name,
                    callback.arity,
                    render_interface_specs(&callback.specs)
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        inputs.push(format!("protocol={}:callbacks=[{}]", protocol.name, callbacks));
    }
    for protocol_impl in protocol_impls {
        let callbacks = protocol_impl
            .callbacks
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",");
        inputs.push(format!(
            "protocol-impl={}:target={}:callbacks=[{}]",
            protocol_impl.protocol, protocol_impl.target, callbacks
        ));
    }
    inputs
}

fn render_interface_specs(specs: &[InterfaceSpec]) -> String {
    if specs.is_empty() {
        return "<unspecified>".to_string();
    }
    specs
        .iter()
        .map(|spec| format!("({})->{}", spec.params.join(","), spec.result))
        .collect::<Vec<_>>()
        .join(";")
}

pub fn fingerprint_digest(inputs: &[String]) -> String {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;

    let mut hash = FNV_OFFSET;
    for input in inputs {
        for byte in input.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash ^= 0xff;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    format!("{hash:016x}")
}

fn render_import_filter(fns: &[InterfaceImportFn]) -> String {
    fns.iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>()
        .join(",")
}

pub fn render_interfaces(interfaces: &BTreeMap<ModuleName, ModuleInterface>) -> String {
    let mut out = String::new();
    for interface in interfaces.values() {
        out.push_str(&format!("interface {} abi={}\n", interface.name, interface.abi_version));
        if let Some(docs) = &interface.docs {
            out.push_str(&format!("  moduledoc {:?}\n", docs));
        }
        if !interface.imports.is_empty() {
            out.push_str("  imports\n");
            for import in &interface.imports {
                let only = render_import_filter(&import.only);
                let except = render_import_filter(&import.except);
                if !only.is_empty() {
                    out.push_str(&format!("    {} only [{}]\n", import.module, only));
                } else if !except.is_empty() {
                    out.push_str(&format!("    {} except [{}]\n", import.module, except));
                } else {
                    out.push_str(&format!("    {} all\n", import.module));
                }
            }
        }
        if !interface.types.is_empty() {
            out.push_str("  types\n");
            for ty in &interface.types {
                out.push_str(&format!("    {} {:?} = {}\n", ty.name, ty.kind, ty.body));
            }
        }
        if !interface.exports.is_empty() {
            out.push_str("  exports\n");
            for export in &interface.exports {
                out.push_str(&format!("    {}/{}", export.name, export.arity));
                for spec in &export.specs {
                    out.push_str(&format!(" :: ({}) -> {}", spec.params.join(", "), spec.result));
                }
                out.push('\n');
            }
        }
        if !interface.protocols.is_empty() {
            out.push_str("  protocols\n");
            for protocol in &interface.protocols {
                out.push_str(&format!("    {}\n", protocol.name));
                for callback in &protocol.callbacks {
                    out.push_str(&format!("      {}/{}", callback.name, callback.arity));
                    for spec in &callback.specs {
                        out.push_str(&format!(" :: ({}) -> {}", spec.params.join(", "), spec.result));
                    }
                    out.push('\n');
                }
            }
        }
        if !interface.protocol_impls.is_empty() {
            out.push_str("  protocol-impls\n");
            for protocol_impl in &interface.protocol_impls {
                out.push_str(&format!(
                    "    {} for {}\n",
                    protocol_impl.protocol, protocol_impl.target
                ));
                for callback in &protocol_impl.callbacks {
                    out.push_str(&format!("      {}\n", callback));
                }
            }
        }
        out.push_str(&format!(
            "  fingerprint-digest {}\n",
            fingerprint_digest(&interface.fingerprint_inputs)
        ));
        out.push_str("  fingerprint-inputs\n");
        for input in &interface.fingerprint_inputs {
            out.push_str(&format!("    {}\n", input));
        }
        out.push('\n');
    }
    out
}

pub fn validate_public_export_specs(interfaces: &BTreeMap<ModuleName, ModuleInterface>) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for interface in interfaces.values() {
        for export in &interface.exports {
            if export.specs.is_empty() {
                out.push(
                    Diagnostic::error(
                        codes::INTERFACE_MISSING_SPEC,
                        format!(
                            "public export `{}`.`{}/{}` requires an explicit @spec",
                            interface.name, export.name, export.arity
                        ),
                        export.name_span,
                    )
                    .with_help("add an @spec immediately before the exported function"),
                );
            }
        }
    }
    out
}

#[cfg(test)]
#[path = "interface_test.rs"]
mod interface_test;
