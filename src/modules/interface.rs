//! Module interface emission.
//!
//! Interfaces are generated from the source-level module AST and carried
//! alongside the flattened program. Resolvers, artifact writers, and LTO
//! validation consume them as public module contracts.

use crate::ast::{
    Attribute, FnDef, ModuleDef, Program, ProtocolDef, ProtocolImplDef, SpecDecl, TypeAliasDecl,
    TypeExprBody,
};
use crate::diag::{Diagnostic, Span, codes};
use crate::lexer::Tok;
use crate::modules::identity::ModuleName;
use crate::protocols::{
    ImplTarget, InterfaceProtocol, InterfaceProtocolCallback, InterfaceProtocolImpl,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const FZ_INTERFACE_ABI_VERSION: u32 = 1;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleInterface {
    pub name: ModuleName,
    pub abi_version: u32,
    pub imports: Vec<InterfaceImport>,
    pub exports: Vec<InterfaceFn>,
    pub types: Vec<InterfaceType>,
    #[serde(default)]
    pub protocols: Vec<InterfaceProtocol>,
    #[serde(default)]
    pub protocol_impls: Vec<InterfaceProtocolImpl>,
    pub docs: Option<String>,
    /// Deterministic semantic inputs used by future artifact fingerprinting.
    /// This is not a digest yet; keeping the inputs visible makes the first
    /// interface tests easier to audit.
    pub fingerprint_inputs: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InterfaceImport {
    pub module: ModuleName,
    pub only: Vec<InterfaceImportFn>,
    pub except: Vec<InterfaceImportFn>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InterfaceImportFn {
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterfaceFn {
    pub name: String,
    pub arity: usize,
    pub spec: Option<InterfaceSpec>,
    #[serde(skip, default = "dummy_span")]
    pub name_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InterfaceSpec {
    pub params: Vec<String>,
    pub result: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum InterfaceTypeKind {
    Alias,
    Opaque,
    Refines,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InterfaceType {
    pub name: String,
    pub kind: InterfaceTypeKind,
    pub body: String,
}

fn dummy_span() -> Span {
    Span::DUMMY
}

pub fn collect_from_program(prog: &Program) -> BTreeMap<ModuleName, ModuleInterface> {
    let mut out = BTreeMap::new();
    for item in &prog.items {
        if let crate::ast::Item::Module(m) = &**item {
            collect_module(m, None, &mut out);
        }
    }
    out
}

fn collect_module(
    module: &ModuleDef,
    parent: Option<&ModuleName>,
    out: &mut BTreeMap<ModuleName, ModuleInterface>,
) {
    let name = if let Some(parent) = parent {
        parent.child(module.name.clone())
    } else {
        ModuleName::from_segments(vec![module.name.clone()])
    };

    let mut imports = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            crate::ast::Item::Import {
                path, only, except, ..
            } => Some(InterfaceImport {
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
            // but is excluded from the module interface, so it is not imported,
            // not artifact-exported, and not subject to strict @spec validation.
            crate::ast::Item::Fn(def)
                if !def.is_macro
                    && !def.is_private
                    && def.extern_abi.is_none()
                    && def.name != "__info__" =>
            {
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
            crate::ast::Item::Protocol(protocol) => Some(interface_protocol(protocol, Some(&name))),
            _ => None,
        })
        .collect::<Vec<_>>();
    protocols.sort_by(|a, b| a.name.cmp(&b.name));

    let mut protocol_impls = module
        .items
        .iter()
        .filter_map(|item| match &**item {
            crate::ast::Item::ProtocolImpl(protocol_impl) => {
                Some(interface_protocol_impl(protocol_impl, Some(&name)))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    protocol_impls.sort_by(|a, b| {
        (&a.protocol, &a.target, &a.callbacks).cmp(&(&b.protocol, &b.target, &b.callbacks))
    });

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
        if let crate::ast::Item::Module(inner) = &**item {
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
    let spec = def.attrs.iter().find_map(|attr| match attr {
        Attribute::Spec(spec) => Some(interface_spec(spec)),
        _ => None,
    });
    InterfaceFn {
        name: def.name.clone(),
        arity,
        spec,
        name_span: def.name_span,
    }
}

fn interface_spec(spec: &SpecDecl) -> InterfaceSpec {
    InterfaceSpec {
        params: spec
            .param_body_tokens
            .iter()
            .map(render_type_body)
            .collect(),
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
            spec: callback.attrs.iter().find_map(|attr| match attr {
                Attribute::Spec(spec) => Some(interface_spec(spec)),
                _ => None,
            }),
        })
        .collect::<Vec<_>>();
    callbacks.sort();
    InterfaceProtocol { name, callbacks }
}

fn interface_protocol_impl(
    protocol_impl: &ProtocolImplDef,
    parent: Option<&ModuleName>,
) -> InterfaceProtocolImpl {
    let callbacks = protocol_impl
        .items
        .iter()
        .filter_map(|item| match &**item {
            crate::ast::Item::Fn(def) => Some(crate::modules::identity::ExportKey::new(
                qualify_module_child(parent, &protocol_impl.target.path),
                def.name.clone(),
                def.clauses.first().map(|c| c.params.len()).unwrap_or(0),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    InterfaceProtocolImpl {
        protocol: qualify_protocol_name(parent, &protocol_impl.protocol),
        target: ImplTarget::module(qualify_module_child(parent, &protocol_impl.target.path)),
        callbacks,
    }
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
        parent.child(name.last_segment().to_string())
    } else {
        name.clone()
    }
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
    let mut inputs = vec![
        format!("abi={}", FZ_INTERFACE_ABI_VERSION),
        format!("module={}", name),
    ];
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
        let spec = export
            .spec
            .as_ref()
            .map(|spec| format!("({})->{}", spec.params.join(","), spec.result))
            .unwrap_or_else(|| "<unspecified>".to_string());
        inputs.push(format!("fn={}/{}:{}", export.name, export.arity, spec));
    }
    for protocol in protocols {
        let callbacks = protocol
            .callbacks
            .iter()
            .map(|callback| {
                let spec = callback
                    .spec
                    .as_ref()
                    .map(|spec| format!("({})->{}", spec.params.join(","), spec.result))
                    .unwrap_or_else(|| "<unspecified>".to_string());
                format!("{}/{}:{}", callback.name, callback.arity, spec)
            })
            .collect::<Vec<_>>()
            .join(",");
        inputs.push(format!(
            "protocol={}:callbacks=[{}]",
            protocol.name, callbacks
        ));
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
        out.push_str(&format!(
            "interface {} abi={}\n",
            interface.name, interface.abi_version
        ));
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
                if let Some(spec) = &export.spec {
                    out.push_str(&format!(
                        " :: ({}) -> {}",
                        spec.params.join(", "),
                        spec.result
                    ));
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
                    if let Some(spec) = &callback.spec {
                        out.push_str(&format!(
                            " :: ({}) -> {}",
                            spec.params.join(", "),
                            spec.result
                        ));
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

pub fn validate_public_export_specs(
    interfaces: &BTreeMap<ModuleName, ModuleInterface>,
) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    for interface in interfaces.values() {
        for export in &interface.exports {
            if export.spec.is_none() {
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
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn interfaces(src: &str) -> BTreeMap<ModuleName, ModuleInterface> {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        collect_from_program(&prog)
    }

    fn module(name: &[&str]) -> ModuleName {
        ModuleName::from_segments(name.iter().map(|s| (*s).to_string()).collect())
    }

    #[test]
    fn emits_exports_for_modules_and_nested_modules() {
        let interfaces = interfaces(
            r#"
defmodule Outer do
  fn f(x), do: x
  defmodule Inner do
    fn g(), do: 1
  end
end
"#,
        );

        let outer = &interfaces[&module(&["Outer"])];
        assert_eq!(outer.exports[0].name, "f");
        assert_eq!(outer.exports[0].arity, 1);

        let inner = &interfaces[&module(&["Outer", "Inner"])];
        assert_eq!(inner.exports[0].name, "g");
        assert_eq!(inner.exports[0].arity, 0);
    }

    #[test]
    fn private_fns_are_not_interface_exports() {
        let interfaces = interfaces(
            r#"
defmodule M do
  fn public(x), do: helper(x)
  fnp helper(x), do: x + 1
end
"#,
        );

        let m = &interfaces[&module(&["M"])];
        let exports = m
            .exports
            .iter()
            .map(|export| format!("{}/{}", export.name, export.arity))
            .collect::<Vec<_>>();
        assert_eq!(exports, vec!["public/1"]);
    }

    #[test]
    fn emits_specs_types_opaque_refines_and_docs() {
        let interfaces = interfaces(
            r#"
defmodule Account do
  @moduledoc "Accounts."
  @type Id :: opaque int
  @type Positive :: refines int
  @type Pair :: {int, int}
  @spec get(Id) :: Pair
  fn get(id), do: {id, id}
end
"#,
        );

        let account = &interfaces[&module(&["Account"])];
        assert_eq!(account.docs.as_deref(), Some("Accounts."));
        assert_eq!(
            account
                .types
                .iter()
                .map(|ty| (&ty.name, ty.kind))
                .collect::<Vec<_>>(),
            vec![
                (&"Id".to_string(), InterfaceTypeKind::Opaque),
                (&"Pair".to_string(), InterfaceTypeKind::Alias),
                (&"Positive".to_string(), InterfaceTypeKind::Refines),
            ]
        );
        assert_eq!(account.exports[0].name, "get");
        assert_eq!(
            account.exports[0].spec,
            Some(InterfaceSpec {
                params: vec!["Upper(\"Id\")".to_string()],
                result: "Upper(\"Pair\")".to_string(),
            })
        );
    }

    #[test]
    fn emits_protocol_contract_facts() {
        let interfaces = interfaces(
            r#"
defmodule Contracts do
  defprotocol Enumerable do
    @spec reduce(t(a), acc, (a, acc) -> acc) :: acc
    fn reduce(enumerable, acc, reducer)
  end

  defimpl Enumerable, for: List do
    fn reduce(list, acc, reducer), do: acc
  end
end
"#,
        );

        let contracts = &interfaces[&module(&["Contracts"])];
        assert_eq!(
            contracts.protocols[0].name,
            module(&["Contracts", "Enumerable"])
        );
        assert_eq!(contracts.protocols[0].callbacks[0].name, "reduce");
        assert_eq!(
            contracts.protocol_impls[0].protocol,
            module(&["Contracts", "Enumerable"])
        );
        assert!(
            contracts
                .fingerprint_inputs
                .iter()
                .any(|input| input.starts_with("protocol=Contracts.Enumerable"))
        );
        let rendered = render_interfaces(&interfaces);
        assert!(rendered.contains("protocols"));
        assert!(rendered.contains("Contracts.Enumerable for Contracts.List"));
    }

    #[test]
    fn aliases_and_imports_do_not_add_exports() {
        let interfaces = interfaces(
            r#"
defmodule Math do
  fn add(x, y), do: x + y
end
defmodule User do
  alias Math, as: M
  import Math, only: [add: 2]
  fn calc(x, y), do: M.add(x, y)
end
"#,
        );
        assert_eq!(
            interfaces[&module(&["User"])]
                .imports
                .iter()
                .map(|import| format!("{}:{}", import.module, render_import_filter(&import.only)))
                .collect::<Vec<_>>(),
            vec!["Math:add/2"]
        );
        assert_eq!(
            interfaces[&module(&["User"])]
                .exports
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            vec!["calc"]
        );
    }

    #[test]
    fn extern_declarations_are_implementation_contracts_not_public_exports() {
        let interfaces = interfaces(
            r#"
defmodule Utf8 do
  extern "C" fn fz_bitstring_valid_utf8(any) :: integer

  @spec valid?(any) :: bool
  fn valid?(bytes), do: fz_bitstring_valid_utf8(bytes) == 1
end
"#,
        );

        assert_eq!(
            interfaces[&module(&["Utf8"])]
                .exports
                .iter()
                .map(|f| format!("{}/{}", f.name, f.arity))
                .collect::<Vec<_>>(),
            vec!["valid?/1"]
        );
    }

    #[test]
    fn render_interfaces_excludes_function_bodies() {
        let interfaces = interfaces(
            r#"
defmodule M do
  @spec f(integer) :: integer
  fn f(x), do: x + 100
end
"#,
        );
        let rendered = render_interfaces(&interfaces);
        assert!(rendered.contains("interface M abi=1"));
        assert!(rendered.contains("f/1 :: (Ident(\"integer\")) -> Ident(\"integer\")"));
        assert!(
            !rendered.contains("100"),
            "body leaked into interface:\n{rendered}"
        );
    }

    #[test]
    fn strict_validation_requires_specs_for_module_exports() {
        let interfaces = interfaces(
            r#"
fn helper(x), do: x

defmodule Public do
  fn missing(x), do: helper(x)
end
"#,
        );
        let diags = validate_public_export_specs(&interfaces);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, crate::diag::codes::INTERFACE_MISSING_SPEC);
        assert!(diags[0].message.contains("Public`.`missing/1"));
        assert_ne!(diags[0].primary.span, Span::DUMMY);
    }

    #[test]
    fn strict_validation_ignores_private_fns() {
        let interfaces = interfaces(
            r#"
defmodule Public do
  @spec visible(integer) :: integer
  fn visible(x), do: helper(x)

  fnp helper(x), do: x
end
"#,
        );

        assert!(validate_public_export_specs(&interfaces).is_empty());
    }

    #[test]
    fn strict_validation_accepts_matching_specs_and_overloads() {
        let name = module(&["Public"]);
        let mut interfaces = BTreeMap::new();
        interfaces.insert(
            name.clone(),
            ModuleInterface {
                name,
                abi_version: FZ_INTERFACE_ABI_VERSION,
                imports: Vec::new(),
                exports: vec![
                    InterfaceFn {
                        name: "f".to_string(),
                        arity: 0,
                        spec: Some(InterfaceSpec {
                            params: Vec::new(),
                            result: "Ident(\"integer\")".to_string(),
                        }),
                        name_span: Span::DUMMY,
                    },
                    InterfaceFn {
                        name: "f".to_string(),
                        arity: 1,
                        spec: Some(InterfaceSpec {
                            params: vec!["Ident(\"integer\")".to_string()],
                            result: "Ident(\"integer\")".to_string(),
                        }),
                        name_span: Span::DUMMY,
                    },
                ],
                types: Vec::new(),
                protocols: Vec::new(),
                protocol_impls: Vec::new(),
                docs: None,
                fingerprint_inputs: Vec::new(),
            },
        );
        assert!(validate_public_export_specs(&interfaces).is_empty());
    }

    #[test]
    fn fingerprint_inputs_are_deterministic() {
        let interfaces = interfaces(
            r#"
defmodule M do
  @type T :: int
  @spec b(T) :: T
  fn b(x), do: x
  fn a(), do: 1
end
"#,
        );
        let first = interfaces[&module(&["M"])].fingerprint_inputs.clone();
        let second = interfaces[&module(&["M"])].fingerprint_inputs.clone();
        assert_eq!(first, second);
        assert_eq!(first[0], "abi=1");
        assert_eq!(first[1], "module=M");
        assert!(first[2].starts_with("type=T:Alias:"));
        assert!(first[3].starts_with("fn=a/0:"));
        assert!(first[4].starts_with("fn=b/1:"));
    }

    #[test]
    fn fingerprint_digest_is_stable() {
        let a = vec!["module=M".to_string(), "fn=f/1:integer".to_string()];
        let b = vec!["module=M".to_string(), "fn=f/1:integer".to_string()];
        let c = vec!["module=M".to_string(), "fn=g/1:integer".to_string()];

        assert_eq!(fingerprint_digest(&a), fingerprint_digest(&b));
        assert_ne!(fingerprint_digest(&a), fingerprint_digest(&c));
        assert_eq!(fingerprint_digest(&a).len(), 16);
    }
}
