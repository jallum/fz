use super::*;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;

fn interfaces(src: &str) -> BTreeMap<ModuleName, ModuleInterface> {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    collect_from_program(&prog)
}

fn module(name: &[&str]) -> ModuleName {
    ModuleName::from_segments(name.iter().map(|s| (*s).to_string()).collect())
}

// DROP: module interface export collection, old-world pipeline infrastructure
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

// DROP: private fn excluded from module interface; old-world pipeline
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

// DROP: interface collects @type/@spec/opaque/refines; old-world pipeline
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
        account.types.iter().map(|ty| (&ty.name, ty.kind)).collect::<Vec<_>>(),
        vec![
            (&"Id".to_string(), InterfaceTypeKind::Opaque),
            (&"Pair".to_string(), InterfaceTypeKind::Alias),
            (&"Positive".to_string(), InterfaceTypeKind::Refines),
        ]
    );
    assert_eq!(account.exports[0].name, "get");
    assert_eq!(
        account.exports[0].specs,
        vec![InterfaceSpec {
            params: vec!["Upper(\"Id\")".to_string()],
            result: "Upper(\"Pair\")".to_string(),
        }]
    );
}

// DROP: protocol contract facts in module interface; old-world pipeline
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
    assert_eq!(contracts.protocols[0].name, module(&["Contracts", "Enumerable"]));
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

// DROP: multiple @spec arrows preserved in interface order; old-world pipeline
#[test]
fn interface_exports_preserve_multiple_specs_in_order() {
    let interfaces = interfaces(
        r#"
defmodule Enum do
  @spec with_index(t(a), integer) :: [{a, integer}]
  @spec with_index(t(a), (a, integer) -> b) :: [b]
  fn with_index(enumerable, offset_or_fun), do: enumerable
end
"#,
    );

    let enum_interface = &interfaces[&module(&["Enum"])];
    assert_eq!(enum_interface.exports[0].specs.len(), 2);
    assert_eq!(
        enum_interface.exports[0]
            .specs
            .iter()
            .map(|spec| spec.result.as_str())
            .collect::<Vec<_>>(),
        vec![
            "LBrack LBrace Ident(\"a\") Comma Ident(\"integer\") RBrace RBrack",
            "LBrack Ident(\"b\") RBrack"
        ]
    );
    assert!(enum_interface.fingerprint_inputs.iter().any(|input| {
        input.contains("with_index/2:specs=[")
            && input.contains("LBrack LBrace Ident(\"a\") Comma Ident(\"integer\") RBrace RBrack")
            && input.contains("LBrack Ident(\"b\") RBrack")
    }));
}

// DROP: protocol callback @spec order in interface; old-world pipeline
#[test]
fn protocol_callbacks_preserve_multiple_specs_in_order() {
    let interfaces = interfaces(
        r#"
defprotocol P do
  @spec pick(integer) :: integer
  @spec pick(float) :: float
  fn pick(value)
end
"#,
    );

    let p = &interfaces[&module(&["P"])];
    let callback = &p.protocols[0].callbacks[0];
    assert_eq!(callback.specs.len(), 2);
    assert_eq!(
        callback
            .specs
            .iter()
            .map(|spec| spec.result.as_str())
            .collect::<Vec<_>>(),
        vec!["Ident(\"integer\")", "Ident(\"float\")"]
    );
    assert!(p.fingerprint_inputs.iter().any(|input| {
        input.contains("pick/1:specs=[") && input.contains("Ident(\"integer\")") && input.contains("Ident(\"float\")")
    }));
}

// DROP: root-level protocol gets its own namespace in interface; old-world pipeline
#[test]
fn emits_root_protocol_as_own_public_namespace() {
    let interfaces = interfaces(
        r#"
defprotocol Enumerable do
  @spec reduce(t(a), acc, (a, acc) -> acc) :: acc
  fn reduce(enumerable, acc, reducer)
end
"#,
    );

    let enumerable = &interfaces[&module(&["Enumerable"])];
    assert_eq!(enumerable.name, module(&["Enumerable"]));
    assert_eq!(enumerable.exports, Vec::<InterfaceFn>::new());
    assert_eq!(enumerable.protocols[0].name, module(&["Enumerable"]));
    assert_eq!(enumerable.protocols[0].callbacks[0].name, "reduce");
    assert!(!interfaces.contains_key(&module(&["Enumerable", "Enumerable"])));
    assert!(
        enumerable
            .fingerprint_inputs
            .iter()
            .any(|input| input.starts_with("protocol=Enumerable"))
    );
}

// DROP: alias/import not added as exports; old-world interface pipeline
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

// DROP: extern fn excluded from module public exports; old-world pipeline
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

// DROP: interface rendering excludes fn bodies; old-world infrastructure
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
    assert!(rendered.contains("interface M"));
    assert!(rendered.contains("f/1 :: (Ident(\"integer\")) -> Ident(\"integer\")"));
    assert!(!rendered.contains("100"), "body leaked into interface:\n{rendered}");
}

// DROP: strict interface validation requires @spec on public exports; old-world pipeline
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

// DROP: strict validation skips private fns; old-world interface pipeline
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
            imports: Vec::new(),
            exports: vec![
                InterfaceFn {
                    name: "f".to_string(),
                    arity: 0,
                    specs: vec![InterfaceSpec {
                        params: Vec::new(),
                        result: "Ident(\"integer\")".to_string(),
                    }],
                    name_span: Span::DUMMY,
                },
                InterfaceFn {
                    name: "f".to_string(),
                    arity: 1,
                    specs: vec![InterfaceSpec {
                        params: vec!["Ident(\"integer\")".to_string()],
                        result: "Ident(\"integer\")".to_string(),
                    }],
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

// DROP: interface fingerprint input ordering determinism; old-world pipeline
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
    assert_eq!(first[0], "module=M");
    assert!(first[1].starts_with("type=T:Alias:"));
    assert!(first[2].starts_with("fn=a/0:"));
    assert!(first[3].starts_with("fn=b/1:"));
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
