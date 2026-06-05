use super::*;
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, InterfaceFn};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::type_expr::{build_module_type_env, parse_type_expr, resolve_spec_decl};
use crate::types::DefaultTypes;

fn parse(src: &str) -> Program {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse")
}

fn flatten(src: &str) -> Program {
    let mut ct = crate::types::new();
    flatten_modules(&mut ct, parse(src), &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten")
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
    // Every module gains a synthesized `__info__/1`.
    assert_eq!(fn_names(&p), vec!["M.f", "M.__info__"]);
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
    // Every module gains a synthesized `__info__/1` — including the
    // namespace-only outer module `A`.
    assert_eq!(fn_names(&p), vec!["A.B.f", "A.B.__info__", "A.__info__"]);
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
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .unwrap_err();
    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_UNKNOWN_MODULE);
    assert_eq!(d.message, "module `Missing` is not defined");
    assert_ne!(d.primary.span, Span::DUMMY);
}

#[test]
fn alias_unknown_module_errors() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .unwrap_err();
    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_UNKNOWN_MODULE);
    assert_eq!(d.message, "module `Missing.Path` is not defined");
}

#[test]
fn import_unknown_arity_errors() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .unwrap_err();
    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_UNKNOWN_IMPORT);
    assert_eq!(d.message, "module `Math` does not export `add/1`");
}

#[test]
fn import_except_unknown_arity_errors() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .unwrap_err();
    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_UNKNOWN_IMPORT);
    assert_eq!(d.message, "module `Math` does not export `add/1`");
}

#[test]
fn import_resolves_from_external_interface_table() {
    let mut ct = crate::types::new();
    let math = ModuleName::from_segments(vec!["Math".to_string()]);
    let mut interfaces = InterfaceTable::new();
    interfaces.insert(
        math.clone(),
        ModuleInterface {
            name: math,
            abi_version: FZ_INTERFACE_ABI_VERSION,
            imports: Vec::new(),
            exports: vec![InterfaceFn {
                name: "add".to_string(),
                arity: 2,
                specs: Vec::new(),
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
fn qualified_runtime_namespace_reference_requests_interface() {
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
                matches!(&callee.node, Expr::Var(name) if name == "Utf8.valid?"),
                "qualified runtime namespace reference must request and resolve the interface"
            );
        }
        other => panic!("expected call, got {:?}", other),
    }
    assert!(
        p.external_module_interfaces
            .contains_key(&ModuleName::from_segments(vec!["Utf8".to_string()]))
    );
}

#[test]
fn runtime_protocol_impl_requests_protocol_interface() {
    let p = flatten(
        r#"
defmodule User do
  fn run(), do: Range.new(1, 3, 1)
end
"#,
    );
    assert!(
        p.external_module_interfaces
            .contains_key(&ModuleName::from_segments(vec!["Range".to_string()]))
    );
    assert!(
        p.external_module_interfaces
            .contains_key(&ModuleName::from_segments(vec!["Enumerable".to_string()]))
    );
}

#[test]
fn import_non_exported_name_errors() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .unwrap_err();
    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_UNKNOWN_IMPORT);
    assert_eq!(d.message, "module `Math` does not export `hidden/0`");
}

#[test]
fn conflicting_imports_error() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
        items: vec![Rc::new(Item::Fn(defs[0].clone())), Rc::new(Item::Fn(defs[1].clone()))],
        attrs: Vec::new(),
        span: Span::DUMMY,
    };
    let prog = Program {
        items: vec![Rc::new(Item::Module(module))],
        module_interfaces: Default::default(),
        ..Program::default()
    };
    let mut ct = crate::types::new();
    let err = flatten_modules(&mut ct, prog, &crate::telemetry::ConfiguredTelemetry::new()).unwrap_err();
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
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &m.attrs).unwrap();
    let int = ct.int();
    assert!(ct.is_equivalent(env.get("id").unwrap(), &int));
    let expected = ct.tuple(&[int.clone(), int]);
    assert!(ct.is_equivalent(env.get("pair").unwrap(), &expected));
    let keyword_int = parse_type_expr(
        &mut ct,
        &Lexer::with_source_name("keyword(integer)", "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
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
    let mut ct = crate::types::new();
    let flat = flatten_modules(&mut ct, prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten");
    let env = flat.module_type_envs.get("M").expect("module env");
    let opts = env.get("opts").expect("opts alias");
    let atom = ct.atom();
    let int = ct.int();
    let pair = ct.tuple(&[atom, int]);
    let expected = ct.list(pair);
    assert!(ct.is_equivalent(opts, &expected));
}

#[test]
fn struct_record_type_alias_populates_program_field_types() {
    let prog = parse(
        r#"
defmodule Range do
  defstruct [:first, :last, :step]
  @type t :: %Range{first: integer, last: integer, step: integer}
end
"#,
    );
    let mut ct = crate::types::new();
    let flat = flatten_modules(&mut ct, prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten");
    let range = ModuleName::from_segments(vec!["Range".to_string()]);
    let fields = flat.struct_field_types.get(&range).expect("Range field types");
    assert_eq!(
        fields.iter().map(|(name, _ty)| name.as_str()).collect::<Vec<_>>(),
        vec!["first", "last", "step"]
    );
    let int = ct.int();
    assert!(fields.iter().all(|(_name, ty)| ct.is_equivalent(ty, &int)));
}

#[test]
fn struct_record_type_alias_must_match_defstruct_schema() {
    let prog = parse(
        r#"
defmodule Range do
  defstruct [:first, :last, :step]
  @type t :: %Range{first: integer, last: integer}
end
"#,
    );
    let mut ct = crate::types::new();
    let err = flatten_modules(&mut ct, prog, &crate::telemetry::ConfiguredTelemetry::new())
        .expect_err("expected schema mismatch");
    match err {
        ResolveError::TypeAliasError { msg, span } => {
            assert!(msg.contains("missing field `step`"), "{msg}");
            assert!(!span.is_dummy());
        }
        other => panic!("expected type alias error, got {other:?}"),
    }
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
    let mut ct = crate::types::new();
    let flat = flatten_modules(&mut ct, prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten");
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
    let resolved = resolve_spec_decl(&mut ct, spec, env).expect("resolve spec");
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
    let env = ModuleTypeEnv::new();
    let mut ct = crate::types::new();
    let resolved = resolve_spec_decl(&mut ct, spec, &env).unwrap();
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
    let toks = Lexer::with_source_name(
        "defmodule M do\n\
          @spec add1(integer, integer) :: integer\n\
          fn add1(n), do: n + 1\n\
        end\n",
        "<test>",
    )
    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
    .unwrap();
    let r = Parser::new(toks).parse_program(&crate::telemetry::ConfiguredTelemetry::new());
    assert!(r.is_err(), "arity mismatch must error");
    let msg = format!("{:?}", r.unwrap_err());
    assert!(msg.contains("arity"), "expected arity diag, got: {}", msg);
}

#[test]
fn spec_name_mismatch_errors_at_parse_time() {
    let toks = Lexer::with_source_name(
        "defmodule M do\n\
          @spec other(integer) :: integer\n\
          fn add1(n), do: n + 1\n\
        end\n",
        "<test>",
    )
    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
    .unwrap();
    let r = Parser::new(toks).parse_program(&crate::telemetry::ConfiguredTelemetry::new());
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
    let toks = Lexer::with_source_name(
        "defmodule M do\n\
          @spec lonely(integer) :: integer\n\
        end\n",
        "<test>",
    )
    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
    .unwrap();
    let r = Parser::new(toks).parse_program(&crate::telemetry::ConfiguredTelemetry::new());
    assert!(r.is_err(), "spec without fn must error");
}

#[test]
fn multiple_specs_on_one_fn_attach_in_order() {
    let toks = Lexer::with_source_name(
        "defmodule M do\n\
          @spec add1(integer) :: integer\n\
          @spec add1(float) :: float\n\
          fn add1(n), do: n + 1\n\
        end\n",
        "<test>",
    )
    .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
    .unwrap();
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
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
    let specs = add1
        .attrs
        .iter()
        .filter_map(|a| match a {
            Attribute::Spec(s) => Some(s),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(specs.len(), 2);
    assert_eq!(specs[0].name, "add1");
    assert_eq!(specs[1].name, "add1");
    assert_eq!(specs[0].param_body_tokens.len(), 1);
    assert_eq!(specs[1].param_body_tokens.len(), 1);
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
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &m.attrs).unwrap();
    let r = resolve_spec_decl(&mut ct, spec, &env);
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
    let mut ct = crate::types::new();
    let env = build_module_type_env(&mut ct, &m.attrs).unwrap();
    let resolved = resolve_spec_decl(&mut ct, spec, &env).unwrap();
    let int = ct.int();
    assert!(ct.is_equivalent(&resolved.params[0], &int));
    assert!(ct.is_equivalent(&resolved.result, &int));
}

#[test]
fn type_alias_at_top_level_errors() {
    let toks = Lexer::with_source_name("@type id :: integer\nfn main(), do: nil", "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    let r = Parser::new(toks).parse_program(&crate::telemetry::ConfiguredTelemetry::new());
    assert!(r.is_err(), "@type at top level must error; got {:?}", r);
}

#[test]
fn unknown_attribute_errors() {
    let toks = Lexer::with_source_name("@bogus \"x\"\nfn main(), do: nil", "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    let r = Parser::new(toks).parse_program(&crate::telemetry::ConfiguredTelemetry::new());
    assert!(r.is_err());
}

#[test]
fn moduledoc_at_top_level_errors() {
    let toks = Lexer::with_source_name("@moduledoc \"x\"\nfn main(), do: nil", "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap();
    let r = Parser::new(toks).parse_program(&crate::telemetry::ConfiguredTelemetry::new());
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
        let Item::Module(m) = &*pre.items[0] else { panic!() };
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
        let Expr::Call(callee, _) = &body.node else { panic!() };
        callee.span
    };

    let mut ct = crate::types::new();
    let post = flatten_modules(&mut ct, pre, &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten");
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

    let mut ct = crate::types::new();
    let post = flatten_modules(&mut ct, pre, &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten");
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
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
        ExportKey::new(enumerable.child("List".to_string()), "reduce", 3)
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
fn protocol_domain_refines_concrete_element_parameter() {
    let mut ct = crate::types::new();
    let p = flatten_modules(
        &mut ct,
        parse(
            r#"
defprotocol Enumerable do
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: acc
end

defmodule Consumer do
  fn use(xs), do: 1
end
"#,
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("flatten");

    let env = &p.module_type_envs["Consumer"];
    let parse_dom = |ct: &mut DefaultTypes, src: &str| {
        let toks = Lexer::with_source_name(src, "<test>")
            .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("lex");
        let (ty, _) = parse_type_expr(ct, &toks, env).expect("parse");
        ty
    };
    let refined = parse_dom(&mut ct, "Enumerable.t(integer)");
    let bare = parse_dom(&mut ct, "Enumerable.t");

    let int = ct.int();
    let atom = ct.atom();
    let list_int = ct.list(int);
    let list_atom = ct.list(atom);

    // The concrete element refines the List target to `list(integer)`.
    assert!(ct.is_subtype(&list_int, &refined));
    assert!(
        !ct.is_subtype(&list_atom, &refined),
        "a refined `Enumerable.t(integer)` must exclude `list(atom)`"
    );
    // The bare domain stays element-agnostic (`list(any)`), so it still
    // admits `list(atom)` — proving the refinement genuinely narrows.
    assert!(ct.is_subtype(&list_atom, &bare));
}

#[test]
fn protocol_impl_must_cover_declared_callbacks() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect_err("missing callback must fail");

    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_PROTOCOL);
    assert!(d.message.contains("missing callback `each/1`"));
}

#[test]
fn duplicate_protocol_impls_are_rejected() {
    let mut ct = crate::types::new();
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
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect_err("duplicate impl must fail");

    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_PROTOCOL);
    assert!(d.message.contains("already has an implementation"));
    // Both the duplicate and the first implementation are pointed at.
    assert_eq!(d.secondaries.len(), 1);
    assert!(d.secondaries[0].label.contains("first implementation"));
}

#[test]
fn protocol_impl_wrong_arity_is_an_arity_mismatch_not_missing() {
    let mut ct = crate::types::new();
    let err = flatten_modules(
        &mut ct,
        parse(
            r#"
defprotocol P do
  fn each(x)
end

defimpl P, for: List do
  fn each(x, extra), do: x
end
"#,
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect_err("arity mismatch must fail");

    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_PROTOCOL);
    assert!(
        d.message.contains("at arity 2") && d.message.contains("`each/1`"),
        "expected arity-mismatch diagnostic naming both arities, got: {}",
        d.message
    );
    assert!(
        !d.message.contains("missing callback") && !d.message.contains("unknown callback"),
        "arity mismatch must not degrade to missing/unknown, got: {}",
        d.message
    );
}

#[test]
fn protocol_callback_validation_preserves_overload_sets() {
    let mut ct = crate::types::new();
    let p = flatten_modules(
        &mut ct,
        parse(
            r#"
defprotocol P do
  @spec pick(integer) :: integer
  @spec pick(float) :: float
  fn pick(value)
end

defimpl P, for: List do
  @spec pick(integer) :: integer
  @spec pick(float) :: float
  fn pick(value), do: value
end
"#,
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("overload-compatible impl must pass");

    let protocol = ModuleName::from_segments(vec!["P".to_string()]);
    let callback = &p.protocol_registry.protocols[&protocol].callbacks[0];
    assert_eq!(callback.specs.len(), 2);
    let implementation = p
        .protocol_registry
        .impls
        .values()
        .find(|fact| fact.protocol == protocol)
        .expect("impl fact");
    assert_eq!(implementation.callback_specs[&("pick".to_string(), 1)].len(), 2);
}

#[test]
fn protocol_callback_validation_rejects_uncovered_impl_overload() {
    let mut ct = crate::types::new();
    let err = flatten_modules(
        &mut ct,
        parse(
            r#"
defprotocol P do
  @spec pick(integer) :: integer
  fn pick(value)
end

defimpl P, for: List do
  @spec pick(integer) :: integer
  @spec pick(float) :: float
  fn pick(value), do: value
end
"#,
        ),
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect_err("uncovered impl overload must fail");

    let d = err.to_diagnostic();
    assert_eq!(d.code, codes::RESOLVE_PROTOCOL);
    assert!(d.message.contains("callback `pick/1` parameter 1 is incompatible"));
}
