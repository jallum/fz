//! The env a macro reads as `__CALLER__` is a `%Macro.Env{}` projected from
//! the caller's scope.

use std::rc::Rc;

use fz_runtime::any_value::ValueKind;

use super::env_projection::CallSite;
use super::identity::DeclaredCallableKind;
use super::quoted_expander::ExpansionContext;
use super::{ModuleId, NamespaceSymbol, QuotedSourceCursor, QuotedSourceHeap, ScopeSnapshot, World};
use crate::modules::identity::ModuleName;
use crate::source::{SourceMap, Span};

fn module(world: &mut World, dotted: &str) -> ModuleId {
    world.reference_module(ModuleName::parse_dotted(dotted).unwrap())
}

fn callable(
    world: &mut World,
    module: ModuleId,
    name: &str,
    arity: usize,
    kind: DeclaredCallableKind,
) -> NamespaceSymbol {
    let function = world.reference_declared_callable(module, name, arity, kind);
    match kind {
        DeclaredCallableKind::Function => NamespaceSymbol::Function(function),
        DeclaredCallableKind::Macro => NamespaceSymbol::Macro(function),
    }
}

fn no_site() -> CallSite {
    CallSite::locate(None, &SourceMap::default())
}

/// The value as Elixir prints it, so a test reads the shape it expects.
fn render(value: &QuotedSourceCursor) -> String {
    match value.root().tag() {
        ValueKind::ATOM => value.atom_name().unwrap().to_string(),
        ValueKind::INT => value.int_value().unwrap().to_string(),
        ValueKind::BITSTRING | ValueKind::BINVIEW => format!("{:?}", value.utf8_binary_text().unwrap()),
        ValueKind::MAP => {
            let entries: Vec<_> = value
                .map_entries()
                .unwrap()
                .iter()
                .map(|(key, entry)| format!("{} => {}", render(key), render(entry)))
                .collect();
            format!("%{{{}}}", entries.join(", "))
        }
        ValueKind::LIST => {
            let items: Vec<_> = value.list_items().unwrap().iter().map(render).collect();
            format!("[{}]", items.join(", "))
        }
        ValueKind::STRUCT => {
            let items: Vec<_> = value.tuple_items().unwrap().iter().map(render).collect();
            format!("{{{}}}", items.join(", "))
        }
        other => panic!("unexpected {other:?}"),
    }
}

fn env_field(world: &World, scope: ScopeSnapshot, context: ExpansionContext, site: &CallSite, field: &str) -> String {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let env = builder
        .root(world.project_env_value(&builder, scope, context, site).unwrap())
        .unwrap();
    render(
        &env.cursor()
            .map_value(field)
            .unwrap()
            .unwrap_or_else(|| panic!("no field {field}")),
    )
}

#[test]
fn an_env_is_a_macro_env_struct_with_every_field_elixir_gives_it() {
    let mut world = World::new();
    let main = module(&mut world, "Main");
    let function = world.reference_function(main, "run", 2);
    let scope = ScopeSnapshot::function(main, world.prelude_head(), function);
    let site = no_site();
    let field = |name| env_field(&world, scope, ExpansionContext::Expression, &site, name);

    assert_eq!(field("__struct__"), "Elixir.Macro.Env");
    assert_eq!(field("function"), "{run, 2}");
    assert_eq!(field("context"), "nil");
    assert_eq!(field("context_modules"), "[Elixir.Main]");
    assert_eq!(field("lexical_tracker"), "nil");
    assert_eq!(field("tracers"), "[]");
    assert_eq!(field("macro_aliases"), "[]");
    assert_eq!(field("versioned_vars"), "%{}");
}

#[test]
fn an_env_outside_any_module_has_no_module_function_or_context_modules() {
    let world = World::new();
    let scope = ScopeSnapshot::module(ModuleId::GLOBAL, world.prelude_head());
    let site = no_site();
    let field = |name| env_field(&world, scope, ExpansionContext::Expression, &site, name);

    assert_eq!(field("module"), "nil");
    assert_eq!(field("function"), "nil");
    assert_eq!(field("context_modules"), "[]");
}

#[test]
fn an_env_reports_the_expansion_context_as_the_atom_elixir_does() {
    let world = World::new();
    let scope = ScopeSnapshot::module(ModuleId::GLOBAL, world.prelude_head());
    let site = no_site();
    let context = |context| env_field(&world, scope, context, &site, "context");

    assert_eq!(context(ExpansionContext::Expression), "nil");
    assert_eq!(context(ExpansionContext::Match), "match");
    assert_eq!(context(ExpansionContext::Guard), "guard");
}

#[test]
fn an_env_names_the_file_and_line_of_the_call_site() {
    let mut source_map = SourceMap::default();
    let version = source_map.add_code(Some("lib/app.fz"), "first\nsecond\nthird\n");
    let on_third_line = Span::new(version, 13, 18);
    let nameless = source_map.add_code(None::<String>, "only\n");

    let world = World::new();
    let scope = ScopeSnapshot::module(ModuleId::GLOBAL, world.prelude_head());
    let field = |site: CallSite, name| env_field(&world, scope, ExpansionContext::Expression, &site, name);
    let at = |span| CallSite::locate(span, &source_map);

    assert_eq!(field(at(Some(on_third_line)), "file"), "\"lib/app.fz\"");
    assert_eq!(field(at(Some(on_third_line)), "line"), "3");
    assert_eq!(field(at(Some(Span::new(nameless, 0, 4))), "file"), "\"nofile\"");
    assert_eq!(field(at(None), "file"), "\"nofile\"");
    assert_eq!(field(at(None), "line"), "0");
    assert_ne!(
        at(Some(on_third_line)),
        at(Some(Span::new(version, 0, 5))),
        "each line is its own call site"
    );
}

#[test]
fn an_env_groups_imports_by_module_and_sorts_them_as_elixir_does() {
    let mut world = World::new();
    let main = module(&mut world, "Main");
    let inner = module(&mut world, "Inner");
    let enumm = module(&mut world, "Enum");
    let logger = module(&mut world, "Logger");
    let symbols = [
        (
            "zip",
            callable(&mut world, enumm, "zip", 2, DeclaredCallableKind::Function),
        ),
        (
            "map",
            callable(&mut world, enumm, "map", 2, DeclaredCallableKind::Function),
        ),
        ("f", callable(&mut world, inner, "f", 0, DeclaredCallableKind::Function)),
        ("m", callable(&mut world, inner, "m", 0, DeclaredCallableKind::Macro)),
        (
            "helper",
            callable(&mut world, main, "helper", 1, DeclaredCallableKind::Function),
        ),
    ];
    let mut head = world.prelude_head();
    for (name, symbol) in symbols {
        head = world.bind_namespace(head, name, symbol);
    }
    let stream = module(&mut world, "Stream");
    head = world.bind_required_module(head, logger);
    head = world.bind_required_module(head, stream);
    let scope = ScopeSnapshot::module(main, head);
    let site = no_site();
    let field = |name| env_field(&world, scope, ExpansionContext::Expression, &site, name);

    assert_eq!(
        field("functions"),
        "[{Elixir.Enum, [{map, 2}, {zip, 2}]}, {Elixir.Inner, [{f, 0}]}]",
        "a function the module itself defines is not an import"
    );
    assert_eq!(field("macros"), "[{Elixir.Inner, [{m, 0}]}]");
    assert_eq!(
        field("requires"),
        "[Elixir.Enum, Elixir.Inner, Elixir.Logger, Elixir.Stream]",
        "a module is required by `require` whether or not it has macros, and by importing from it"
    );
}

#[test]
fn an_env_lists_aliases_in_the_order_written_and_leaves_out_a_modules_own_name() {
    let mut world = World::new();
    let main = module(&mut world, "Main");
    let inner = module(&mut world, "Inner");
    let enumm = module(&mut world, "Enum");
    let nested = module(&mut world, "Main.Nested");
    let mut head = world.prelude_head();
    for (name, bound) in [
        ("In", inner),
        ("Inner", inner),
        ("Nested", nested),
        ("Enum", enumm),
        ("In", enumm),
    ] {
        head = world.bind_namespace(head, name, NamespaceSymbol::Module(bound));
    }
    let scope = ScopeSnapshot::module(main, head);
    let site = no_site();

    assert_eq!(
        env_field(&world, scope, ExpansionContext::Expression, &site, "aliases"),
        "[{Elixir.In, Elixir.Enum}, {Elixir.Nested, Elixir.Main.Nested}]",
        "a name bound again keeps its first place and takes its latest module"
    );
}
