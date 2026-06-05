use super::*;
use crate::compiler::Compiler;
use crate::telemetry::{Capture, ConfiguredTelemetry, NullTelemetry, Value};
use std::rc::Rc;

fn compiler() -> Compiler {
    Compiler::new()
}

fn runtime_module(name: &str) -> ModuleName {
    ModuleName::from_segments(vec![name.to_string()])
}

fn runtime_interface(compiler: &mut Compiler, name: &str) -> ModuleInterface {
    compiler
        .ensure_runtime_module_interface(&runtime_module(name), &NullTelemetry)
        .expect("runtime interface build")
        .unwrap_or_else(|| panic!("runtime module `{name}` should exist"))
}

fn parsed_runtime_modules(capture: &Capture) -> Vec<String> {
    capture
        .find(&["fz", "compiler", "parsed"])
        .into_iter()
        .filter_map(
            |ev| match (ev.metadata.get("module_origin"), ev.metadata.get("module_key")) {
                (Some(Value::Str(origin)), Some(Value::Str(module))) if origin == "embedded_runtime" => {
                    Some(module.to_string())
                }
                _ => None,
            },
        )
        .collect()
}

fn collect_primitive_contract_names(items: &[Rc<Item>], names: &mut Vec<String>) {
    for item in items {
        if let Item::Fn(def) = &**item
            && def.extern_abi.is_some()
        {
            names.push(format!("{}/{}", def.name, def.extern_params.len()));
        }
        if let Item::Module(module) = &**item {
            collect_primitive_contract_names(&module.items, names);
        }
    }
}

fn runtime_primitive_contract_names(compiler: &mut Compiler) -> Vec<String> {
    let mut names = Vec::new();
    collect_primitive_contract_names(
        &primitive_prelude_program(compiler.world_mut(), &NullTelemetry).items,
        &mut names,
    );
    for runtime_source in RUNTIME_MODULE_SOURCES {
        let module = runtime_module(runtime_source.name);
        let module_id = compiler
            .discover_runtime_module(&module, &NullTelemetry)
            .unwrap_or_else(|| panic!("runtime module `{module}` should be registered"));
        let parsed = compiler
            .ensure_prelude(module_id, &NullTelemetry)
            .unwrap_or_else(|diagnostic| panic!("parse runtime module `{module}`: {diagnostic:?}"));
        collect_primitive_contract_names(&parsed.items, &mut names);
    }
    names.sort();
    names
}

#[test]
fn runtime_library_interface_loading_is_lazy_per_module() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler"], capture.handler());

    let mut compiler = compiler();
    let utf8 = compiler
        .ensure_runtime_module_interface(&runtime_module("Utf8"), &tel)
        .expect("Utf8 interface build")
        .expect("Utf8 runtime module");

    assert_eq!(utf8.name, runtime_module("Utf8"));
    assert_eq!(compiler.module_count(), 1);
    assert_eq!(compiler.file_count(), 1);
    assert_eq!(
        parsed_runtime_modules(&capture),
        vec!["Utf8".to_string()],
        "loading Utf8's interface should not parse unrelated runtime modules"
    );
    assert_eq!(capture.count(&["fz", "compiler", "interface_ready"]), 1);

    compiler
        .validate_invariants()
        .expect("single runtime interface load should preserve compiler invariants");
}

#[test]
fn runtime_library_interfaces_expose_fz_functions_not_primitive_externs() {
    let mut compiler = compiler();

    let utf8 = runtime_interface(&mut compiler, "Utf8");
    let enumerable = runtime_interface(&mut compiler, "Enumerable");
    let list_module = runtime_interface(&mut compiler, "List");
    let range_module = runtime_interface(&mut compiler, "Range");
    let map_module = runtime_interface(&mut compiler, "Map");
    let enum_module = runtime_interface(&mut compiler, "Enum");
    let kernel = runtime_interface(&mut compiler, "Kernel");

    let exports = utf8
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    assert_eq!(exports, vec!["from_bytes/1", "from_bytes!/1", "to_bytes/1", "valid?/1"]);
    assert!(!exports.iter().any(|name| name.starts_with("fz_")));

    assert!(
        enumerable
            .protocols
            .iter()
            .any(|protocol| protocol.name.dotted() == "Enumerable")
    );
    assert!(enumerable.exports.is_empty());

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

    let enum_exports = enum_module
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    for export in ["count/1", "member?/2", "reduce/3", "slice/1", "sort/1", "sort/2"] {
        assert!(enum_exports.contains(&export.to_string()));
    }

    let kernel_exports = kernel
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    for export in ["<>/2", "+/2", "-/2", "*/2", "//2", "%/2"] {
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
        runtime_primitive_contract_names(&mut compiler),
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

    compiler
        .validate_invariants()
        .expect("runtime interface checks should preserve compiler invariants");
}

#[test]
fn runtime_library_implementation_dependencies_are_local_to_requested_module() {
    let mut compiler = compiler();

    assert_eq!(
        implementation_dependencies(compiler.world_mut(), &runtime_module("Process"), &NullTelemetry)
            .expect("Process implementation dependencies"),
        Vec::<ModuleName>::new(),
        "Process should not drag in unrelated runtime modules"
    );
    assert_eq!(
        implementation_dependencies(compiler.world_mut(), &runtime_module("Utf8"), &NullTelemetry)
            .expect("Utf8 implementation dependencies"),
        vec![runtime_module("Kernel")],
        "Utf8 should report only the implicit prelude runtime module it actually uses"
    );
    assert_eq!(
        implementation_dependencies(compiler.world_mut(), &runtime_module("Enum"), &NullTelemetry)
            .expect("Enum implementation dependencies"),
        vec![runtime_module("Enumerable"), runtime_module("Kernel")],
        "Enum should report the runtime modules it reaches directly or through implicit prelude operators/helpers"
    );

    compiler
        .validate_invariants()
        .expect("implementation dependency discovery should preserve compiler invariants");
}

#[test]
fn primitive_prelude_imports_kernel_without_defmodule_body() {
    let mut compiler = compiler();
    let prelude = primitive_prelude_program(compiler.world_mut(), &NullTelemetry);
    assert!(prelude.items.iter().all(|item| !matches!(&**item, Item::Module(_))));
    assert!(
        prelude
            .items
            .iter()
            .any(|item| matches!(&**item, Item::Import { path, .. } if path.dotted() == "Kernel"))
    );
}
