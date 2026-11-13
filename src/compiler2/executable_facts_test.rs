use super::*;

fn dispatch_projection(world: &mut World, ty: Ty) -> RuntimeDemand {
    let any = world.types_mut().any();
    let mut builder = RuntimeDemandTypeBuilder::new(any);
    prepare_type_projection(world, &mut builder, ty);
    builder.dispatch_demand(ty)
}

/// A value that dispatch reads must stay in the executable ABI, so reading an
/// empty tuple, or a tuple of empty tuples, is never an ignored input.
#[test]
fn a_dispatch_read_of_a_zero_width_tuple_is_present() {
    let mut world = World::new();
    let empty = world.types_mut().tuple(&[]);
    let nested = world.types_mut().tuple(&[empty]);
    assert_eq!(dispatch_projection(&mut world, empty), RuntimeDemand::whole());
    assert!(!dispatch_projection(&mut world, nested).is_ignore());
}

/// A tuple with a wide field keeps its per-field demand.
#[test]
fn a_dispatch_read_of_a_wide_tuple_keeps_its_field_demands() {
    let mut world = World::new();
    let one = world.types_mut().int_lit(1);
    let tuple = world.types_mut().tuple(&[one]);
    let demand = dispatch_projection(&mut world, tuple);
    assert!(!demand.is_ignore());
    assert_ne!(demand, RuntimeDemand::whole());
}

/// Building a body's value tables and its value origins reads each value by
/// its number in the body: no value id is ever hashed.
#[test]
fn a_bodys_value_tables_are_built_without_hashing_a_value_id() {
    use crate::compiler2::body::value_id_hashes;
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};
    use crate::modules::identity::ModuleName;
    use crate::telemetry::ConfiguredTelemetry;

    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("value_tables.fz".into()),
        text: r#"
defmodule Tables do
  def pairs(list, acc) do
    case list do
      [] -> acc
      [head | tail] -> pairs(tail, [{head, head * 2} | acc])
    end
  end
end
"#
        .into(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("value_tables_main.fz".into()),
        text: "require Tables\ndef main(), do: length(Tables.pairs([1, 2, 3], []))\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(3));
    let module = compiler
        .world_mut()
        .reference_module(ModuleName::parse_dotted("Tables").unwrap());
    let pairs = compiler.world_mut().reference_function(module, "pairs", 2);
    let body = compiler.world().lowered_body(pairs);
    let LoweredBody::Clauses {
        clauses,
        entries,
        generated,
        ..
    } = &*body;

    let before = value_id_hashes::so_far();
    let rebuilt = LoweredBody::clauses(clauses.clone(), entries.clone(), generated.clone());
    let origins = collect_value_origins(&rebuilt, &collect_callsite_return_origins(&rebuilt));
    let hashed = value_id_hashes::so_far() - before;

    assert!(
        !origins.is_empty(),
        "the body defines values whose origins are collected"
    );
    assert_eq!(hashed, 0, "{hashed} value ids were hashed while building the tables");
}
