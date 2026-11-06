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
