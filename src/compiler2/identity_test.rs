use super::{FunctionState, ModuleState, RootState, World};

#[test]
fn compiler2_identity_maps_promote_placeholders_and_preserve_reverse_lookup() {
    let mut world = World::new();

    let math_ref = world.modules_mut().reference_named("Math");
    let math_def = world.modules_mut().define_named("Math");
    assert_eq!(
        math_ref, math_def,
        "module definition should fill the referenced placeholder"
    );
    assert_eq!(world.modules().name(math_def), Some("Math"));
    assert_eq!(
        world.modules().get(math_def).map(|module| module.state()),
        Some(&ModuleState::Defined),
        "module should promote from placeholder to defined"
    );

    let add_ref = world.functions_mut().reference(math_def, "add", 2);
    let add_def = world.functions_mut().define(math_def, "add", 2);
    assert_eq!(
        add_ref, add_def,
        "function definition should fill the referenced placeholder"
    );
    let add_ref_data = world.functions().reference_for(add_def).expect("function ref");
    assert_eq!(add_ref_data.module, math_def);
    assert_eq!(add_ref_data.name, "add");
    assert_eq!(add_ref_data.arity, 2);
    assert_eq!(
        world.functions().get(add_def).map(|function| function.state()),
        Some(&FunctionState::Defined),
        "function should promote from placeholder to defined"
    );

    let repl_ref = world.roots_mut().reference_named("repl");
    let repl_def = world.roots_mut().define_named("repl");
    assert_eq!(
        repl_ref, repl_def,
        "root definition should fill the referenced placeholder"
    );
    assert_eq!(world.roots().name(repl_def), Some("repl"));
    assert_eq!(
        world.roots().get(repl_def).map(|root| root.state()),
        Some(&RootState::Defined),
        "root should promote from placeholder to defined"
    );
}
