use super::*;

#[test]
fn runtime_library_sources_resolve_like_user_interfaces() {
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
        interface_table(&crate::telemetry::ConfiguredTelemetry::new()),
        &crate::telemetry::ConfiguredTelemetry::new(),
    ) {
        Ok(_) => {}
        Err(_) => panic!("runtime interfaces resolve like user module interfaces"),
    }
}

#[test]
fn primitive_prelude_imports_kernel_without_defmodule_body() {
    let prelude = primitive_prelude_program(&crate::telemetry::ConfiguredTelemetry::new());
    assert!(prelude.items.iter().all(|item| !matches!(&**item, Item::Module(_))));
    assert!(
        prelude
            .items
            .iter()
            .any(|item| matches!(&**item, Item::Import { path, .. } if path.dotted() == "Kernel"))
    );
}
