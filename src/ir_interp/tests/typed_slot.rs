use crate::ir_interp::*;
use crate::lexer::Lexer;
use crate::parser::Parser;
use fz_runtime::any_value::ValueKind;

use crate::fz_ir::Module;

fn lower_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    crate::ir_lower::lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower")
}

fn run(src: &str) -> i64 {
    let m = lower_src(src);
    run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run")
}

fn capture(src: &str) -> String {
    let m = lower_src(src);
    let _ = fz_runtime::ir_runtime::test_capture_take();
    run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run");
    fz_runtime::ir_runtime::test_capture_take().join("\n")
}

#[test]
fn interp_typed_int_arithmetic_full_i64() {
    assert_eq!(
        run("fn main(), do: 4611686018427387904 + 7"),
        4611686018427387911
    );
}

#[test]
fn interp_typed_float_raw() {
    assert_eq!(f64::from_bits(run("fn main(), do: 1.5 + 2.5") as u64), 4.0);
}

#[test]
fn interp_render_raw_float_in_container() {
    assert_eq!(capture("fn main(), do: print([1.5])"), "[1.5]");
}

#[test]
fn interp_equality_float_in_container() {
    assert_eq!(run("fn main(), do: [1.5] == [1.5]"), 1);
}

#[test]
fn interp_receive_matcher_float_in_container() {
    assert_eq!(
        run(r#"
            fn main() do
              send(self(), [2.5])
              receive do
                [2.5] -> 7
              end
            end
        "#),
        7
    );
}

#[test]
fn interp_deep_copy_float_in_container_preserves_raw_slot() {
    run(r#"
        fn main() do
          send(self(), [2.5])
          nil
        end
    "#);

    INTERP_TASKS.with(|tasks| {
        let tasks = tasks.borrow();
        let task = tasks.get(&1).expect("main task remains registered");
        let any_ref = task.mailbox.front().expect("self-send remains queued");
        assert_eq!(any_ref.tag(), ValueKind::LIST);
        let list = any_ref.list_addr().expect("mailbox keeps tagged list ref");
        let head = unsafe { (*(list as *const fz_runtime::any_value::ListCons)).head_value() };
        assert_eq!(head.kind(), fz_runtime::any_value::ValueKind::FLOAT);
        assert_eq!(f64::from_bits(head.raw()), 2.5);
    });
}

#[test]
fn interp_typed_int_send_receive_boundary() {
    assert_eq!(
        run(r#"
            fn main() do
              send(self(), 4611686018427387904)
              receive()
            end
            "#,),
        4611686018427387904
    );
}

#[test]
fn interp_typed_int_list_head_boundary() {
    assert_eq!(
        run(r#"
            fn first([h | _]), do: h
            fn main(), do: first([4611686018427387904])
        "#),
        4611686018427387904
    );
}

#[test]
fn interp_typed_int_map_get_boundary() {
    assert_eq!(
        run("fn main(), do: %{answer: 4611686018427387904}.answer"),
        4611686018427387904
    );
}

#[test]
fn interp_ref_bifs_read_scalars_from_list_map_and_tuple() {
    assert_eq!(
        capture(
            r#"
            fn tuple_second({_, x}), do: x
            fn list_head([h | _]), do: h
            fn main() do
              print({list_head([7]), %{answer: 42}.answer, tuple_second({:ok, 1.5})})
            end
        "#
        ),
        "{7, 42, 1.5}"
    );
}

#[test]
fn interp_ref_bifs_read_heap_values_from_list_map_and_tuple() {
    assert_eq!(
        capture(
            r#"
            fn tuple_second({_, x}), do: x
            fn list_head([h | _]), do: h
            fn main() do
              print({list_head([[1]]), %{child: [2]}.child, tuple_second({:ok, [3]})})
            end
        "#
        ),
        "{[1], [2], [3]}"
    );
}

#[test]
fn interp_typed_int_dispatch_and_return_flow() {
    assert_eq!(
        run(r#"
            fn bump(x :: integer), do: x + 7
            fn bump(_), do: 0
            fn main(), do: bump(4611686018427387904)
        "#),
        4611686018427387911
    );
}

#[test]
fn interp_typed_int_sender_wakes_blocked_receiver() {
    assert_eq!(
        run(r#"
            fn child(parent) do
              send(parent, 4611686018427387904)
            end
            fn main() do
              me = self()
              spawn(fn () -> child(me))
              receive()
            end
        "#),
        4611686018427387904
    );
}
