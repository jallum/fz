use std::rc::Rc;

use super::super::source_sugar::rewrite_source_sugar;
use super::super::{QuotedSourceHeap, QuotedSourceMetadata};

#[test]
fn successful_source_sugar_rewrites_are_stable_within_the_quoted_heap() {
    let sources = crate::source::SourceMap::default();
    for (name, source) in [("pipe", "41 |> outer()"), ("capture", "&outer(&1)")] {
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        let meta = QuotedSourceMetadata::default();
        let outer = builder.call("outer", &meta, &[]).expect("outer call");
        let source = match source {
            "41 |> outer()" => builder.call("|>", &meta, &[builder.int(41), outer]),
            "&outer(&1)" => {
                let arg = builder.call("&", &meta, &[builder.int(1)]).expect("capture arg");
                let outer = builder.call("outer", &meta, &[arg]).expect("captured outer call");
                builder.call("&", &meta, &[outer])
            }
            _ => unreachable!(),
        }
        .expect("source sugar");
        let root = builder.root(source).expect("quoted root");
        let node = root
            .cursor()
            .ast_node(&sources)
            .expect("quoted AST read")
            .expect("source sugar AST");

        let first = rewrite_source_sugar(&root, root.root(), &node, &sources)
            .expect("first rewrite")
            .expect("recognized source sugar");
        let second = rewrite_source_sugar(&root, root.root(), &node, &sources)
            .expect("second rewrite")
            .expect("memoized source sugar");

        assert_eq!(
            first, second,
            "{name} rewriting must retain one root identity for every retry"
        );
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use fz_runtime::any_value::{AnyValueRef, ValueKind};

    use super::super::{capture_arg_index, lambda_source_sugar_shape, range_parts};
    use crate::compiler2::{QuotedSourceHeap, QuotedSourceMetadata};
    use crate::source::SourceMap;

    #[test]
    fn sugar_shape_probes_propagate_invalid_atom_payloads() {
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        let unknown_atom_id = u64::MAX;
        let unknown_atom = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &unknown_atom_id)
            .expect("stack scalar is a valid temporary atom carrier");
        let node = builder
            .ast_node(unknown_atom, &QuotedSourceMetadata::default(), builder.empty_list())
            .expect("builder copies the scalar into its owned heap");
        let root = builder.root(node).expect("quoted source root");
        let cursor = root.cursor();
        let sources = SourceMap::new();

        for error in [
            range_parts(&cursor, &sources).expect_err("range probe must propagate invalid atom"),
            lambda_source_sugar_shape(std::slice::from_ref(&cursor), &sources)
                .expect_err("lambda probe must propagate invalid atom"),
            capture_arg_index(&cursor, &sources).expect_err("capture probe must propagate invalid atom"),
        ] {
            assert!(error.to_string().contains("unknown atom id"), "{error}");
        }
    }
}

fn stamp_after_rewriting(text: &str) -> Option<String> {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("operator.fz"), text);
    let root = super::super::parse_quoted_program(&sources, version, &tel).expect("quoted parse");
    let operator = root.cursor().list_items().expect("items").remove(0);
    let node = operator.ast_node(&sources).expect("node").expect("operator node");
    let rewritten = rewrite_source_sugar(&root, operator.root(), &node, &sources)
        .expect("rewrite")
        .expect("operator sugar");
    let call = root.builder().root(rewritten).expect("rewritten root");
    let rewritten_node = call.cursor().ast_node(&sources).expect("node").expect("call");
    rewritten_node
        .meta
        .map_value(super::super::source::META_FROM_OPERATOR_KEY)
        .expect("meta is a map")
        .map(|stamp| stamp.atom_name().expect("the stamp is an atom").to_string())
}

/// The operators a later decoder has to recognize again carry their stamp:
/// the concatenations read as patterns, and `in`, read as a rescue head.
#[test]
fn a_rewritten_operator_a_decoder_recognizes_carries_the_operator_it_came_from() {
    assert_eq!(stamp_after_rewriting("a <> b\n").as_deref(), Some("<>"));
    assert_eq!(stamp_after_rewriting("a ++ b\n").as_deref(), Some("++"));
    assert_eq!(stamp_after_rewriting("a in b\n").as_deref(), Some("in"));
}

#[test]
fn the_other_rewritten_operators_carry_no_stamp() {
    assert_eq!(stamp_after_rewriting("a -- b\n"), None);
}

/// The quoted form as one line: calls as `head(args)`, remote calls as
/// `Mod.fun(args)`, closure calls as `(var.)(args)`, lists as `[..]`, tuples
/// as `{..}`, and a generated variable as `name#ordinal`.
fn show(cursor: &crate::compiler2::QuotedSourceCursor, sources: &crate::source::SourceMap) -> String {
    use fz_runtime::any_value::ValueKind;
    let Some(node) = cursor.ast_node(sources).expect("node read") else {
        return match cursor.root().tag() {
            ValueKind::INT => cursor.int_value().expect("int").to_string(),
            ValueKind::ATOM => format!(":{}", cursor.atom_name().expect("atom")),
            ValueKind::LIST => format!(
                "[{}]",
                cursor
                    .list_items()
                    .expect("list")
                    .iter()
                    .map(|item| show(item, sources))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ValueKind::STRUCT => format!(
                "{{{}}}",
                cursor
                    .tuple_items()
                    .expect("tuple")
                    .iter()
                    .map(|item| show(item, sources))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            other => format!("<{other:?}>"),
        };
    };
    if !node.tail.is_list_like() {
        let name = node.head.atom_name().expect("variable name").to_string();
        return match node.meta.hygiene_ordinal().expect("hygiene") {
            Some(ordinal) => format!("{name}#{ordinal}"),
            None => name,
        };
    }
    let args = node
        .tail
        .list_items()
        .expect("args")
        .iter()
        .map(|arg| show(arg, sources))
        .collect::<Vec<_>>()
        .join(", ");
    if node.head.root().tag() == ValueKind::ATOM {
        let head = node.head.atom_name().expect("head");
        if head == "__aliases__" {
            return args.replace(", ", ".").replace(':', "");
        }
        return format!("{head}({args})");
    }
    let head = node.head.ast_node(sources).expect("head node").expect("head is a node");
    let head_args = head.tail.list_items().expect("head args");
    match head_args.as_slice() {
        [module, function] => format!(
            "{}.{}({args})",
            show(module, sources),
            show(function, sources).trim_start_matches(':')
        ),
        [fun] => format!("({}.)({args})", show(fun, sources)),
        _ => unreachable!("a call head is a dot over one or two parts"),
    }
}

fn rewrite_for(text: &str) -> Result<String, String> {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("comprehension.fz"), text);
    let root = super::super::parse_quoted_program(&sources, version, &tel).expect("quoted parse");
    let form = root.cursor().list_items().expect("items").remove(0);
    let node = form.ast_node(&sources).expect("node").expect("for node");
    let rewritten = rewrite_source_sugar(&root, form.root(), &node, &sources).map_err(|error| error.to_string())?;
    let rewritten = rewritten.expect("a for is source sugar");
    let rewritten = root.builder().root(rewritten).expect("rewritten root");
    Ok(show(&rewritten.cursor(), &sources))
}

#[test]
fn a_plain_comprehension_reverses_a_reduce_that_conses_the_body() {
    assert_eq!(
        rewrite_for("for x <- xs, do: x\n").unwrap(),
        "Enum.reverse(Enum.reduce(xs, [], fn(->([x, __fz_for_acc#0], [|(x, __fz_for_acc#0)]))))"
    );
}

#[test]
fn a_refutable_generator_pattern_skips_what_does_not_match() {
    assert_eq!(
        rewrite_for("for {a, b} <- xs, do: a\n").unwrap(),
        "Enum.reverse(Enum.reduce(xs, [], fn(->([__fz_for_elem#0, __fz_for_acc#0], \
         case(__fz_for_elem#0, [{:do, [->([{a, b}], [|(a, __fz_for_acc#0)]), ->([_], __fz_for_acc#0)]}])))))"
    );
}

#[test]
fn an_irrefutable_generator_pattern_has_no_skip_arm() {
    for text in ["for x <- xs, do: x\n", "for _x <- xs, do: 1\n", "for(_ <- xs, do: 1)\n"] {
        let rewritten = rewrite_for(text).unwrap();
        assert!(
            !rewritten.contains("case("),
            "{text} would carry a redundant clause: {rewritten}"
        );
        assert!(
            !rewritten.contains("->([_]"),
            "{text} would carry a skip arm: {rewritten}"
        );
    }
}

#[test]
fn a_filter_guards_the_step_and_keeps_the_accumulator_otherwise() {
    assert_eq!(
        rewrite_for("for x <- xs, x > 1, do: x\n").unwrap(),
        "Enum.reverse(Enum.reduce(xs, [], fn(->([x, __fz_for_acc#0], \
         if(>(x, 1), [{:do, [|(x, __fz_for_acc#0)]}, {:else, __fz_for_acc#0}])))))"
    );
}

#[test]
fn each_generator_threads_the_enclosing_accumulator_into_the_next_reduce() {
    assert_eq!(
        rewrite_for("for {k, v} <- m, v > 1, w <- ws, do: {k, w}\n").unwrap(),
        "Enum.reverse(Enum.reduce(m, [], fn(->([__fz_for_elem#0, __fz_for_acc#0], \
         case(__fz_for_elem#0, [{:do, [->([{k, v}], if(>(v, 1), [{:do, \
         Enum.reduce(ws, __fz_for_acc#0, fn(->([w, __fz_for_acc#1], [|({k, w}, __fz_for_acc#1)])))}, \
         {:else, __fz_for_acc#0}])), ->([_], __fz_for_acc#0)]}])))))"
    );
}

#[test]
fn into_collects_through_the_collectable_and_finishes_with_done() {
    assert_eq!(
        rewrite_for("for x <- xs, into: c, do: x\n").unwrap(),
        "__block__(=({__fz_for_init#0, __fz_for_fun#0}, Collectable.into(c)), \
         (__fz_for_fun#0.)(Enum.reduce(xs, __fz_for_init#0, \
         fn(->([x, __fz_for_acc#0], (__fz_for_fun#0.)(__fz_for_acc#0, {:cont, x})))), :done))"
    );
}

#[test]
fn reduce_starts_from_its_value_and_matches_the_accumulator_against_the_clauses() {
    assert_eq!(
        rewrite_for("for x <- xs, reduce: 0 do\n  acc -> acc + x\nend\n").unwrap(),
        "Enum.reduce(xs, 0, fn(->([x, __fz_for_acc#0], \
         case(__fz_for_acc#0, [{:do, [->([acc], +(acc, x))]}]))))"
    );
}

#[test]
fn the_variables_a_comprehension_generates_carry_generated_ordinals() {
    let rewritten = rewrite_for("for x <- xs, y <- ys, do: x + y\n").unwrap();
    for generated in ["__fz_for_acc#0", "__fz_for_acc#1"] {
        assert!(rewritten.contains(generated), "{generated} missing from {rewritten}");
    }
    assert!(
        !rewritten.contains("__fz_for_acc,") && !rewritten.contains("__fz_for_acc)"),
        "a generated variable lost its ordinal: {rewritten}"
    );
}

#[test]
fn a_comprehension_that_cannot_be_built_is_refused_naming_the_form() {
    for (text, message) in [
        ("for x <- xs, uniq: true, do: x\n", "comprehension `uniq:` is not built"),
        (
            "for <<c <- bin>>, do: c\n",
            "comprehension bitstring generators are not built",
        ),
        ("for 1, do: 2\n", "comprehension must start with a generator"),
        ("for 1, x <- xs, do: x\n", "comprehension must start with a generator"),
        (
            "for x <- xs, into: [], reduce: 0, do: x\n",
            "comprehension takes `into:` or `reduce:`, not both",
        ),
        (
            "for x <- xs, reduce: 0, do: x\n",
            "comprehension `reduce:` takes a `do` block of `->` clauses",
        ),
        ("for x <- xs\n", "comprehension needs a `do` body"),
    ] {
        assert_eq!(rewrite_for(text).unwrap_err(), message, "{text}");
    }
}
