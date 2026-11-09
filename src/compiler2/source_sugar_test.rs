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
        .map(|stamp| stamp.atom_name().expect("the stamp is an atom"))
}

#[test]
fn a_rewritten_concatenation_operator_carries_the_operator_it_came_from() {
    assert_eq!(stamp_after_rewriting("a <> b\n").as_deref(), Some("<>"));
    assert_eq!(stamp_after_rewriting("a ++ b\n").as_deref(), Some("++"));
}

#[test]
fn the_other_rewritten_operators_carry_no_stamp() {
    assert_eq!(stamp_after_rewriting("a -- b\n"), None);
    assert_eq!(stamp_after_rewriting("a in b\n"), None);
}
