use std::rc::Rc;

use super::source_sugar::rewrite_source_sugar;
use super::{QuotedSourceHeap, QuotedSourceMetadata};

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
