use std::rc::Rc;

use super::{
    QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceFingerprintPolicy, QuotedSourceHeap,
    QuotedSourceMetadata, QuotedSourceRoot, QuotedSourceSpan,
};

fn context(kind: QuotedLexicalContextKind, module: &[&str], scope: &[&str], namespace_id: u32) -> QuotedLexicalContext {
    QuotedLexicalContext::new(
        kind,
        module.iter().map(|segment| (*segment).to_string()).collect(),
        scope.iter().map(|segment| (*segment).to_string()).collect(),
    )
    .with_namespace_id(namespace_id)
}

fn meta(context: &QuotedLexicalContext, source_name: &str, line: u32) -> QuotedSourceMetadata {
    QuotedSourceMetadata {
        lexical_context: Some(context.clone()),
        span: Some(QuotedSourceSpan::new(source_name, line, 1, 3)),
    }
}

fn build_simple_def(
    source_name: &str,
    line: u32,
    namespace_id: u32,
    module: &[&str],
    literal: i64,
) -> QuotedSourceRoot {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let ctx = context(QuotedLexicalContextKind::Source, module, &["foo"], namespace_id);
    let fn_meta = meta(&ctx, source_name, line);
    let head_meta = meta(&ctx, source_name, line + 1);
    let var_meta = meta(&ctx, source_name, line + 2);
    let body_meta = meta(&ctx, source_name, line + 3);

    let x = builder.variable("x", &var_meta).expect("x var");
    let head = builder.call("foo", &head_meta, &[x]).expect("foo head");
    let body = builder
        .call("+", &body_meta, &[x, builder.int(literal)])
        .expect("body expression");
    let do_kw = builder.keyword("do", body).expect("do keyword");
    let kw = builder.list(&[do_kw]).expect("keyword list");
    let def = builder.call("def", &fn_meta, &[head, kw]).expect("def form");

    builder.root(def).expect("quoted source root")
}

#[test]
fn heap_and_root_form_the_stable_source_key() {
    let left = build_simple_def("left.fz", 10, 11, &["App"], 1);
    let right = build_simple_def("right.fz", 90, 11, &["App"], 1);

    assert_ne!(
        left.key(),
        right.key(),
        "equivalent quoted source on different heaps should still be distinct source keys"
    );
    assert_eq!(
        left.key(),
        left.key(),
        "{{heap, root}} should be a stable handle for one source root"
    );
}

#[test]
fn semantic_fingerprint_ignores_span_noise() {
    let left = build_simple_def("left.fz", 10, 11, &["App"], 1);
    let right = build_simple_def("right.fz", 90, 11, &["App"], 1);

    assert_eq!(
        left.fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("left semantic fingerprint")
            .digest,
        right
            .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("right semantic fingerprint")
            .digest,
        "semantic fingerprint should follow source shape and lexical context, not span metadata"
    );

    let left_diag = left
        .fingerprint(QuotedSourceFingerprintPolicy::Diagnostic)
        .expect("left diagnostic fingerprint");
    let right_diag = right
        .fingerprint(QuotedSourceFingerprintPolicy::Diagnostic)
        .expect("right diagnostic fingerprint");
    assert_ne!(
        left_diag.digest, right_diag.digest,
        "diagnostic fingerprint should change when the caller opts spans into the fingerprint"
    );
}

#[test]
fn namespace_id_is_transport_only_and_not_part_of_fingerprint() {
    let left = build_simple_def("app.fz", 10, 11, &["App"], 1);
    let right = build_simple_def("app.fz", 10, 77, &["App"], 1);

    assert_eq!(
        left.fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("left semantic")
            .digest,
        right
            .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("right semantic")
            .digest,
        "ephemeral namespace ids should not churn semantic fingerprints"
    );
    assert_eq!(
        left.fingerprint(QuotedSourceFingerprintPolicy::Diagnostic)
            .expect("left diagnostic")
            .digest,
        right
            .fingerprint(QuotedSourceFingerprintPolicy::Diagnostic)
            .expect("right diagnostic")
            .digest,
        "diagnostic fingerprint should stay stable across namespace-id transport changes too"
    );
}

#[test]
fn lexical_context_and_literals_both_move_semantic_fingerprint() {
    let app = build_simple_def("app.fz", 10, 11, &["App"], 1);
    let helpers = build_simple_def("app.fz", 10, 11, &["Helpers"], 1);
    let changed_body = build_simple_def("app.fz", 10, 11, &["App"], 2);

    assert_ne!(
        app.fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("app semantic")
            .digest,
        helpers
            .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("helpers semantic")
            .digest,
        "semantic fingerprint should include lexical context"
    );
    assert_ne!(
        app.fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("app semantic")
            .digest,
        changed_body
            .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
            .expect("changed semantic")
            .digest,
        "semantic fingerprint should change when the quoted body changes"
    );
}

#[test]
fn cursor_reads_definition_and_caller_contexts_separately() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let definition_ctx = context(QuotedLexicalContextKind::Definition, &["Helpers"], &["twice"], 21);
    let caller_ctx = context(QuotedLexicalContextKind::Caller, &["App"], &["main"], 42);

    let arg = builder
        .variable("x", &meta(&caller_ctx, "helpers.fz", 12))
        .expect("caller var");
    let call = builder
        .call("double", &meta(&definition_ctx, "helpers.fz", 13), &[arg])
        .expect("definition call");
    let root = builder.root(call).expect("quoted source root");

    let node = root.cursor().ast_node().expect("call cursor").expect("ast node");
    assert_eq!(node.head, "double");

    let call_ctx = node
        .meta
        .map_value("__fz_lexical__")
        .expect("call lexical lookup")
        .expect("call lexical context");
    assert_eq!(
        call_ctx
            .map_value("kind")
            .expect("call kind lookup")
            .expect("call kind")
            .atom_name()
            .expect("call kind atom"),
        "definition"
    );
    assert_eq!(
        call_ctx
            .map_value("module")
            .expect("call module lookup")
            .expect("call module")
            .list_atom_names()
            .expect("call module atoms"),
        vec!["Helpers".to_string()]
    );

    let args = node.tail.list_items().expect("call args");
    let arg_node = args[0].ast_node().expect("arg node cursor").expect("arg ast node");
    assert_eq!(arg_node.head, "x");
    assert_eq!(
        arg_node
            .tail
            .map_value("kind")
            .expect("arg kind lookup")
            .expect("arg kind")
            .atom_name()
            .expect("arg kind atom"),
        "caller"
    );
    assert_eq!(
        arg_node
            .tail
            .map_value("module")
            .expect("arg module lookup")
            .expect("arg module")
            .list_atom_names()
            .expect("arg module atoms"),
        vec!["App".to_string()]
    );
}

#[test]
fn worked_surface_examples_fit_in_one_quoted_source_model() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let ctx = context(QuotedLexicalContextKind::Source, &["App"], &["macro_surface"], 9);
    let meta = meta(&ctx, "surface.fz", 5);

    let x = builder.variable("x", &meta).expect("x var");
    let inc_head = builder.call("inc", &meta, &[x]).expect("inc head");
    let inc_body = builder.call("+", &meta, &[x, builder.int(1)]).expect("inc body");
    let inc_kw = builder
        .list(&[builder.keyword("do", inc_body).expect("inc do")])
        .expect("inc kw");
    let defmacro_inc = builder
        .call("defmacro", &meta, &[inc_head, inc_kw])
        .expect("defmacro inc");

    let helpers_alias = builder.alias(&meta, &["Helpers"]).expect("Helpers alias");
    let module_body = builder
        .list(&[builder.call("double", &meta, &[builder.int(1)]).expect("double body")])
        .expect("module body");
    let defmodule_helpers = builder
        .call(
            "defmodule",
            &meta,
            &[
                helpers_alias,
                builder
                    .list(&[builder.keyword("do", module_body).expect("module do")])
                    .expect("module kw"),
            ],
        )
        .expect("defmodule");

    let import_helpers = builder
        .call(
            "import",
            &meta,
            &[
                builder.alias(&meta, &["Helpers"]).expect("import alias"),
                builder
                    .list(&[builder
                        .keyword(
                            "only",
                            builder
                                .list(&[builder
                                    .tuple(&[builder.atom("twice"), builder.int(1)])
                                    .expect("only entry")])
                                .expect("only list"),
                        )
                        .expect("only keyword")])
                    .expect("import kw"),
            ],
        )
        .expect("import");

    let test_call = builder
        .call(
            "test",
            &meta,
            &[
                builder.atom("name"),
                builder
                    .list(&[builder.keyword("do", builder.int(42)).expect("test do")])
                    .expect("test kw"),
            ],
        )
        .expect("test form");

    let root = builder
        .root(
            builder
                .list(&[defmacro_inc, defmodule_helpers, import_helpers, test_call])
                .expect("surface list"),
        )
        .expect("surface root");
    let semantic = root
        .fingerprint(QuotedSourceFingerprintPolicy::Semantic)
        .expect("surface semantic fingerprint");

    assert!(
        semantic.canonical.contains("atom:defmacro")
            && semantic.canonical.contains("atom:defmodule")
            && semantic.canonical.contains("atom:import")
            && semantic.canonical.contains("atom:test"),
        "one quoted-source graph should carry macro defs, module defs, imports, and item-level macro surfaces"
    );
}
