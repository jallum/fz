use std::rc::Rc;

use fz_runtime::any_value::ValueKind;

use super::source::{META_SPAN_KEY, META_SPAN_LENGTH_KEY, META_SPAN_START_KEY, META_SPAN_VERSION_KEY};
use super::{
    Horizon, QuotedLexicalContext, QuotedLexicalContextKind, QuotedSourceCursor, QuotedSourceHeap,
    QuotedSourceMetadata, QuotedSourceRoot, parse_quoted_program,
};
use crate::modules::runtime_library;
use crate::source::{SourceVersion, Span};
use crate::telemetry::ConfiguredTelemetry;

/// Every atom name and UTF-8 binary payload reachable in a quoted graph, in
/// traversal order. Tests use this to assert a parse carried specific forms
/// without re-inventing a canonical rendering of the graph.
pub(super) fn quoted_tokens(root: &QuotedSourceRoot) -> Vec<String> {
    let mut tokens = Vec::new();
    collect_tokens(&root.cursor(), &mut tokens);
    tokens
}

fn collect_tokens(cursor: &QuotedSourceCursor, tokens: &mut Vec<String>) {
    match cursor.root().tag() {
        ValueKind::ATOM => tokens.push(cursor.atom_name().expect("atom name")),
        ValueKind::LIST => {
            for item in cursor.list_items().expect("list items") {
                collect_tokens(&item, tokens);
            }
        }
        ValueKind::STRUCT => {
            for item in cursor.tuple_items().expect("tuple items") {
                collect_tokens(&item, tokens);
            }
        }
        ValueKind::MAP => {
            for (key, value) in cursor.map_entries().expect("map entries") {
                collect_tokens(&key, tokens);
                collect_tokens(&value, tokens);
            }
        }
        ValueKind::BITSTRING | ValueKind::PROCBIN => {
            if let Ok(text) = cursor.utf8_binary_text() {
                tokens.push(text);
            }
        }
        _ => {}
    }
}

pub(super) fn assert_quoted_mentions(root: &QuotedSourceRoot, expected: &[&str]) {
    let tokens = quoted_tokens(root);
    for name in expected {
        assert!(
            tokens.iter().any(|token| token == name),
            "quoted source should mention `{name}`; tokens: {tokens:?}"
        );
    }
}

fn context(kind: QuotedLexicalContextKind, module: &[&str], scope: &[&str], namespace_id: u32) -> QuotedLexicalContext {
    QuotedLexicalContext::new(
        kind,
        module.iter().map(|segment| (*segment).to_string()).collect(),
        scope.iter().map(|segment| (*segment).to_string()).collect(),
    )
    .with_namespace_id(namespace_id)
}

// `_source_name` and `line` are arbitrary span noise: the byte-offset `Span`
// carries no source name, and these tests assert spans are not semantic content,
// so the helper just needs to vary the span by its `line` input.
fn meta(context: &QuotedLexicalContext, _source_name: &str, line: u32) -> QuotedSourceMetadata {
    let mut sources = crate::source::SourceMap::new();
    let version = sources.add_code(Some("quoted-structural-test.fz"), " ".repeat(256));
    QuotedSourceMetadata {
        module: None,
        from_brackets: false,
        lexical_context: Some(context.clone()),
        span: Some(Span::new(
            version,
            line,
            line.checked_add(3).expect("test span end fits in u32"),
        )),
    }
}

#[test]
fn module_reference_metadata_keeps_portable_identity_in_semantic_equality() {
    use crate::modules::identity::{ModuleDenotation, ModuleName};
    fn projected(module: ModuleDenotation) -> QuotedSourceRoot {
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        let meta = QuotedSourceMetadata {
            module: Some(module),
            ..Default::default()
        };
        builder.root(builder.alias(&meta, &["A", "B", "C"]).unwrap()).unwrap()
    }
    let name = |path| ModuleName::parse_dotted(path).unwrap();
    let left = ModuleDenotation::ProtocolImpl {
        protocol: name("A"),
        target: name("B.C"),
    };
    let right = ModuleDenotation::ProtocolImpl {
        protocol: name("A.B"),
        target: name("C"),
    };
    let first = projected(left.clone());
    let equal = projected(left.clone());
    let other_impl = projected(right.clone());
    let named = projected(ModuleDenotation::Named(name("A.B.C")));
    assert!(
        first.semantically_eq(&equal, Horizon::Full),
        "identity is portable across quoted heaps"
    );
    assert!(
        !first.semantically_eq(&other_impl, Horizon::Full),
        "the protocol/target boundary is semantic"
    );
    assert!(
        !first.semantically_eq(&named, Horizon::Full),
        "display equality cannot collapse an implementation into a named module"
    );
    for (root, expected) in [(first, left), (other_impl, right)] {
        assert_eq!(
            root.cursor()
                .ast_node(&crate::source::SourceMap::new())
                .unwrap()
                .unwrap()
                .meta
                .module_denotation()
                .unwrap(),
            Some(expected)
        );
    }
}

#[test]
fn malformed_module_reference_metadata_is_rejected_without_interning() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let empty = builder.list(&[]).unwrap();
    let path = builder.list(&[builder.atom("A")]).unwrap();
    let wrong = [
        builder.int(1),
        builder.tuple(&[]).unwrap(),
        builder.tuple(&[builder.atom("unknown"), path]).unwrap(),
        builder.tuple(&[builder.atom("named"), empty]).unwrap(),
        builder.tuple(&[builder.atom("named"), path, path]).unwrap(),
        builder.tuple(&[builder.atom("protocol_impl"), path]).unwrap(),
        builder.tuple(&[builder.atom("protocol_impl"), path, empty]).unwrap(),
    ];
    for value in wrong {
        let meta = builder
            .root(
                builder
                    .map(&[(builder.atom(super::source::META_MODULE_KEY), value)])
                    .unwrap(),
            )
            .unwrap();
        assert!(meta.cursor().module_denotation().is_err());
    }
}

fn encoded_ast_with_span(start: i64, length: i64, source_version: i64) -> QuotedSourceRoot {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let span = builder
        .map(&[
            (builder.atom(META_SPAN_START_KEY), builder.int(start)),
            (builder.atom(META_SPAN_LENGTH_KEY), builder.int(length)),
            (builder.atom(META_SPAN_VERSION_KEY), builder.int(source_version)),
        ])
        .expect("encoded span map");
    let meta = builder
        .map(&[(builder.atom(META_SPAN_KEY), span)])
        .expect("encoded metadata map");
    let node = builder
        .tuple(&[builder.atom("node"), meta, builder.nil()])
        .expect("encoded AST node");
    builder.root(node).expect("encoded AST root")
}

fn encoded_token(start: i64, end: i64, source_version: i64) -> QuotedSourceRoot {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let token = builder
        .tuple(&[
            builder.atom("ident"),
            builder.utf8_binary("integer").expect("token payload"),
            builder.int(start),
            builder.int(end),
            builder.bool(false),
            builder.int(source_version),
        ])
        .expect("encoded token");
    let tokens = builder.list(&[token]).expect("encoded token list");
    builder.root(tokens).expect("encoded token root")
}

#[test]
fn quoted_span_decoder_rejects_overflow_and_explicit_absence() {
    let sources = crate::source::SourceMap::default();
    let overflow = encoded_ast_with_span(i64::from(u32::MAX), 1, 0);
    assert!(
        overflow
            .cursor()
            .ast_node(&sources)
            .unwrap_err()
            .to_string()
            .contains("overflows u32")
    );

    let absent = encoded_ast_with_span(0, 0, i64::from(SourceVersion::NONE.as_u32()));
    assert!(
        absent
            .cursor()
            .ast_node(&sources)
            .unwrap_err()
            .to_string()
            .contains("does not resolve in the source map")
    );
}

#[test]
fn absent_quoted_span_metadata_is_not_malformed() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let meta = builder.map(&[]).expect("empty metadata");
    let node = builder
        .tuple(&[builder.atom("node"), meta, builder.nil()])
        .expect("source-less AST node");
    let root = builder.root(node).expect("source-less AST root");
    assert_eq!(
        root.cursor()
            .ast_node(&crate::source::SourceMap::default())
            .expect("absence is valid")
            .expect("AST node")
            .span,
        None
    );
}

#[test]
fn quoted_token_decoder_rejects_unregistered_source_versions() {
    let sources = crate::source::SourceMap::default();
    let encoded = encoded_token(0, 1, i64::from(u32::MAX - 1));
    assert!(
        super::token_payload::decode_tokens(&encoded.cursor(), &sources).is_err(),
        "token provenance must resolve through the authoritative source map"
    );
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

// Builder-constructed graphs (as opposed to parsed ones) carry hand-placed
// span metadata; spans are still not semantic content.
#[test]
fn built_graphs_compare_semantically_across_span_noise() {
    let left = build_simple_def("left.fz", 10, 11, &["App"], 1);
    let right = build_simple_def("right.fz", 90, 11, &["App"], 1);

    assert!(
        left.semantically_eq(&right, Horizon::Full),
        "semantic equality should follow source shape and lexical context, not span metadata"
    );
    assert!(
        left.semantically_eq(&right, Horizon::Surface),
        "span noise should not move the surface horizon either"
    );
}

#[test]
fn namespace_id_is_transport_only_not_semantic_content() {
    let left = build_simple_def("app.fz", 10, 11, &["App"], 1);
    let right = build_simple_def("app.fz", 10, 77, &["App"], 1);

    assert!(
        left.semantically_eq(&right, Horizon::Full),
        "ephemeral namespace ids should not churn semantic equality"
    );
}

#[test]
fn lexical_context_and_literals_both_move_semantic_equality() {
    let app = build_simple_def("app.fz", 10, 11, &["App"], 1);
    let helpers = build_simple_def("app.fz", 10, 11, &["Helpers"], 1);
    let changed_body = build_simple_def("app.fz", 10, 11, &["App"], 2);

    assert!(
        !app.semantically_eq(&helpers, Horizon::Full),
        "lexical context is semantic content"
    );
    assert!(
        !app.semantically_eq(&changed_body, Horizon::Full),
        "a changed quoted body is a semantic change at full depth"
    );
    assert!(
        app.semantically_eq(&changed_body, Horizon::Surface),
        "the changed literal lives under do: — below the surface horizon"
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

    let node = root
        .cursor()
        .trusted_ast_node()
        .expect("call cursor")
        .expect("ast node");
    assert_eq!(node.head.atom_name().expect("call head atom"), "double");

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
    let arg_node = args[0]
        .trusted_ast_node()
        .expect("arg node cursor")
        .expect("arg ast node");
    assert_eq!(arg_node.head.atom_name().expect("arg head atom"), "x");
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

    // One quoted-source graph should carry macro defs, module defs, imports,
    // and item-level macro surfaces.
    assert_quoted_mentions(&root, &["defmacro", "defmodule", "import", "test"]);
}

fn build_bulk_ast_list(last: i64) -> QuotedSourceRoot {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let ctx = context(QuotedLexicalContextKind::Source, &["App"], &["bulk"], 99);
    let node_meta = meta(&ctx, "bulk.fz", 1);
    let mut items = Vec::new();
    for n in 0..64 {
        let value = if n == 63 { last } else { n };
        items.push(
            builder
                .call("dbg", &node_meta, &[builder.int(value)])
                .expect("bulk dbg call"),
        );
    }
    builder
        .root(builder.list(&items).expect("bulk root list"))
        .expect("bulk root")
}

// Equality with an independently built copy can only hold if the walk visits
// every node; a difference confined to the final leaf proves it gets there.
#[test]
fn semantic_walk_reaches_the_last_leaf_of_long_ast_lists() {
    let first = build_bulk_ast_list(63);
    let second = build_bulk_ast_list(63);
    let tail_changed = build_bulk_ast_list(999);

    assert!(
        first.semantically_eq(&second, Horizon::Full),
        "independently built copies of a long quoted list should compare equal"
    );
    assert!(
        !first.semantically_eq(&tail_changed, Horizon::Full),
        "a difference in the final list item must be seen — the walk reaches the last leaf"
    );
}

#[test]
fn semantic_walk_handles_runtime_sized_quoted_roots() {
    let tel = ConfiguredTelemetry::new();
    for (name, source) in runtime_library::module_sources() {
        let mut left_sources = crate::source::SourceMap::default();
        let left_version = left_sources.add_code(Some(format!("runtime:{name}.fz")), source);
        let left = parse_quoted_program(&left_sources, left_version, &tel)
            .unwrap_or_else(|error| panic!("runtime source `{name}` should parse to quoted root: {error}"));
        let mut right_sources = crate::source::SourceMap::default();
        let right_version = right_sources.add_code(Some(format!("runtime:{name}.fz")), source);
        let right = parse_quoted_program(&right_sources, right_version, &tel)
            .unwrap_or_else(|error| panic!("runtime source `{name}` should re-parse to quoted root: {error}"));
        assert!(
            left.semantically_eq(&right, Horizon::Full),
            "runtime source `{name}` should walk to the leaves and compare equal across re-parse"
        );
        assert!(
            left.semantically_eq(&right, Horizon::Surface),
            "runtime source `{name}` should compare equal at the surface horizon across re-parse"
        );
    }
}

fn build_bitstring_heavy_list(last_payload: &str) -> QuotedSourceRoot {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let ctx = context(QuotedLexicalContextKind::Source, &["App"], &["bulk_bits"], 101);
    let node_meta = meta(&ctx, "bulk_bits.fz", 1);
    let payload = "abcdefghijklmnopqrstuvwxyz0123456789".repeat(8);
    let mut items = Vec::new();
    for n in 0..48 {
        let text = if n == 47 { last_payload } else { payload.as_str() };
        let node = builder
            .call(
                "@spec",
                &node_meta,
                &[builder.utf8_binary(text).expect("payload binary")],
            )
            .expect("bitstring-heavy node");
        items.push(node);
    }
    builder
        .root(builder.list(&items).expect("bitstring-heavy root list"))
        .expect("bitstring-heavy root")
}

#[test]
fn semantic_walk_compares_bitstring_payloads_in_long_lists() {
    let payload = "abcdefghijklmnopqrstuvwxyz0123456789".repeat(8);
    let first = build_bitstring_heavy_list(&payload);
    let second = build_bitstring_heavy_list(&payload);
    let tail_changed = build_bitstring_heavy_list("different payload");

    assert!(
        first.semantically_eq(&second, Horizon::Full),
        "independently built bitstring-heavy lists should compare equal"
    );
    assert!(
        !first.semantically_eq(&tail_changed, Horizon::Full),
        "a payload difference in the final bitstring must be seen — bitstrings compare by content"
    );
}

fn parse_src(name: &str, text: &str) -> QuotedSourceRoot {
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some(name), text);
    parse_quoted_program(&sources, version, &ConfiguredTelemetry::new()).expect("parse quoted program")
}

// Spans and source positions are not semantic content: the same code parsed
// under a different name or shifted by blank lines is semantically equal at
// every horizon.
#[test]
fn semantically_eq_ignores_span_and_position() {
    let a = parse_src("a.fz", "def foo(x), do: x + 1\n");
    let b = parse_src("b.fz", "\n\ndef foo(x), do: x + 1\n");
    assert!(
        a.semantically_eq(&b, Horizon::Full),
        "position is not semantic content (full)"
    );
    assert!(
        a.semantically_eq(&b, Horizon::Surface),
        "position is not semantic content (surface)"
    );
}

#[test]
fn semantic_map_keys_ignore_metadata_that_changes_runtime_order() {
    fn graph(reverse_spans: bool) -> QuotedSourceRoot {
        let mut sources = crate::source::SourceMap::new();
        let version = sources.add_code(Some("metadata-order.fz"), "ab");
        let heap = Rc::new(QuotedSourceHeap::new());
        let builder = heap.builder();
        let entries = ["a", "b"].into_iter().enumerate().map(|(index, name)| {
            let position = if reverse_spans { 1 - index } else { index } as u32;
            let metadata = builder
                .meta(&QuotedSourceMetadata {
                    span: Some(Span::new(version, position, position + 1)),
                    ..Default::default()
                })
                .unwrap();
            let key = builder.tuple(&[metadata, builder.atom(name)]).unwrap();
            (key, builder.int(index as i64))
        });
        let map = builder.map(&entries.collect::<Vec<_>>()).unwrap();
        builder.root(map).unwrap()
    }
    let left = graph(false);
    let right = graph(true);
    assert_eq!(left.cursor().map_entries().unwrap()[0].1.int_value(), Ok(0));
    assert_eq!(right.cursor().map_entries().unwrap()[0].1.int_value(), Ok(1));
    assert!(left.semantically_eq(&right, Horizon::Full));
}

// The function body is part of its definition (Full) but below the module
// surface (Surface): a body-only edit is a function change, not a module change.
#[test]
fn semantically_eq_full_sees_body_changes_but_surface_does_not() {
    let a = parse_src("f.fz", "def foo(x), do: x + 1\n");
    let b = parse_src("f.fz", "def foo(x), do: x + 2\n");
    assert!(
        !a.semantically_eq(&b, Horizon::Full),
        "the body is part of the function definition"
    );
    assert!(
        a.semantically_eq(&b, Horizon::Surface),
        "the do: body is below the module surface"
    );
}

// Signatures (name, arity, guards) are surface — they are above the do: body,
// so the surface horizon sees them change.
#[test]
fn semantically_eq_surface_sees_signature_changes() {
    let base = parse_src("f.fz", "def foo(x), do: x + 1\n");
    let renamed = parse_src("f.fz", "def bar(x), do: x + 1\n");
    let widened = parse_src("f.fz", "def foo(x, y), do: x + 1\n");
    let guarded = parse_src("f.fz", "def foo(x) when x > 0, do: x + 1\n");
    assert!(
        !base.semantically_eq(&renamed, Horizon::Surface),
        "the function name is surface"
    );
    assert!(!base.semantically_eq(&widened, Horizon::Surface), "arity is surface");
    assert!(!base.semantically_eq(&guarded, Horizon::Surface), "guards are surface");
}

// A multi-clause module re-parsed verbatim is equal at both horizons — the
// walk handles guards, multiple clauses, and patterns without false negatives.
#[test]
fn semantically_eq_is_stable_across_reparse_of_multi_clause_source() {
    let src = "def foo(x) when x > 0, do: x + 1\ndef foo(_), do: 0\n";
    let a = parse_src("a.fz", src);
    let b = parse_src("b.fz", src);
    assert!(a.semantically_eq(&b, Horizon::Full));
    assert!(a.semantically_eq(&b, Horizon::Surface));
}
