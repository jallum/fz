use std::rc::Rc;

use fz_runtime::any_value::AnyValueRef;

use super::{ExpansionClaim, is_remote_dot_callee, stamp_expansion_counter};
use crate::compiler2::{QuotedSourceHeap, QuotedSourceMetadata};
use crate::source::SourceMap;

#[test]
fn remote_callee_probe_propagates_an_invalid_atom_payload() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let unknown_atom = AnyValueRef::atom(u32::MAX);
    let encoded = builder
        .ast_node(unknown_atom, &QuotedSourceMetadata::default(), builder.empty_list())
        .expect("builder copies the atom into its owned heap");
    let root = builder.root(encoded).expect("quoted source root");
    let node = root
        .cursor()
        .ast_node(&SourceMap::new())
        .expect("structural read")
        .expect("AST node");

    let error = is_remote_dot_callee(&node).expect_err("remote callee probe must propagate invalid atom");
    assert!(error.to_string().contains("unknown atom id"), "{error}");
}

#[test]
fn an_expansion_claims_exactly_its_modules_unclaimed_variables() {
    use crate::ast::{AtomName, Var, VarContext, VarCounter};
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let var = |name: &str, context: Option<&str>, counter: Option<VarCounter>| {
        let var = Var {
            name: name.to_string(),
            context: VarContext {
                context: context.map(AtomName::from),
                counter,
            },
        };
        builder.variable(&var, &QuotedSourceMetadata::default()).unwrap()
    };
    let earlier = VarCounter::Module {
        module: AtomName::from("Elixir.Other"),
        n: 4,
    };
    let tree = builder
        .list(&[
            var("x", Some("Elixir.Gen"), None),
            var("x", Some("Elixir.Gen"), Some(earlier.clone())),
            var("x", Some("Elixir.Other"), None),
            var("x", None, None),
            var("_", Some("Elixir.Gen"), None),
        ])
        .unwrap();
    let root = builder.root(tree).unwrap();
    let ours = VarCounter::Module {
        module: AtomName::from("Elixir.Main"),
        n: 2,
    };
    let claim = ExpansionClaim {
        receiver: AtomName::from("Elixir.Gen"),
        counter: ours.clone(),
    };
    let sources = SourceMap::new();
    let stamped = root.subroot(stamp_expansion_counter(&root, &root.cursor(), &claim, &sources).unwrap());
    let counters = stamped
        .cursor()
        .list_items()
        .unwrap()
        .iter()
        .map(|item| item.ast_node(&sources).unwrap().unwrap().meta.var_counter().unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        counters,
        [Some(ours), Some(earlier), None, None, None],
        "only Gen's counterless `x` is claimed; a kept counter, another context, the user's x and `_` are left alone"
    );
}

/// What a macro that answers with the context it was expanded in becomes at
/// each position that binds a pattern, guards, or tests. A match yields
/// `:match`, a guard `true`, and an expression `nil`; the program returns 1
/// only when the macro saw the context its position has.
const EACH_POSITION_SEES_ITS_CONTEXT: &[(&str, &str)] = &[
    (
        "a function head",
        "def head(ctx()), do: 1\ndef main(), do: head(:match)",
    ),
    (
        "a guard",
        "def guarded(_x) when ctx(), do: 1\ndef main(), do: guarded(0)",
    ),
    ("the left of =", "def main() do\n ctx() = :match\n 1\nend"),
    (
        "a generator",
        "def main(), do: length(for ctx() <- [:match, :other], do: 1)",
    ),
    ("a with clause", "def main(), do: with(ctx() <- :match, do: 1)"),
    ("a case clause", "def main(), do: case(:match, do: (ctx() -> 1))"),
    ("a fn clause", "def main(), do: (fn ctx() -> 1 end).(:match)"),
    (
        "a receive clause",
        "def main() do\n send(self(), :match)\n receive do\n ctx() -> 1\n end\nend",
    ),
    (
        "a try else clause",
        "def main(), do: try(do: :match, else: (ctx() -> 1))",
    ),
    (
        "a catch clause",
        "def main(), do: try(do: throw(:match), catch: (ctx() -> 1))",
    ),
    (
        "a with else clause",
        "def main(), do: with(:a <- :match, do: 0, else: (ctx() -> 1))",
    ),
    (
        "a for reduce clause",
        "def main(), do: for(_ <- [1], reduce: :match, do: (ctx() -> 1))",
    ),
    (
        "an ordinary expression",
        "def main(), do: if(ctx() == nil, do: 1, else: 0)",
    ),
    ("a cond test", "def main(), do: cond(do: (ctx() == nil -> 1))"),
    (
        "a receive after timeout",
        "def main(), do: receive(do: (:never -> 0), after: ((if ctx() == nil, do: 0, else: 1000) -> 1))",
    ),
];

#[test]
fn a_macro_sees_the_context_of_the_position_it_is_expanded_in() {
    use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
    use crate::telemetry::ConfiguredTelemetry;

    let context_macro =
        "defmacro ctx() do\n case __CALLER__.context do\n :match -> :match\n :guard -> true\n nil -> nil\n end\nend\n";
    for (position, body) in EACH_POSITION_SEES_ITS_CONTEXT {
        let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
        compiler.submit_code(CodeSubmission {
            name: Some("context_positions.fz".into()),
            text: format!("{context_macro}{body}\n"),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".into(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        assert_eq!(compiler.run_root_interp(root), Ok(1), "in {position}");
    }
}
