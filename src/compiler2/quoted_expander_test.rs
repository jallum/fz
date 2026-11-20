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
