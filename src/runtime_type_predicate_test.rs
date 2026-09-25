//! Which arities the other-structs axis takes, asked of the predicate alone.
//!
//! The axis is the one place a door used to derive its own answer instead of
//! reading the predicate's, and no source program can reach the difference: the
//! projection only ever turns the axis on together with a tuple axis that
//! already admits every arity. So the discriminating case is built by hand
//! here, at the layer every door reads.
//!
//! The rest of what a predicate answers is asked in the module's own `tests`,
//! whose helpers these reuse.

use super::tests::{atom, ints, tuple_of};
use super::*;

/// A local coordinate in a test-only regular predicate component.
///
/// Production predicates are trees today.  These coordinates let this test
/// state the finite graph that `.177.12` will later project without giving the
/// production representation a second graph form first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Node(usize);

/// The three recursive predicate edges the existing tree relations descend.
///
/// At depth zero only `atoms` remain.  Replacing an edge with its child at
/// each later depth is therefore the ordinary least finite unrolling of the
/// component, not an active-edge success convention.
#[derive(Clone, Default)]
struct RegularBody {
    atoms: FiniteSet<String>,
    tuple: Option<Vec<Node>>,
    list: Option<Node>,
    callable: Option<(ClosureTarget, Node)>,
}

#[derive(Clone)]
struct RegularPredicate {
    bodies: Vec<RegularBody>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RelationAnswers {
    contained_in: bool,
    overlaps: bool,
    overlaps_on_an_erasing_axis: bool,
}

impl RegularPredicate {
    fn new(bodies: Vec<RegularBody>) -> Self {
        assert!(!bodies.is_empty(), "a regular predicate component needs a node");
        Self { bodies }
    }

    fn body(&self, node: Node) -> &RegularBody {
        self.bodies
            .get(node.0)
            .expect("a regular predicate edge must name a node in its component")
    }

    /// The existing tree predicate at one finite unfolding depth.
    fn unroll(&self, node: Node, depth: usize) -> RuntimeTypePredicate {
        let body = self.body(node);
        let mut predicate = RuntimeTypePredicate::none();
        predicate.atoms = body.atoms.clone();
        if depth == 0 {
            return predicate;
        }
        if let Some(children) = &body.tuple {
            predicate.tuples = TupleShapes::exact(vec![
                children.iter().map(|child| self.unroll(*child, depth - 1)).collect(),
            ]);
        }
        if let Some(head) = body.list {
            predicate.lists =
                ListShapes::exact(FiniteSet::lit(ListShape::NonEmpty), vec![self.unroll(head, depth - 1)]);
        }
        if let Some((target, capture)) = body.callable {
            predicate.callables = CallableShapes::exact(vec![CallableShape {
                target,
                captures: vec![self.unroll(capture, depth - 1)],
            }]);
        }
        predicate
    }

    /// The three relations future graph predicates need, calculated from their
    /// equations rather than a visited-pair convention.  Containment starts
    /// at top and descends to its greatest fixed point; the two existence
    /// questions start at bottom and ascend to their least fixed points.
    fn relations(&self, left: Node, right: Node) -> RelationAnswers {
        let overlaps = self.fixed_point(false, |known, left, right| self.overlap_step(known, left, right));
        RelationAnswers {
            contained_in: self.fixed_point(true, |known, left, right| self.contains_step(known, left, right))[left.0]
                [right.0],
            overlaps: overlaps[left.0][right.0],
            overlaps_on_an_erasing_axis: self.fixed_point(false, |known, left, right| {
                self.erasing_overlap_step(&overlaps, known, left, right)
            })[left.0][right.0],
        }
    }

    fn fixed_point(&self, initial: bool, step: impl Fn(&[Vec<bool>], Node, Node) -> bool) -> Vec<Vec<bool>> {
        let mut known = vec![vec![initial; self.bodies.len()]; self.bodies.len()];
        loop {
            let next = (0..self.bodies.len())
                .map(|left| {
                    (0..self.bodies.len())
                        .map(|right| step(&known, Node(left), Node(right)))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            if next == known {
                return next;
            }
            known = next;
        }
    }

    fn contains_step(&self, known: &[Vec<bool>], left: Node, right: Node) -> bool {
        let (left, right) = (self.body(left), self.body(right));
        right.atoms.contains_all(&left.atoms)
            && match (&left.tuple, &right.tuple) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(left), Some(right)) => {
                    left.len() == right.len() && left.iter().zip(right).all(|(left, right)| known[left.0][right.0])
                }
            }
            && match (left.list, right.list) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(left), Some(right)) => known[left.0][right.0],
            }
            && match (left.callable, right.callable) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some((left_target, left)), Some((right_target, right))) => {
                    left_target == right_target && known[left.0][right.0]
                }
            }
    }

    fn overlap_step(&self, known: &[Vec<bool>], left: Node, right: Node) -> bool {
        let (left, right) = (self.body(left), self.body(right));
        left.atoms.overlaps(&right.atoms)
            || matches!(
                (&left.tuple, &right.tuple),
                (Some(left), Some(right))
                    if left.len() == right.len()
                        && left.iter().zip(right).all(|(left, right)| known[left.0][right.0])
            )
            || matches!((left.list, right.list), (Some(left), Some(right)) if known[left.0][right.0])
            || matches!(
                (left.callable, right.callable),
                (Some((left_target, left)), Some((right_target, right)))
                    if left_target == right_target && known[left.0][right.0]
            )
    }

    fn erasing_overlap_step(
        &self,
        overlaps: &[Vec<bool>],
        erasing_overlaps: &[Vec<bool>],
        left: Node,
        right: Node,
    ) -> bool {
        let (left, right) = (self.body(left), self.body(right));
        matches!(
            (&left.tuple, &right.tuple),
            (Some(left), Some(right))
                if left.len() == right.len()
                    && left.iter().zip(right).all(|(left, right)| overlaps[left.0][right.0])
                    && left
                        .iter()
                        .zip(right)
                        .any(|(left, right)| erasing_overlaps[left.0][right.0])
        ) || matches!(
            (left.list, right.list),
            (Some(left), Some(right)) if overlaps[left.0][right.0]
        ) || matches!(
            (left.callable, right.callable),
            (Some((left_target, left)), Some((right_target, right)))
                if left_target == right_target
                    && overlaps[left.0][right.0]
                    && erasing_overlaps[left.0][right.0]
        )
    }
}

fn atoms(names: impl IntoIterator<Item = &'static str>) -> FiniteSet<String> {
    FiniteSet::finite(names.into_iter().map(String::from))
}

#[derive(Clone, Copy)]
enum RecursiveEdge {
    Tuple,
    List,
    Callable,
}

fn self_recursive(edge: RecursiveEdge, atoms: FiniteSet<String>) -> RegularPredicate {
    let mut body = RegularBody {
        atoms,
        ..RegularBody::default()
    };
    match edge {
        RecursiveEdge::Tuple => body.tuple = Some(vec![Node(0)]),
        RecursiveEdge::List => body.list = Some(Node(0)),
        RecursiveEdge::Callable => body.callable = Some((ClosureTarget(66), Node(0))),
    }
    RegularPredicate::new(vec![body])
}

fn assert_unroll_tail(
    component: &RegularPredicate,
    left: Node,
    right: Node,
    first_depth: usize,
    expected: RelationAnswers,
) {
    assert_eq!(component.relations(left, right), expected, "the founded graph relation");
    for depth in first_depth..=8 {
        let (left, right) = (component.unroll(left, depth), component.unroll(right, depth));
        assert_eq!(
            RelationAnswers {
                contained_in: left.contained_in(&right),
                overlaps: left.overlaps(&right),
                overlaps_on_an_erasing_axis: left.overlaps_on_an_erasing_axis(&right),
            },
            expected,
            "finite unrolling depth {depth}",
        );
    }
}

/// An unproductive component has no finite runtime witness.  Its recursive
/// spelling is still contained in itself (the greatest containment fixed
/// point), but neither existence question may turn a back-edge into a witness.
#[test]
fn unproductive_recursive_edges_are_contained_but_never_overlap_or_erase() {
    for edge in [RecursiveEdge::Tuple, RecursiveEdge::List, RecursiveEdge::Callable] {
        let component = self_recursive(edge, FiniteSet::none());
        assert_unroll_tail(
            &component,
            Node(0),
            Node(0),
            0,
            RelationAnswers {
                contained_in: true,
                overlaps: false,
                overlaps_on_an_erasing_axis: false,
            },
        );
    }
}

/// A scalar leaf makes the recursive component productive.  It is the witness
/// that makes overlap true; it does not by itself make a tuple or callable
/// edge erasing, because those positions still decide the scalar exactly.
#[test]
fn productive_recursive_edges_have_only_the_erasure_their_edge_can_witness() {
    let expected = RelationAnswers {
        contained_in: true,
        overlaps: true,
        overlaps_on_an_erasing_axis: false,
    };
    for edge in [RecursiveEdge::Tuple, RecursiveEdge::Callable] {
        let component = self_recursive(edge, atoms(["leaf"]));
        assert_unroll_tail(&component, Node(0), Node(0), 0, expected);
    }

    let list = self_recursive(RecursiveEdge::List, atoms(["leaf"]));
    assert_unroll_tail(
        &list,
        Node(0),
        Node(0),
        1,
        RelationAnswers {
            overlaps_on_an_erasing_axis: true,
            ..expected
        },
    );
}

/// Tuple and callable positions inherit erasure; they do not invent it on a
/// back-edge.  A productive list witness beneath each one is what changes the
/// answer, and the finite unrollings become the same answer at depth two.
#[test]
fn tuple_and_callable_edges_inherit_a_productive_erasing_witness() {
    let tuple = RegularPredicate::new(vec![
        RegularBody {
            atoms: atoms(["leaf"]),
            tuple: Some(vec![Node(1)]),
            ..RegularBody::default()
        },
        RegularBody {
            list: Some(Node(0)),
            ..RegularBody::default()
        },
    ]);
    let callable = RegularPredicate::new(vec![
        RegularBody {
            atoms: atoms(["leaf"]),
            callable: Some((ClosureTarget(66), Node(1))),
            ..RegularBody::default()
        },
        RegularBody {
            list: Some(Node(0)),
            ..RegularBody::default()
        },
    ]);
    let expected = RelationAnswers {
        contained_in: true,
        overlaps: true,
        overlaps_on_an_erasing_axis: true,
    };

    assert_unroll_tail(&tuple, Node(0), Node(0), 2, expected);
    assert_unroll_tail(&callable, Node(0), Node(0), 2, expected);
}

/// Containment stays directional through every recursive edge.  The `:other`
/// leaf is an immediate counterexample to the reverse direction; the matching
/// edge proves the forward direction needs the coinductive pair relation.
#[test]
fn recursive_containment_is_coinductive_and_directional_across_every_edge() {
    for edge in [RecursiveEdge::Tuple, RecursiveEdge::List, RecursiveEdge::Callable] {
        let mut narrow = RegularBody {
            atoms: atoms(["leaf"]),
            ..RegularBody::default()
        };
        let mut wide = RegularBody {
            atoms: atoms(["leaf", "other"]),
            ..RegularBody::default()
        };
        match edge {
            RecursiveEdge::Tuple => {
                narrow.tuple = Some(vec![Node(0)]);
                wide.tuple = Some(vec![Node(1)]);
            }
            RecursiveEdge::List => {
                narrow.list = Some(Node(0));
                wide.list = Some(Node(1));
            }
            RecursiveEdge::Callable => {
                narrow.callable = Some((ClosureTarget(66), Node(0)));
                wide.callable = Some((ClosureTarget(66), Node(1)));
            }
        }
        let component = RegularPredicate::new(vec![narrow, wide]);
        let first_depth = matches!(edge, RecursiveEdge::List).then_some(1).unwrap_or(0);
        assert_unroll_tail(
            &component,
            Node(0),
            Node(1),
            first_depth,
            RelationAnswers {
                contained_in: true,
                overlaps: true,
                overlaps_on_an_erasing_axis: matches!(edge, RecursiveEdge::List),
            },
        );
        assert_unroll_tail(
            &component,
            Node(1),
            Node(0),
            first_depth,
            RelationAnswers {
                contained_in: false,
                overlaps: true,
                overlaps_on_an_erasing_axis: matches!(edge, RecursiveEdge::List),
            },
        );
    }
}

/// One exact arity-3 shape whose middle position is a 2-tuple. Arity 2 is a
/// question this test asks INSIDE a value and never of a whole one, so it is
/// not among the arities the tuple axis names.
fn nested_pair_in_a_triple() -> RuntimeTypePredicate {
    let mut predicate = tuple_of(vec![vec![atom("ok"), tuple_of(vec![vec![ints(), ints()]]), ints()]]);
    predicate.allow_other_structs = true;
    predicate
}

/// Naming is a TOP-LEVEL reading, so a whole 2-tuple belongs to the
/// other-structs axis even though the test asks about 2-tuples at depth.
///
/// This is the distinction a door loses by reading its own registered tuple
/// schemas: a schema is registered per arity at every depth
/// (`tuple_arities_at_every_depth`), so the nested 2 would exclude a top-level
/// 2-tuple that the axis admits.
#[test]
fn the_other_structs_axis_admits_an_arity_only_a_nested_position_names() {
    let admitted = nested_pair_in_a_triple().other_struct_arities();
    assert!(
        admitted.contains(&2),
        "arity 2 is named only by a nested position, so the tuple axis does not speak for a whole 2-tuple"
    );
    assert!(
        !admitted.contains(&3),
        "arity 3 is the tuple axis' own, and the two axes cover each unnamed struct exactly once"
    );
}

/// The whole-value reading agrees with the axis: a nested arity is one the
/// other-structs axis admits, so no shape of the tuple axis may refuse it.
#[test]
fn a_whole_tuple_of_a_nested_arity_is_never_refused_on_its_shape() {
    let predicate = nested_pair_in_a_triple();
    assert!(matches!(predicate.tuple_positions(2), TuplePositions::Always));
    assert!(matches!(predicate.tuple_positions(3), TuplePositions::AnyOf(_)));
}
