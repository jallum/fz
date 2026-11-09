use super::*;
use crate::ast::{BinOp, Callee, FnClause, Spanned, TypeExprBody, UnOp};
use crate::compiler2::{Ty, Types};
use crate::dispatch_matrix::{DispatchNode, SubjectSource};

fn sp<T>(node: T) -> Spanned<T> {
    Spanned::dummy(node)
}

fn var(name: &str) -> Expr {
    Expr::Var(Var::user(name))
}

fn call(name: &str, args: Vec<Expr>) -> Expr {
    Expr::Call(Box::new(sp(var(name))), args.into_iter().map(sp).collect())
}

fn and(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp(BinOp::And, Box::new(sp(lhs)), Box::new(sp(rhs)))
}

fn or(lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp(BinOp::Or, Box::new(sp(lhs)), Box::new(sp(rhs)))
}

fn not(expr: Expr) -> Expr {
    Expr::UnOp(UnOp::Not, Box::new(sp(expr)))
}

fn plus_one(name: &str) -> Expr {
    Expr::BinOp(BinOp::Add, Box::new(sp(var(name))), Box::new(sp(Expr::Int(1))))
}

struct Surface(Vec<FnClause>);

impl CallableSurface for Surface {
    fn name(&self) -> &str {
        "helper"
    }
    fn clauses(&self) -> &[FnClause] {
        &self.0
    }
    fn extern_abi(&self) -> Option<&str> {
        None
    }
    fn extern_param_tokens(&self) -> &[TypeExprBody] {
        &[]
    }
    fn extern_ret_tokens(&self) -> &TypeExprBody {
        unreachable!("a helper in these tests is never an extern")
    }
    fn extern_constraints(&self) -> &[(String, TypeExprBody)] {
        &[]
    }
}

fn params(arity: usize) -> Vec<Spanned<Pattern>> {
    (0..arity).map(|_| sp(Pattern::Wildcard)).collect()
}

fn clause(arity: usize, guard: Option<Expr>, body: Expr) -> FnClause {
    FnClause {
        params: params(arity),
        param_annotations: vec![None; arity],
        guard: guard.map(sp),
        body: sp(body),
        span: crate::source::Span::DUMMY,
    }
}

fn row(arity: usize, annotated: &[(u32, Ty)], body_id: PatternBodyId) -> PatternRow<Ty> {
    PatternRow {
        patterns: params(arity),
        preconditions: annotated
            .iter()
            .map(|(index, ty)| (PatternSubjectRef::Input(*index), *ty))
            .collect(),
        guard: None,
        body_id,
    }
}

fn no_calls() -> impl FnMut(&Callee, usize) -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
    |_callee, _arity| Ok(None)
}

/// `def helper(_ :: T0, ..), do: true; def helper(_, ..), do: false`
fn predicate_helper(arity: usize, annotated: &[(u32, Ty)]) -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![
        clause(arity, None, Expr::Bool(true)),
        clause(arity, None, Expr::Bool(false)),
    ]);
    let rows = vec![row(arity, annotated, 0), row(arity, &[], 1)];
    guard_dispatch_from_rows(&surface, rows, &mut no_calls()).expect("a predicate-shaped helper reifies")
}

/// `def opaque(_), do: true`: a helper that answers no type question.
fn opaque_helper() -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![clause(1, None, Expr::Bool(true))]);
    guard_dispatch_from_rows(&surface, vec![row(1, &[], 0)], &mut no_calls()).expect("opaque helper reifies")
}

struct Helpers {
    is_int: Arc<PatternGuardDispatch<Ty>>,
    is_float: Arc<PatternGuardDispatch<Ty>>,
    opaque: Arc<PatternGuardDispatch<Ty>>,
}

impl Helpers {
    fn new() -> Self {
        let mut types = Types::new();
        let int = types.int();
        let float = types.float();
        Self {
            is_int: Arc::new(predicate_helper(1, &[(0, int)])),
            is_float: Arc::new(predicate_helper(1, &[(0, float)])),
            opaque: Arc::new(opaque_helper()),
        }
    }

    fn resolver(&self) -> impl FnMut(&Callee, usize) -> Result<Option<GuardCallee<Ty>>, SourcePatternError> + '_ {
        |callee, _arity| {
            let Callee::Name(name) = callee else { return Ok(None) };
            Ok(match name.name.as_str() {
                "is_int" => Some(GuardCallee::Helper(Arc::clone(&self.is_int))),
                "is_float" => Some(GuardCallee::Helper(Arc::clone(&self.is_float))),
                "opaque" => Some(GuardCallee::Helper(Arc::clone(&self.opaque))),
                _ => None,
            })
        }
    }

    fn plan(&self, patterns: Vec<Pattern>, preconditions: Vec<(PatternSubjectRef, Ty)>, guard: Expr) -> Plan {
        let row = PatternRow {
            patterns: patterns.into_iter().map(sp).collect(),
            preconditions,
            guard: Some(sp(guard)),
            body_id: 0,
        };
        self.plan_of_row(row)
    }

    fn plan_of_row(&self, row: PatternRow<Ty>) -> Plan {
        let input_count = row.patterns.len();
        let rows = SourcePatternRows::lexical(input_count, vec![row]);
        pattern_dispatch_from_source_with_resolver(rows, &mut self.resolver()).expect("the row compiles")
    }
}

type Plan = PatternDispatchPlan<Ty>;

fn x() -> Pattern {
    Pattern::Var(Var::user("x"))
}

/// The questions of a one-row plan, in the order they are asked.
fn tests(plan: &Plan) -> Vec<&RegionPredicate<Ty>> {
    let mut asked = Vec::new();
    let mut node = plan.graph.root;
    while let Some(DispatchNode::Test {
        predicate, on_match, ..
    }) = plan.graph.node(node)
    {
        asked.push(predicate);
        node = on_match.target;
    }
    asked
}

fn type_questions(plan: &Plan) -> Vec<(&SubjectSource, &Ty)> {
    tests(plan)
        .into_iter()
        .filter_map(|predicate| match &predicate.region {
            Region::Type(ty) => Some((plan.subject(predicate.subject), ty)),
            _ => None,
        })
        .collect()
}

fn guard_questions(plan: &Plan) -> usize {
    tests(plan)
        .into_iter()
        .filter(|predicate| matches!(predicate.region, Region::Guard(_)))
        .count()
}

#[test]
fn a_guard_that_is_a_type_predicate_builds_the_row_a_typed_parameter_builds() {
    let helpers = Helpers::new();
    let int = helpers.is_int.type_predicate.as_ref().unwrap()[0].1;
    let guarded = helpers.plan(vec![x()], Vec::new(), call("is_int", vec![var("x")]));
    let typed = helpers.plan_of_row(PatternRow {
        patterns: vec![sp(x())],
        preconditions: vec![(PatternSubjectRef::Input(0), int)],
        guard: None,
        body_id: 0,
    });

    assert_eq!(guarded.graph, typed.graph, "the guard is read as a type question");
    assert!(guarded.guards.is_empty(), "nothing is left of the guard");
}

#[test]
fn a_helper_with_two_guardless_clauses_true_then_false_over_annotated_params_is_a_type_predicate() {
    let mut types = Types::new();
    let int = types.int();
    let float = types.float();
    let pair = predicate_helper(2, &[(0, int), (1, float)]);
    assert_eq!(pair.type_predicate, Some(vec![(0, int), (1, float)]));
}

#[test]
fn a_helper_that_does_not_have_the_predicate_shape_is_not_one() {
    let mut types = Types::new();
    let int = types.int();
    let reify = |clauses: Vec<FnClause>, rows: Vec<PatternRow<Ty>>| {
        guard_dispatch_from_rows(&Surface(clauses), rows, &mut no_calls())
            .expect("the helper reifies")
            .type_predicate
    };

    let both_true = reify(
        vec![clause(1, None, Expr::Bool(true)), clause(1, None, Expr::Bool(true))],
        vec![row(1, &[(0, int)], 0), row(1, &[], 1)],
    );
    let nothing_annotated = reify(
        vec![clause(1, None, Expr::Bool(true)), clause(1, None, Expr::Bool(false))],
        vec![row(1, &[], 0), row(1, &[], 1)],
    );
    let second_annotated = reify(
        vec![clause(1, None, Expr::Bool(true)), clause(1, None, Expr::Bool(false))],
        vec![row(1, &[(0, int)], 0), row(1, &[(0, int)], 1)],
    );
    let guarded = reify(
        vec![
            clause(1, Some(Expr::Bool(true)), Expr::Bool(true)),
            clause(1, None, Expr::Bool(false)),
        ],
        vec![row(1, &[(0, int)], 0), row(1, &[], 1)],
    );
    let one_clause = reify(vec![clause(1, None, Expr::Bool(true))], vec![row(1, &[(0, int)], 0)]);
    let mut literal_head = clause(1, None, Expr::Bool(true));
    literal_head.params = vec![sp(Pattern::Nil)];
    let literal_pattern = reify(
        vec![literal_head, clause(1, None, Expr::Bool(false))],
        vec![
            PatternRow {
                patterns: vec![sp(Pattern::Nil)],
                preconditions: vec![(PatternSubjectRef::Input(0), int)],
                guard: None,
                body_id: 0,
            },
            row(1, &[], 1),
        ],
    );

    for (shape, found) in [
        ("two true clauses", both_true),
        ("no annotation", nothing_annotated),
        ("second clause annotated", second_annotated),
        ("guarded first clause", guarded),
        ("one clause", one_clause),
        ("a literal pattern in the head", literal_pattern),
    ] {
        assert_eq!(found, None, "{shape} is not a type predicate");
    }
}

#[test]
fn a_conjunct_that_is_not_a_type_predicate_stays_the_guard_after_the_type_question() {
    let helpers = Helpers::new();
    let plan = helpers.plan(
        vec![x()],
        Vec::new(),
        and(call("is_int", vec![var("x")]), call("opaque", vec![var("x")])),
    );

    assert_eq!(type_questions(&plan).len(), 1, "is_int(x) is a type question");
    assert_eq!(plan.guards.len(), 1, "only the other conjunct is left as a guard");
    assert!(
        matches!(plan.guards[0], PatternGuardExpr::Dispatch { .. }),
        "the remaining guard is exactly opaque(x): {:?}",
        plan.guards[0]
    );
}

#[test]
fn a_type_conjunct_written_after_another_conjunct_folds_as_well() {
    let helpers = Helpers::new();
    let plan = helpers.plan(
        vec![x()],
        Vec::new(),
        and(call("opaque", vec![var("x")]), call("is_int", vec![var("x")])),
    );
    let question_kinds = tests(&plan)
        .into_iter()
        .map(|predicate| matches!(predicate.region, Region::Type(_)))
        .collect::<Vec<_>>();

    assert_eq!(
        question_kinds,
        vec![true, false],
        "the type question is asked before the guard it was written after"
    );
    assert_eq!(plan.guards.len(), 1);
}

#[test]
fn several_type_conjuncts_fold_in_written_order_and_the_guard_disappears() {
    let helpers = Helpers::new();
    let plan = helpers.plan(
        vec![x(), Pattern::Var(Var::user("y"))],
        Vec::new(),
        and(call("is_int", vec![var("x")]), call("is_float", vec![var("y")])),
    );

    assert_eq!(type_questions(&plan).len(), 2);
    assert_eq!(guard_questions(&plan), 0);
    assert!(plan.guards.is_empty());
}

#[test]
fn a_guard_that_is_not_a_top_level_and_chain_of_type_predicates_is_unchanged() {
    let helpers = Helpers::new();
    let cases = [
        (
            "or",
            or(call("is_int", vec![var("x")]), call("is_float", vec![var("x")])),
        ),
        ("not", not(call("is_int", vec![var("x")]))),
        ("an expression argument", call("is_int", vec![plus_one("x")])),
        ("a name no pattern in the row binds", call("is_int", vec![var("outer")])),
    ];
    for (shape, guard) in cases {
        let plan = helpers.plan(vec![x()], Vec::new(), guard);
        assert_eq!(type_questions(&plan).len(), 0, "{shape}: no type question is lifted");
        assert_eq!(guard_questions(&plan), 1, "{shape}: the guard is kept whole");
    }
}

#[test]
fn a_type_question_on_a_value_inside_a_tuple_is_asked_of_that_field() {
    let helpers = Helpers::new();
    let pair = Pattern::Tuple(vec![sp(x()), sp(Pattern::Wildcard)]);
    let plan = helpers.plan(vec![pair], Vec::new(), call("is_int", vec![var("x")]));

    let questions = type_questions(&plan);
    assert_eq!(questions.len(), 1);
    let SubjectSource::Projection(projection) = questions[0].0 else {
        panic!("the question is asked of a projected field, not of the whole argument");
    };
    assert_eq!(projection.kind, ProjectionKind::TupleField(0));
    assert!(plan.guards.is_empty());
}

#[test]
fn a_type_question_the_parameter_already_asks_is_asked_once() {
    let helpers = Helpers::new();
    let int = helpers.is_int.type_predicate.as_ref().unwrap()[0].1;
    let plan = helpers.plan(
        vec![x()],
        vec![(PatternSubjectRef::Input(0), int)],
        call("is_int", vec![var("x")]),
    );

    assert_eq!(type_questions(&plan).len(), 1);
    assert!(plan.guards.is_empty());
}

#[test]
fn a_plan_carries_the_exception_its_rows_raise_through_every_rebuild() {
    let rows = vec![PatternRow {
        patterns: vec![sp(Pattern::Int(1))],
        preconditions: Vec::new(),
        guard: None,
        body_id: 0,
    }];
    let plan = pattern_dispatch_from_source::<Ty>(
        SourcePatternRows::lexical(1, rows.clone()).raising(LastResort::case_clause()),
    )
    .expect("the row compiles");
    assert_eq!(plan.last_resort, Some(LastResort::case_clause()));

    let trimmed = plan
        .trimmed(&|_| crate::dispatch_matrix::LiveEdges::Match)
        .expect("a narrowed test trims the plan");
    assert_eq!(
        trimmed.last_resort, plan.last_resort,
        "trimming keeps what the construct raises"
    );
    let mapped = plan.map_type_handle(&mut |ty| *ty);
    assert_eq!(
        mapped.last_resort, plan.last_resort,
        "a plan read through another type handle raises the same exception"
    );

    let unraised = pattern_dispatch_from_source::<Ty>(SourcePatternRows::lexical(1, rows)).expect("the row compiles");
    assert_eq!(
        unraised.last_resort, None,
        "rows that do not say what they raise leave the miss to their construct"
    );
}

fn aborting_extern() -> Arc<GuardExtern> {
    use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};
    Arc::new(
        GuardExtern::new(
            ExternAbi::C,
            "abort",
            &[ExternTy::Any],
            ExternReturn::Scalar(ExternTy::Never),
            false,
        )
        .expect("an aborting extern is a guard extern"),
    )
}

/// `def fails(_), do: abort(1)` over an aborting extern.
fn failing_helper() -> Arc<PatternGuardDispatch<Ty>> {
    let surface = Surface(vec![clause(1, None, call("abort", vec![Expr::Int(1)]))]);
    let mut resolver = |callee: &Callee, _arity: usize| -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok((name.name == "abort").then(|| GuardCallee::Extern(aborting_extern())))
    };
    Arc::new(guard_dispatch_from_rows(&surface, vec![row(1, &[], 0)], &mut resolver).expect("a failing helper reifies"))
}

fn guard_of(expr: &Expr, helper: Arc<PatternGuardDispatch<Ty>>) -> Result<PatternGuardExpr<Ty>, SourcePatternError> {
    let mut resolver = |callee: &Callee, _arity: usize| -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok(match name.name.as_str() {
            "abort" => Some(GuardCallee::Extern(aborting_extern())),
            "fails" => Some(GuardCallee::Helper(Arc::clone(&helper))),
            _ => None,
        })
    };
    guard_expr_from_ast(
        expr,
        &Default::default(),
        &Default::default(),
        &mut Default::default(),
        &mut resolver,
    )
}

#[test]
fn a_call_to_an_aborting_extern_is_a_failing_node_whose_arguments_are_never_built() {
    // `nothing(1)` resolves to no callee, so building it is an error: the
    // call below can only succeed if its arguments are not visited.
    let call_with_unbuildable_argument = call("abort", vec![call("nothing", vec![Expr::Int(1)])]);
    let built = guard_of(&call_with_unbuildable_argument, failing_helper());
    assert!(matches!(built, Ok(PatternGuardExpr::Fails)), "{built:?}");
}

#[test]
fn a_call_to_a_helper_whose_callee_always_fails_is_a_failing_node_whose_arguments_are_never_built() {
    let call_with_unbuildable_argument = call("fails", vec![call("nothing", vec![Expr::Int(1)])]);
    let built = guard_of(&call_with_unbuildable_argument, failing_helper());
    assert!(matches!(built, Ok(PatternGuardExpr::Fails)), "{built:?}");
}
