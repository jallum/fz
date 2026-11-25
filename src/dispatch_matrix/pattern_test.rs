use super::*;
use crate::ast::{BinOp, Callee, FnClause, Spanned, TypeExprBody, UnOp};
use crate::compiler2::{Ty, Types};
use crate::dispatch_matrix::demand::DispatchDemand;
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

/// `def always(_, ..), do: true`: a helper that ignores its arguments.
fn always_helper(arity: usize) -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![clause(arity, None, Expr::Bool(true))]);
    guard_dispatch_from_rows(&surface, vec![row(arity, &[], 0)], &mut no_calls()).expect("always helper reifies")
}

/// `def ambiguous(_ :: T, ..), do: true; def ambiguous(_, ..), do: true`: two
/// clauses that both answer true, which no one set of facts states.
fn ambiguous_helper(arity: usize, ty: Ty) -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![
        clause(arity, None, Expr::Bool(true)),
        clause(arity, None, Expr::Bool(true)),
    ]);
    let rows = vec![row(arity, &[(0, ty)], 0), row(arity, &[], 1)];
    guard_dispatch_from_rows(&surface, rows, &mut no_calls()).expect("ambiguous helper reifies")
}

fn n() -> Pattern {
    Pattern::Var(Var::user("n"))
}

fn row_over_n(guard: Expr, body_id: PatternBodyId) -> PatternRow<Ty> {
    PatternRow {
        patterns: vec![sp(n())],
        preconditions: Vec::new(),
        guard: Some(sp(guard)),
        body_id,
    }
}

fn compare(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    Expr::BinOp(op, Box::new(sp(lhs)), Box::new(sp(rhs)))
}

/// `def positive(n) when n > 0, do: true; def positive(_), do: false`
fn positive_helper() -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![
        clause(1, Some(Expr::Bool(true)), Expr::Bool(true)),
        clause(1, None, Expr::Bool(false)),
    ]);
    let rows = vec![
        row_over_n(compare(BinOp::Gt, var("n"), Expr::Int(0)), 0),
        row(1, &[], 1),
    ];
    guard_dispatch_from_rows(&surface, rows, &mut no_calls()).expect("positive helper reifies")
}

/// `def number(n), do: is_int(n) or is_float(n)`
fn number_helper(int: Ty, float: Ty) -> PatternGuardDispatch<Ty> {
    let is_int = Arc::new(predicate_helper(1, &[(0, int)]));
    let is_float = Arc::new(predicate_helper(1, &[(0, float)]));
    let body = or(call("is_int", vec![var("n")]), call("is_float", vec![var("n")]));
    let surface = Surface(vec![clause(1, None, body)]);
    let row = PatternRow {
        patterns: vec![sp(n())],
        preconditions: Vec::new(),
        guard: None,
        body_id: 0,
    };
    let mut resolver = |callee: &Callee, _arity: usize| -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok(match name.name.as_str() {
            "is_int" => Some(GuardCallee::Helper(Arc::clone(&is_int))),
            "is_float" => Some(GuardCallee::Helper(Arc::clone(&is_float))),
            _ => None,
        })
    };
    guard_dispatch_from_rows(&surface, vec![row], &mut resolver).expect("number helper reifies")
}

/// `def checked(n) when n < 0, do: abort(1); def checked(_), do: true`
fn checked_helper() -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![
        clause(1, Some(Expr::Bool(true)), call("abort", vec![Expr::Int(1)])),
        clause(1, None, Expr::Bool(true)),
    ]);
    let rows = vec![
        row_over_n(compare(BinOp::Lt, var("n"), Expr::Int(0)), 0),
        row(1, &[], 1),
    ];
    let mut resolver = |callee: &Callee, _arity: usize| -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok((name.name == "abort").then(|| GuardCallee::Extern(aborting_extern())))
    };
    guard_dispatch_from_rows(&surface, rows, &mut resolver).expect("checked helper reifies")
}

/// `def only_int(_ :: int), do: true`: no clause for any other argument, so a
/// call with another argument raises.
fn partial_helper(ty: Ty) -> PatternGuardDispatch<Ty> {
    let surface = Surface(vec![clause(1, None, Expr::Bool(true))]);
    guard_dispatch_from_rows(&surface, vec![row(1, &[(0, ty)], 0)], &mut no_calls()).expect("partial helper reifies")
}

struct Helpers {
    int: Ty,
    is_int: Arc<PatternGuardDispatch<Ty>>,
    is_float: Arc<PatternGuardDispatch<Ty>>,
    only_int: Arc<PatternGuardDispatch<Ty>>,
    number: Arc<PatternGuardDispatch<Ty>>,
    pair: Arc<PatternGuardDispatch<Ty>>,
    always: Arc<PatternGuardDispatch<Ty>>,
    ambiguous: Arc<PatternGuardDispatch<Ty>>,
    positive: Arc<PatternGuardDispatch<Ty>>,
    checked: Arc<PatternGuardDispatch<Ty>>,
    /// What the operator `+` resolves to in a guard: a call like any other.
    plus: Arc<PatternGuardDispatch<Ty>>,
}

impl Helpers {
    fn new() -> Self {
        let mut types = Types::new();
        let int = types.int();
        let float = types.float();
        Self {
            int,
            is_int: Arc::new(predicate_helper(1, &[(0, int)])),
            is_float: Arc::new(predicate_helper(1, &[(0, float)])),
            only_int: Arc::new(partial_helper(int)),
            number: Arc::new(number_helper(int, float)),
            pair: Arc::new(predicate_helper(2, &[(0, int), (1, float)])),
            always: Arc::new(always_helper(1)),
            ambiguous: Arc::new(ambiguous_helper(1, int)),
            positive: Arc::new(positive_helper()),
            checked: Arc::new(checked_helper()),
            plus: Arc::new(ambiguous_helper(2, int)),
        }
    }

    fn resolver(&self) -> impl FnMut(&Callee, usize) -> Result<Option<GuardCallee<Ty>>, SourcePatternError> + '_ {
        |callee, _arity| {
            let Callee::Name(name) = callee else { return Ok(None) };
            let helper = |helper: &Arc<PatternGuardDispatch<Ty>>| Some(GuardCallee::Helper(Arc::clone(helper)));
            Ok(match name.name.as_str() {
                "is_int" => helper(&self.is_int),
                "is_float" => helper(&self.is_float),
                "only_int" => helper(&self.only_int),
                "number" => helper(&self.number),
                "pair" => helper(&self.pair),
                "always" => helper(&self.always),
                "ambiguous" => helper(&self.ambiguous),
                "positive" => helper(&self.positive),
                "checked" => helper(&self.checked),
                "+" => helper(&self.plus),
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
        pattern_dispatch_from_source_with_resolver(&rows, &mut self.resolver()).expect("the row compiles")
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

fn guard_over_x(helpers: &Helpers, guard: Expr) -> Plan {
    helpers.plan(vec![x()], Vec::new(), guard)
}

#[test]
fn a_guard_that_is_a_type_predicate_builds_the_row_a_typed_parameter_builds() {
    let helpers = Helpers::new();
    let guarded = guard_over_x(&helpers, call("is_int", vec![var("x")]));
    let typed = helpers.plan_of_row(PatternRow {
        patterns: vec![sp(x())],
        preconditions: vec![(PatternSubjectRef::Input(0), helpers.int)],
        guard: None,
        body_id: 0,
    });

    assert_eq!(guarded.graph, typed.graph, "the call unfolds into the type question");
    assert!(guarded.guards.is_empty(), "nothing is left of the guard");
}

#[test]
fn a_predicate_over_two_arguments_unfolds_into_a_type_question_for_each() {
    let helpers = Helpers::new();
    let plan = helpers.plan(
        vec![x(), Pattern::Var(Var::user("y"))],
        Vec::new(),
        call("pair", vec![var("x"), var("y")]),
    );

    assert_eq!(type_questions(&plan).len(), 2);
    assert!(plan.guards.is_empty());
}

#[test]
fn a_helper_that_answers_true_in_two_clauses_stays_the_guard_it_is() {
    let helpers = Helpers::new();
    let plan = guard_over_x(&helpers, call("ambiguous", vec![var("x")]));

    assert_eq!(
        type_questions(&plan).len(),
        0,
        "no one clause states what the call asks"
    );
    assert!(
        matches!(plan.guards.as_slice(), [PatternGuardExpr::Dispatch { .. }]),
        "the guard is exactly ambiguous(x): {:?}",
        plan.guards
    );
}

#[test]
fn a_helper_that_ignores_its_argument_asks_nothing_of_it() {
    let helpers = Helpers::new();
    let plan = guard_over_x(&helpers, call("always", vec![var("x")]));

    assert!(type_questions(&plan).is_empty());
    assert!(plan.guards.is_empty(), "the argument is read by no guard");
    assert_eq!(plan.graph.input_demand, vec![DispatchDemand::Ignore]);
}

#[test]
fn a_conjunct_that_cannot_unfold_stays_the_guard_after_the_type_question() {
    let helpers = Helpers::new();
    let plan = guard_over_x(
        &helpers,
        and(call("is_int", vec![var("x")]), call("ambiguous", vec![var("x")])),
    );

    assert_eq!(type_questions(&plan).len(), 1, "is_int(x) is a type question");
    assert!(
        matches!(plan.guards.as_slice(), [PatternGuardExpr::Dispatch { .. }]),
        "only the other conjunct is left, exactly ambiguous(x): {:?}",
        plan.guards
    );
}

#[test]
fn a_type_conjunct_written_after_another_conjunct_unfolds_as_well() {
    let helpers = Helpers::new();
    let plan = guard_over_x(
        &helpers,
        and(call("ambiguous", vec![var("x")]), call("is_int", vec![var("x")])),
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
fn several_type_conjuncts_unfold_in_written_order_and_the_guard_disappears() {
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
fn a_guard_that_is_not_an_and_or_chain_of_calls_is_unchanged() {
    let helpers = Helpers::new();
    let cases = [
        (
            "not, which a resolver without complements cannot read",
            not(call("is_int", vec![var("x")])),
        ),
        ("an expression argument", call("is_int", vec![plus_one("x")])),
        ("a name no pattern in the row binds", call("is_int", vec![var("outer")])),
    ];
    for (shape, guard) in cases {
        let plan = guard_over_x(&helpers, guard);
        assert_eq!(type_questions(&plan).len(), 0, "{shape}: no type question is lifted");
        assert_eq!(guard_questions(&plan), 1, "{shape}: the guard is kept whole");
    }
}

/// The arms of a plan's matrix: how many ways its clauses can match, and how
/// many clauses there are.
fn arms_and_outcomes(plan: &Plan) -> (usize, usize) {
    (plan.source_matrix.arms.len(), plan.source_matrix.outcomes.len())
}

/// The questions each arm asks, in the order the arms are tried.
fn arm_questions(plan: &Plan) -> Vec<Vec<&Region<Ty>>> {
    plan.source_matrix
        .arms
        .iter()
        .map(|arm| {
            arm.questions
                .iter()
                .map(|question| &question.predicate.region)
                .collect()
        })
        .collect()
}

fn is_type_region(region: &&Region<Ty>) -> bool {
    matches!(region, Region::Type(_))
}

#[test]
fn an_or_of_two_type_tests_is_one_row_whose_guard_is_the_or() {
    let helpers = Helpers::new();
    let plan = guard_over_x(
        &helpers,
        or(call("is_int", vec![var("x")]), call("is_float", vec![var("x")])),
    );

    assert_eq!(arms_and_outcomes(&plan), (1, 1), "one way to match the clause");
    assert_eq!(plan.guards.len(), 1, "the disjunction is what the row runs");
    assert!(
        arm_questions(&plan)[0].iter().all(|region| !is_type_region(region)),
        "neither side is asked as a type of its own"
    );
    assert_eq!(plan.outcomes.len(), 1);
}

#[test]
fn an_or_of_three_tests_is_one_row_with_one_guard_however_it_nests() {
    let helpers = Helpers::new();
    let (a, b, c) = (
        call("is_int", vec![var("x")]),
        call("is_float", vec![var("x")]),
        call("positive", vec![var("x")]),
    );
    let left = guard_over_x(&helpers, or(or(a.clone(), b.clone()), c.clone()));
    let right = guard_over_x(&helpers, or(a, or(b, c)));

    for (nesting, plan) in [("left", &left), ("right", &right)] {
        assert_eq!(arms_and_outcomes(plan), (1, 1), "{nesting}: one row");
        assert_eq!(plan.guards.len(), 1, "{nesting}: the whole chain is its guard");
    }
    assert_eq!(left.source_matrix.arms, right.source_matrix.arms);
}

#[test]
fn an_or_of_a_type_test_and_a_side_that_runs_is_one_row_with_the_or_as_its_guard() {
    let helpers = Helpers::new();
    let plan = guard_over_x(
        &helpers,
        or(call("is_int", vec![var("x")]), call("positive", vec![var("x")])),
    );

    assert_eq!(arms_and_outcomes(&plan), (1, 1));
    assert_eq!(plan.guards.len(), 1, "the or runs whole, both sides in it");
    assert_eq!(
        type_questions(&plan).len(),
        0,
        "the type test is inside the guard, not a question"
    );
}

#[test]
fn an_or_whose_earlier_side_may_raise_stays_one_guard() {
    let helpers = Helpers::new();
    let cases = [
        (
            "a side that runs",
            or(call("positive", vec![var("x")]), call("is_int", vec![var("x")])),
        ),
        (
            "a helper with no clause for some arguments",
            or(call("only_int", vec![var("x")]), call("is_float", vec![var("x")])),
        ),
    ];
    for (shape, guard) in cases {
        let plan = guard_over_x(&helpers, guard);
        assert_eq!(arms_and_outcomes(&plan), (1, 1), "{shape}: a single row");
        assert_eq!(plan.guards.len(), 1, "{shape}: the guard is kept whole");
    }
}

#[test]
fn a_helper_that_is_an_or_is_one_row_with_its_or_as_the_guard() {
    let helpers = Helpers::new();
    let plan = guard_over_x(&helpers, call("number", vec![var("x")]));

    assert_eq!(arms_and_outcomes(&plan), (1, 1));
    assert_eq!(plan.guards.len(), 1);
    assert_eq!(type_questions(&plan).len(), 0);
}

#[test]
fn an_or_of_helpers_that_are_ors_is_one_row_with_one_guard() {
    let helpers = Helpers::new();
    let plan = guard_over_x(
        &helpers,
        or(call("number", vec![var("x")]), call("is_int", vec![var("x")])),
    );

    assert_eq!(arms_and_outcomes(&plan), (1, 1));
    assert_eq!(plan.guards.len(), 1);
}

#[test]
fn an_and_of_ors_is_one_row_whose_guard_keeps_every_or() {
    let helpers = Helpers::new();
    let plan = helpers.plan(
        vec![x(), Pattern::Var(Var::user("y"))],
        Vec::new(),
        and(
            or(call("is_int", vec![var("x")]), call("is_float", vec![var("x")])),
            or(call("is_int", vec![var("y")]), call("is_float", vec![var("y")])),
        ),
    );

    assert_eq!(arms_and_outcomes(&plan), (1, 1));
    assert_eq!(plan.guards.len(), 1, "the ors stay together in the one guard");
    assert_eq!(type_questions(&plan).len(), 0);
}

#[test]
fn a_chain_of_ors_joined_by_and_is_one_row_whose_guard_keeps_every_or() {
    let helpers = Helpers::new();
    let names = ["a", "b", "c", "d", "e"];
    let either = |name: &str| or(call("is_int", vec![var(name)]), call("is_float", vec![var(name)]));
    let guard = names[1..]
        .iter()
        .fold(either(names[0]), |chain, name| and(chain, either(name)));
    let plan = helpers.plan(
        names.iter().map(|name| Pattern::Var(Var::user(*name))).collect(),
        Vec::new(),
        guard,
    );

    let (arms, outcomes) = arms_and_outcomes(&plan);
    assert_eq!(outcomes, 1);
    assert_eq!(arms, 1, "the ors never multiply out");
    assert_eq!(plan.guards.len(), 1);
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
    let plan = helpers.plan(
        vec![x()],
        vec![(PatternSubjectRef::Input(0), helpers.int)],
        call("is_int", vec![var("x")]),
    );

    assert_eq!(type_questions(&plan).len(), 1);
    assert!(plan.guards.is_empty());
}

#[test]
fn a_conjunct_the_helper_states_over_its_argument_is_a_guard_over_the_callers_subject() {
    let helpers = Helpers::new();
    let plan = guard_over_x(&helpers, call("positive", vec![var("x")]));

    assert!(
        matches!(
            plan.guards.as_slice(),
            [PatternGuardExpr::Binary {
                op: PatternGuardBinOp::Gt,
                ..
            }]
        ),
        "the call is replaced by what the helper's clause says, not kept as a call: {:?}",
        plan.guards
    );
}

#[test]
fn a_literal_argument_is_substituted_and_a_conjunct_of_constants_is_decided_on_the_spot() {
    let helpers = Helpers::new();
    let holds = guard_over_x(&helpers, call("positive", vec![Expr::Int(3)]));
    let fails = guard_over_x(&helpers, call("positive", vec![Expr::Int(0)]));

    assert!(holds.guards.is_empty(), "3 > 0 asks nothing at run time");
    assert_eq!(
        fails.guards,
        vec![PatternGuardExpr::Const(GroundValue::Bool(false))],
        "0 > 0 can never hold"
    );
}

#[test]
fn a_clause_that_raises_contributes_false_so_the_guard_fails() {
    let helpers = Helpers::new();
    let raising = guard_over_x(
        &helpers,
        call("checked", vec![Expr::UnOp(UnOp::Neg, Box::new(sp(Expr::Int(5))))]),
    );
    let answering = guard_over_x(&helpers, call("checked", vec![Expr::Int(5)]));

    assert_eq!(
        raising.guards,
        vec![PatternGuardExpr::Const(GroundValue::Bool(false))],
        "the argument selects the clause that raises, which fails the guard"
    );
    assert!(
        answering.guards.is_empty(),
        "the argument selects the clause that answers true"
    );
}

#[test]
fn a_clause_that_raises_beside_one_that_answers_stays_a_call_when_the_argument_is_unknown() {
    let helpers = Helpers::new();
    let plan = guard_over_x(&helpers, call("checked", vec![var("x")]));

    assert!(
        matches!(plan.guards.as_slice(), [PatternGuardExpr::Dispatch { .. }]),
        "only a negation could say the answering clause is the rest: {:?}",
        plan.guards
    );
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
        .trimmed(&|_| crate::dispatch_matrix::LiveEdges::Match, &|_| false, &|_| false)
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

/// The subject that projects `kind` from `source`.
fn projected(plan: &Plan, source: SubjectId, kind: ProjectionKind) -> SubjectId {
    plan.graph
        .subjects
        .iter()
        .find(|subject| match &subject.source {
            SubjectSource::Projection(projection) => projection.source == source && projection.kind == kind,
            SubjectSource::Input { .. } => false,
        })
        .map(|subject| subject.id)
        .expect("the plan projects this subject")
}

fn list_pattern(items: Vec<Pattern>, tail: Option<Pattern>) -> Pattern {
    Pattern::List(items.into_iter().map(sp).collect(), tail.map(|tail| Box::new(sp(tail))))
}

/// `[_, head | tail]` binds a cell and the head and tail inside it. The cell is
/// the one root; the head and the tail are read out of it, so a receiver that
/// copies the cell holds the head and tail of its own copy.
#[test]
fn a_cell_and_the_head_and_tail_inside_it_share_the_cell_as_their_root() {
    let helpers = Helpers::new();
    let head = Pattern::Var(Var::user("head"));
    let tail = Pattern::Var(Var::user("tail"));
    let plan = helpers.plan(
        vec![list_pattern(vec![Pattern::Wildcard, head], Some(tail))],
        Vec::new(),
        Expr::Bool(true),
    );
    let input = SubjectId(0);
    let cell = projected(&plan, input, ProjectionKind::ListTail);
    let head = projected(&plan, cell, ProjectionKind::ListHead);
    let tail = projected(&plan, cell, ProjectionKind::ListTail);

    let roots = plan.outcome_roots([head, tail, cell]);

    assert_eq!(roots.roots, vec![cell]);
    assert_eq!(roots.arguments[0].path.as_slice(), &[head]);
    assert_eq!(roots.arguments[1].path.as_slice(), &[tail]);
    assert!(roots.arguments[2].path.is_empty(), "the cell is its own root");
    assert!(roots.arguments.iter().all(|argument| argument.root == 0));
    assert!(!roots.is_identity());
}

/// Without the cell among the arguments, the head and the tail are disjoint
/// positions of the message, and each is a root of its own.
#[test]
fn a_head_and_a_tail_without_their_cell_are_two_roots() {
    let helpers = Helpers::new();
    let plan = helpers.plan(
        vec![list_pattern(
            vec![Pattern::Var(Var::user("head"))],
            Some(Pattern::Var(Var::user("tail"))),
        )],
        Vec::new(),
        Expr::Bool(true),
    );
    let input = SubjectId(0);
    let head = projected(&plan, input, ProjectionKind::ListHead);
    let tail = projected(&plan, input, ProjectionKind::ListTail);

    let roots = plan.outcome_roots([tail, head]);

    assert_eq!(roots.roots, vec![tail, head], "roots follow the order of the arguments");
    assert!(roots.is_identity(), "nothing is left to project");
}

/// A root is the outermost *argument*, not the outermost subject: an argument
/// deep in a message is its own root when nothing above it is an argument, so
/// the gift carries it and not the message around it.
#[test]
fn an_argument_below_unread_structure_is_a_root_of_its_own() {
    let helpers = Helpers::new();
    let nested = Pattern::Tuple(vec![
        sp(Pattern::Wildcard),
        sp(list_pattern(
            vec![Pattern::Var(Var::user("head"))],
            Some(Pattern::Var(Var::user("tail"))),
        )),
    ]);
    let plan = helpers.plan(vec![nested], Vec::new(), Expr::Bool(true));
    let input = SubjectId(0);
    let list = projected(&plan, input, ProjectionKind::TupleField(1));
    let head = projected(&plan, list, ProjectionKind::ListHead);
    let tail = projected(&plan, list, ProjectionKind::ListTail);

    let roots = plan.outcome_roots([head, tail]);

    assert_eq!(roots.roots, vec![head, tail]);
    assert!(roots.is_identity());
}

fn plan_of_pattern(pattern: Pattern) -> Plan {
    Helpers::new().plan_of_row(PatternRow {
        patterns: vec![sp(pattern)],
        preconditions: Vec::new(),
        guard: None,
        body_id: 0,
    })
}

fn literal_bytes_as_bitstring(bytes: &[u8]) -> Pattern {
    Pattern::Bitstring(crate::ast::binary_literal_fields(bytes, crate::source::Span::DUMMY))
}

#[test]
fn an_empty_string_pattern_asks_the_questions_the_empty_bitstring_pattern_asks() {
    assert_eq!(
        plan_of_pattern(Pattern::Binary(Vec::new())).graph,
        plan_of_pattern(Pattern::Bitstring(Vec::new())).graph,
    );
}

#[test]
fn a_string_pattern_asks_the_questions_its_one_segment_bitstring_asks() {
    assert_eq!(
        plan_of_pattern(Pattern::Binary(b"abc".to_vec())).graph,
        plan_of_pattern(literal_bytes_as_bitstring(b"abc")).graph,
    );
}

#[test]
fn a_string_pattern_never_compares_the_whole_value() {
    let plan = plan_of_pattern(Pattern::Binary(b"abc".to_vec()));
    assert!(
        tests(&plan).iter().all(|predicate| !matches!(
            &predicate.region,
            Region::Equal(ComparisonValue::Const(
                GroundValue::Utf8Binary(_) | GroundValue::Binary(_)
            ))
        )),
        "a string pattern is a size test and byte comparisons, never a whole-value comparison"
    );
}

fn equal_to_earlier_subject(plan: &Plan) -> Vec<(SubjectId, SubjectId)> {
    tests(plan)
        .into_iter()
        .filter_map(|predicate| match &predicate.region {
            Region::Equal(ComparisonValue::Subject(earlier)) => Some((predicate.subject, *earlier)),
            _ => None,
        })
        .collect()
}

#[test]
fn a_variable_repeated_in_a_tuple_binds_once_and_asks_equality_with_its_first_occurrence() {
    let helpers = Helpers::new();
    let plan = helpers.plan_of_row(PatternRow {
        patterns: vec![sp(Pattern::Tuple(vec![sp(x()), sp(x())]))],
        preconditions: Vec::new(),
        guard: None,
        body_id: 0,
    });

    let bindings = &plan.outcomes[0].bindings;
    assert_eq!(bindings.len(), 1, "one binding per name");
    let equalities = equal_to_earlier_subject(&plan);
    assert_eq!(equalities.len(), 1, "the repeat is one equality question");
    assert_eq!(
        equalities[0].1, bindings[0].source,
        "it compares with the first occurrence"
    );
    assert_ne!(equalities[0].0, bindings[0].source, "it asks the second occurrence");
}

#[test]
fn a_variable_repeated_across_parameters_asks_equality_with_the_earlier_parameter() {
    let helpers = Helpers::new();
    let plan = helpers.plan_of_row(PatternRow {
        patterns: vec![sp(x()), sp(x())],
        preconditions: Vec::new(),
        guard: None,
        body_id: 0,
    });

    assert_eq!(plan.outcomes[0].bindings.len(), 1);
    assert_eq!(equal_to_earlier_subject(&plan).len(), 1);
}

fn projecting_extern(property: ProjectedProperty) -> Arc<GuardExtern> {
    use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};
    Arc::new(
        GuardExtern::new(
            ExternAbi::Fz,
            "count",
            &[ExternTy::Any],
            ExternReturn::Scalar(ExternTy::I64),
            false,
        )
        .expect("a counting extern is a guard extern")
        .projecting(Some(property)),
    )
}

/// `def size_is(x, n), do: count(x) == n` over an extern that projects `property`.
fn size_is_helper(property: ProjectedProperty) -> Arc<PatternGuardDispatch<Ty>> {
    let body = compare(BinOp::Eq, call("count", vec![var("x")]), var("n"));
    let surface = Surface(vec![clause(2, None, body)]);
    let two_names = PatternRow {
        patterns: vec![sp(x()), sp(n())],
        preconditions: Vec::new(),
        guard: None,
        body_id: 0,
    };
    let mut resolver = projection_resolver(property, None);
    Arc::new(guard_dispatch_from_rows(&surface, vec![two_names], &mut resolver).expect("size_is reifies"))
}

/// `def int?(_ :: int), do: true; def int?(_), do: abort(1)`: a helper that
/// answers for integers and raises for everything else.
fn answers_or_raises_helper(int: Ty) -> Arc<PatternGuardDispatch<Ty>> {
    let surface = Surface(vec![
        clause(1, None, Expr::Bool(true)),
        clause(1, None, call("abort", vec![Expr::Int(1)])),
    ]);
    let rows = vec![row(1, &[(0, int)], 0), row(1, &[], 1)];
    let mut resolver = |callee: &Callee, _arity: usize| -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok((name.name == "abort").then(|| GuardCallee::Extern(aborting_extern())))
    };
    Arc::new(guard_dispatch_from_rows(&surface, rows, &mut resolver).expect("int? reifies"))
}

fn projection_resolver(
    property: ProjectedProperty,
    size_is: Option<Arc<PatternGuardDispatch<Ty>>>,
) -> impl FnMut(&Callee, usize) -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
    move |callee, _arity| {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok(match name.name.as_str() {
            "count" => Some(GuardCallee::Extern(projecting_extern(property))),
            "size_is" => size_is.as_ref().map(|helper| GuardCallee::Helper(Arc::clone(helper))),
            _ => None,
        })
    }
}

fn plan_with_projection(property: ProjectedProperty, guard: Expr) -> Plan {
    let size_is = size_is_helper(property);
    let row = PatternRow {
        patterns: vec![sp(x())],
        preconditions: Vec::new(),
        guard: Some(sp(guard)),
        body_id: 0,
    };
    let rows = SourcePatternRows::lexical(1, vec![row]);
    pattern_dispatch_from_source_with_resolver(&rows, &mut projection_resolver(property, Some(size_is)))
        .expect("the row compiles")
}

fn regions(plan: &Plan) -> Vec<Region<Ty>> {
    tests(plan)
        .into_iter()
        .map(|predicate| predicate.region.clone())
        .collect()
}

#[test]
fn a_projection_compared_with_a_constant_is_the_question_it_projects_whichever_side_it_is_on() {
    let cases = [
        (ProjectedProperty::FunctionArity, Region::Arity(2)),
        (ProjectedProperty::MapSize, Region::MapSize(2)),
        (ProjectedProperty::ByteSize, Region::ByteSize(2)),
        (ProjectedProperty::TupleSize, Region::TupleArity(2)),
    ];
    for (property, question) in cases {
        for (side, guard) in [
            ("left", compare(BinOp::Eq, call("count", vec![var("x")]), Expr::Int(2))),
            ("right", compare(BinOp::Eq, Expr::Int(2), call("count", vec![var("x")]))),
        ] {
            let plan = plan_with_projection(property, guard);
            assert_eq!(regions(&plan), vec![question.clone()], "{property:?} on the {side}");
            assert!(
                plan.guards.is_empty(),
                "{property:?} on the {side}: nothing is left of the guard"
            );
        }
    }
}

#[test]
fn a_projection_compared_any_other_way_stays_the_guard_it_was_written_as() {
    let cases = [
        (
            "an ordering",
            compare(BinOp::Gt, call("count", vec![var("x")]), Expr::Int(2)),
        ),
        (
            "another subject's size",
            compare(BinOp::Eq, call("count", vec![var("x")]), var("x")),
        ),
        (
            "a negative size",
            compare(BinOp::Eq, call("count", vec![var("x")]), Expr::Int(-1)),
        ),
        (
            "a float",
            compare(BinOp::Eq, call("count", vec![var("x")]), Expr::Float(2.0)),
        ),
    ];
    for (shape, guard) in cases {
        let plan = plan_with_projection(ProjectedProperty::MapSize, guard);
        assert!(
            regions(&plan)
                .iter()
                .all(|region| !matches!(region, Region::MapSize(_))),
            "{shape}: no size question"
        );
        assert_eq!(plan.guards.len(), 1, "{shape}: the guard is kept");
    }
}

#[test]
fn a_helper_that_compares_a_projection_with_its_argument_asks_the_question_for_the_callers_constant() {
    let plan = plan_with_projection(
        ProjectedProperty::FunctionArity,
        call("size_is", vec![var("x"), Expr::Int(3)]),
    );

    assert_eq!(regions(&plan), vec![Region::Arity(3)]);
    assert!(plan.guards.is_empty());
}

#[test]
fn a_negated_helper_that_raises_where_it_does_not_answer_stays_the_guard_that_fails() {
    let helpers = Helpers::new();
    let int_or_raises = answers_or_raises_helper(helpers.int);
    let row = PatternRow {
        patterns: vec![sp(x())],
        preconditions: Vec::new(),
        guard: Some(sp(not(call("int?", vec![var("x")])))),
        body_id: 0,
    };
    let rows = SourcePatternRows::lexical(1, vec![row]);
    let mut resolver = |callee: &Callee, _arity: usize| -> Result<Option<GuardCallee<Ty>>, SourcePatternError> {
        let Callee::Name(name) = callee else { return Ok(None) };
        Ok((name.name == "int?").then(|| GuardCallee::Helper(Arc::clone(&int_or_raises))))
    };
    let plan = pattern_dispatch_from_source_with_resolver(&rows, &mut resolver).expect("the row compiles");

    assert_eq!(
        plan.guards.len(),
        1,
        "not int?(x) cannot be the complement of an int test: for a value that is no integer the helper raises, and a raise fails the guard"
    );
}
