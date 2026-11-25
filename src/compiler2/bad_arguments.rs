//! A built-in function's failure for a bad argument, written once at its
//! definition.
//!
//! A `def` whose tail declares `raises: Exception, reason: :atom` names the
//! failure of a call outside its head: a last clause is added after the
//! function's own, and raises `Exception` with `reason` for the Erlang
//! `catch`, worded as Erlang's error formatter words it, one line for each
//! argument that failed its test. The tests are the conjuncts of the head's
//! guard, and one table gives each its wording.
//!
//! * A call to a test of one argument (`is_integer(n)`) fails that argument
//!   with the test's wording.
//! * Any other conjunct (`n >= 0`, `i <= tuple_size(t)`) is a range. Its
//!   arguments are the ones it names. A range that names one argument is
//!   judged once that argument's tests have passed; a range that relates
//!   several is judged once every tested argument's tests have passed, as
//!   Erlang's BIFs check a length against a start only when both are
//!   integers. The first range to fail names the first of its arguments, and
//!   that argument reads "out of range".

use crate::ast::{BinOp, Expr, FnClause, MatchClause, ModuleTarget, Pattern, Spanned, UnOp, Var, VarContext};
use crate::compiler2::QuotedSourceError;
use crate::modules::identity::ModuleName;
use crate::source::Span;

/// What a definition's `raises:` and `reason:` declare.
#[derive(Debug, Clone)]
pub(super) struct DeclaredFailure {
    pub(super) exception: ModuleName,
    pub(super) reason: String,
}

/// The wording of each test of one argument. The predicates named by a
/// built-in's guard that are not Kernel's own, such as `is_radix/1`, are
/// defined beside the built-in and listed here.
const WORDINGS: &[(&str, &str)] = &[
    ("is_atom", "not an atom"),
    ("is_binary", "not a binary"),
    ("is_bitstring", "not a bitstring"),
    ("is_float", "not a float"),
    ("is_integer", "not an integer"),
    ("is_list", "not a list"),
    ("is_map", "not a map"),
    ("fz_list_is_cons", "not a nonempty list"),
    ("is_number", "not a number"),
    ("is_destination", "invalid destination"),
    ("is_tuple", "not a tuple"),
    ("is_bitstring_subject", "not a binary"),
    ("is_binary_subject", "is a bitstring (expected a binary)"),
    ("is_encoding", "is an invalid encoding option"),
    ("is_float_format", "invalid option in list"),
    ("is_radix", "not an integer in the range 2 through 36"),
];

/// What the first range to fail says of the argument it blames.
const RANGE_WORDING: &str = "out of range";

/// One argument of the definition: the variable its head names, and the tests
/// of it, each with its wording.
struct Argument {
    var: Option<Var>,
    tests: Vec<(Spanned<Expr>, &'static str)>,
}

/// A conjunct that is no test of one argument.
struct Range {
    conjunct: Spanned<Expr>,
    /// The arguments it names, in the order it names them.
    arguments: Vec<usize>,
}

/// The clause that raises `failure` for a call `clause` does not take.
pub(super) fn failure_clause(failure: &DeclaredFailure, clause: &FnClause) -> Result<FnClause, QuotedSourceError> {
    let span = clause.span;
    let mut arguments = clause
        .params
        .iter()
        .map(|param| match &param.node {
            Pattern::Var(var) => Ok(Argument {
                var: Some(var.clone()),
                tests: Vec::new(),
            }),
            Pattern::Wildcard => Ok(Argument {
                var: None,
                tests: Vec::new(),
            }),
            _ => Err(refused(span, "takes plain variables for its arguments")),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let ranges = sort_conjuncts(clause, &mut arguments)?;
    let named: Vec<usize> = ranges
        .iter()
        .flat_map(|range| range.arguments.iter().copied())
        .collect();
    let literal = only_way_to_fail(&arguments, &ranges).is_some();
    for (index, argument) in arguments.iter_mut().enumerate() {
        if literal || (argument.tests.is_empty() && !named.contains(&index)) {
            argument.var = None;
        }
    }
    let blamed = Var {
        name: "blamed".to_string(),
        context: VarContext::minted("bad_arguments", 0),
    };
    let message = failure_message(span, &arguments, &ranges, &blamed);
    let exception = Spanned::new(
        Expr::Struct {
            module: ModuleTarget::Unresolved(failure.exception.clone()),
            fields: vec![("message".to_string(), message)],
        },
        span,
    );
    let raise = Spanned::new(Expr::Var(Var::user("__raise__")), span);
    let reason = Spanned::new(Expr::Atom(failure.reason.clone()), span);
    let body = Spanned::new(Expr::Call(Box::new(raise), vec![exception, reason]), span);
    Ok(FnClause {
        params: arguments
            .iter()
            .map(|argument| {
                let pattern = argument.var.clone().map_or(Pattern::Wildcard, Pattern::Var);
                Spanned::new(pattern, span)
            })
            .collect(),
        param_annotations: vec![None; arguments.len()],
        guard: None,
        body,
        span,
    })
}

/// The message the failure raises. A head with one test and no range has one
/// way to fail, so its message is the text itself.
/// The one argument and wording of a head that can fail in no other way: a
/// single test and no range.
fn only_way_to_fail(arguments: &[Argument], ranges: &[Range]) -> Option<(usize, &'static str)> {
    let mut tested = arguments
        .iter()
        .enumerate()
        .filter(|(_, argument)| !argument.tests.is_empty());
    let (index, argument) = tested.next()?;
    match (tested.next(), argument.tests.as_slice(), ranges.is_empty()) {
        (None, [(_, wording)], true) => Some((index, wording)),
        _ => None,
    }
}

fn failure_message(span: Span, arguments: &[Argument], ranges: &[Range], blamed: &Var) -> Spanned<Expr> {
    let heading = "errors were found at the given arguments:\n\n";
    if let Some((index, wording)) = only_way_to_fail(arguments, ranges) {
        return text(
            span,
            &format!("{heading}  * {} argument: {wording}\n", ordinal(index + 1)),
        );
    }
    let lines = arguments
        .iter()
        .enumerate()
        .filter(|(index, argument)| {
            !argument.tests.is_empty() || ranges.iter().any(|range| range.arguments[0] == *index)
        })
        .map(|(index, argument)| complaint(span, index, argument, blamed, ranges));
    let message = lines.fold(text(span, heading), |message, line| {
        remote(span, "Kernel", "<>", vec![message, line])
    });
    if ranges.is_empty() {
        return message;
    }
    Spanned::new(
        Expr::Case(
            Some(Box::new(blamed_range(ranges, arguments, span))),
            vec![MatchClause {
                pattern: Spanned::new(Pattern::Var(blamed.clone()), span),
                guard: None,
                body: message,
                span,
            }],
        ),
        span,
    )
}

fn refused(span: Span, why: &str) -> QuotedSourceError {
    QuotedSourceError::user(
        crate::diag::codes::PARSE_INVALID_FUNCTION_DEFINITION,
        Some(span),
        format!("a definition that declares `raises:` {why}"),
    )
}

/// Files each conjunct of the guard under the argument it tests, or returns it
/// as a range.
fn sort_conjuncts(clause: &FnClause, arguments: &mut [Argument]) -> Result<Vec<Range>, QuotedSourceError> {
    let Some(guard) = &clause.guard else {
        return Err(refused(
            clause.span,
            "needs a guard: its tests are the failure's wording",
        ));
    };
    let mut conjuncts = Vec::new();
    split_conjuncts(guard, &mut conjuncts);
    let mut ranges = Vec::new();
    for conjunct in conjuncts {
        match tested_argument(conjunct, arguments)? {
            Some((index, wording)) => arguments[index].tests.push((conjunct.clone(), wording)),
            None => ranges.push(Range {
                arguments: named_arguments(conjunct, arguments)?,
                conjunct: conjunct.clone(),
            }),
        }
    }
    Ok(ranges)
}

fn split_conjuncts<'a>(guard: &'a Spanned<Expr>, out: &mut Vec<&'a Spanned<Expr>>) {
    match &guard.node {
        Expr::BinOp(BinOp::And, left, right) => {
            split_conjuncts(left, out);
            split_conjuncts(right, out);
        }
        _ => out.push(guard),
    }
}

/// The argument a test of one argument tests, and its wording.
fn tested_argument(
    conjunct: &Spanned<Expr>,
    arguments: &[Argument],
) -> Result<Option<(usize, &'static str)>, QuotedSourceError> {
    let Expr::Call(callee, args) = &conjunct.node else {
        return Ok(None);
    };
    let Expr::Var(callee) = &callee.node else {
        return Ok(None);
    };
    let [
        Spanned {
            node: Expr::Var(subject),
            ..
        },
    ] = args.as_slice()
    else {
        return Ok(None);
    };
    let Some(index) = arguments
        .iter()
        .position(|argument| argument.var.as_ref() == Some(subject))
    else {
        return Ok(None);
    };
    match WORDINGS.iter().find(|(test, _)| *test == callee.name) {
        Some((_, wording)) => Ok(Some((index, wording))),
        None => Ok(None),
    }
}

/// The arguments a range names, in order of first mention.
fn named_arguments(conjunct: &Spanned<Expr>, arguments: &[Argument]) -> Result<Vec<usize>, QuotedSourceError> {
    let mut found = Vec::new();
    collect_arguments(conjunct, arguments, &mut found)?;
    if found.is_empty() {
        return Err(refused(
            conjunct.span,
            "needs every conjunct of its guard to test an argument",
        ));
    }
    Ok(found)
}

fn collect_arguments(
    expr: &Spanned<Expr>,
    arguments: &[Argument],
    found: &mut Vec<usize>,
) -> Result<(), QuotedSourceError> {
    match &expr.node {
        Expr::Var(var) => {
            if let Some(index) = arguments.iter().position(|argument| argument.var.as_ref() == Some(var))
                && !found.contains(&index)
            {
                found.push(index);
            }
            Ok(())
        }
        Expr::Int(_) | Expr::Float(_) | Expr::Atom(_) | Expr::Bool(_) | Expr::Nil => Ok(()),
        Expr::BinOp(
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Eq
            | BinOp::Neq
            | BinOp::Lt
            | BinOp::LtEq
            | BinOp::Gt
            | BinOp::GtEq,
            left,
            right,
        ) => {
            collect_arguments(left, arguments, found)?;
            collect_arguments(right, arguments, found)
        }
        Expr::UnOp(_, operand) => collect_arguments(operand, arguments, found),
        Expr::Call(callee, args) if matches!(callee.node, Expr::Var(_)) => {
            args.iter().try_for_each(|arg| collect_arguments(arg, arguments, found))
        }
        _ => Err(refused(
            expr.span,
            "takes only comparisons, arithmetic and calls of Kernel functions in the guard beside its tests",
        )),
    }
}

/// The line of the message that is one argument's complaint: the wording of
/// the first of its tests to fail, or "out of range" when it is the argument
/// the first failing range blames, or nothing.
fn complaint(span: Span, index: usize, argument: &Argument, blamed: &Var, ranges: &[Range]) -> Spanned<Expr> {
    let line = |wording: &str| text(span, &format!("  * {} argument: {wording}\n", ordinal(index + 1)));
    let mut arms: Vec<_> = argument
        .tests
        .iter()
        .map(|(test, wording)| (negate(span, test.clone()), line(wording)))
        .collect();
    if ranges.iter().any(|range| range.arguments[0] == index) {
        let is_blamed = Spanned::new(
            Expr::BinOp(
                BinOp::Eq,
                Box::new(Spanned::new(Expr::Var(blamed.clone()), span)),
                Box::new(int(span, index + 1)),
            ),
            span,
        );
        arms.push((is_blamed, line(RANGE_WORDING)));
    }
    arms.push((Spanned::new(Expr::Bool(true), span), text(span, "")));
    first_to_hold(span, arms)
}

fn ordinal(position: usize) -> String {
    match position {
        1 => "1st".to_string(),
        2 => "2nd".to_string(),
        3 => "3rd".to_string(),
        n => format!("{n}th"),
    }
}

/// The position of the argument the first range to fail blames, or 0. A range
/// is judged when the tests of every argument it names pass.
fn blamed_range(ranges: &[Range], arguments: &[Argument], span: Span) -> Spanned<Expr> {
    let mut arms: Vec<_> = ranges
        .iter()
        .map(|range| {
            let judged_arguments: Vec<usize> = match range.arguments.as_slice() {
                [only] => vec![*only],
                _ => (0..arguments.len()).collect(),
            };
            let mut conditions: Vec<_> = judged_arguments
                .iter()
                .flat_map(|index| arguments[*index].tests.iter().map(|(test, _)| test.clone()))
                .collect();
            conditions.push(negate(span, range.conjunct.clone()));
            (conjunction(span, conditions), int(span, range.arguments[0] + 1))
        })
        .collect();
    arms.push((Spanned::new(Expr::Bool(true), span), int(span, 0)));
    first_to_hold(span, arms)
}

/// The body of the first arm whose condition holds, as a `case` whose clauses
/// guard on the conditions: a guard is tested where it stands, so the tests
/// call no function of the module they come from.
fn first_to_hold(span: Span, arms: Vec<(Spanned<Expr>, Spanned<Expr>)>) -> Spanned<Expr> {
    let clauses = arms
        .into_iter()
        .map(|(condition, body)| MatchClause {
            pattern: Spanned::new(Pattern::Wildcard, span),
            guard: (!matches!(condition.node, Expr::Bool(true))).then_some(condition),
            body,
            span,
        })
        .collect();
    let subject = Spanned::new(Expr::Nil, span);
    Spanned::new(Expr::Case(Some(Box::new(subject)), clauses), span)
}

fn conjunction(span: Span, mut conditions: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    let mut all = conditions.remove(0);
    for condition in conditions {
        all = Spanned::new(Expr::BinOp(BinOp::And, Box::new(all), Box::new(condition)), span);
    }
    all
}

fn negate(span: Span, expr: Spanned<Expr>) -> Spanned<Expr> {
    Spanned::new(Expr::UnOp(UnOp::Not, Box::new(expr)), span)
}

fn int(span: Span, n: usize) -> Spanned<Expr> {
    Spanned::new(Expr::Int(n as i64), span)
}

fn text(span: Span, words: &str) -> Spanned<Expr> {
    Spanned::new(Expr::Binary(words.as_bytes().to_vec()), span)
}

fn remote(span: Span, module: &str, function: &str, args: Vec<Spanned<Expr>>) -> Spanned<Expr> {
    let module = Spanned::new(Expr::Alias(ModuleName::from_segments(vec![module.to_string()])), span);
    let function = Spanned::new(Expr::Atom(function.to_string()), span);
    let callee = Spanned::new(Expr::Index(Box::new(module), Box::new(function)), span);
    Spanned::new(Expr::Call(Box::new(callee), args), span)
}
