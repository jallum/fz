use self::source::{collect_pinned_names, direct_bitfield_bindings};
#[cfg(test)]
use super::DispatchMatrix;
use super::{
    BitstringEndian, BitstringFieldKind, BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue,
    DispatchCompileError, DispatchGraph, DispatchMatrixBuilder, DispatchMatrixError, EdgeEvidence, GraphNodeId,
    GroundValue, GuardId, GuardLeaf, LiveEdges, OutcomeId, OutcomeMultiplicity, PinnedValueId, PlanInputs,
    PreparedKeyId, ProjectionKind, Region, RegionPredicate, RegionQuestion, SubjectId, compile_dispatch_matrix,
    demand::DispatchDemand,
};
use crate::ast::{BitSize, BitType, Endian, Expr, Pattern, Spanned, Var};
use crate::function_surface::CallableSurface;
use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};
use crate::source::Span;
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) mod last_resort;
pub(crate) mod source;
pub(crate) use last_resort::LastResort;
pub(crate) use source::{PatternBodyId, PatternRow, SourcePatternError, SourcePatternRows};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchPlan<TypeHandle> {
    pub(crate) graph: DispatchGraph<TypeHandle>,
    #[cfg(test)]
    pub(crate) source_matrix: DispatchMatrix<TypeHandle>,
    pub(crate) input_count: usize,
    pub(crate) outcomes: Vec<PatternDispatchOutcome>,
    pub(crate) guards: Vec<PatternGuardExpr<TypeHandle>>,
    pub(crate) pinned: Vec<PatternPinnedInput>,
    pub(crate) prepared_keys: Vec<GroundValue>,
    /// The exception a decision that ends with no outcome raises, or `None`
    /// when the construct that owns the plan takes such a decision elsewhere:
    /// a guard answers false, a `cond` tries its next condition, a `with`
    /// takes its `else`, a `receive` waits.
    pub(crate) last_resort: Option<LastResort>,
    /// The tuple arity a winning decision proves of each input, read from the
    /// graph as built. Narrowing may later drop the question that proved it,
    /// because the input's type already answers it; the proof still holds.
    proven_tuple_arities: Vec<Option<u32>>,
}

impl<TypeHandle> PatternDispatchPlan<TypeHandle> {
    /// The tuple arity every outcome of this plan proves `ordinal` to have.
    pub(crate) fn proven_tuple_arity(&self, ordinal: usize) -> Option<usize> {
        self.proven_tuple_arities
            .get(ordinal)
            .copied()
            .flatten()
            .map(|arity| arity as usize)
    }

    pub(crate) fn outcome(&self, id: OutcomeId) -> Option<&PatternDispatchOutcome> {
        self.outcomes.get(id.0 as usize)
    }

    /// The body a winning outcome names. Every outcome the graph can reach is
    /// one this plan carries, so a decision always has a body.
    pub(crate) fn body_id(&self, outcome: OutcomeId) -> PatternBodyId {
        self.outcome(outcome).expect("a winning outcome names a body").body_id
    }

    pub(crate) fn subject(&self, id: SubjectId) -> &super::SubjectSource {
        &self
            .graph
            .subject(id)
            .expect("a plan subject must be retained by its graph")
            .source
    }

    /// What this plan reads of each of its inputs, one slot per declared input.
    pub(crate) fn input_demand(&self) -> &[DispatchDemand] {
        &self.graph.input_demand
    }

    /// Whether deciding a clause reads this input at all. A caller is free to
    /// pass anything else as nil.
    pub(crate) fn required_input(&self, ordinal: usize) -> bool {
        self.input_demand()
            .get(ordinal)
            .is_some_and(DispatchDemand::asks_anything)
    }

    pub(crate) fn prepared_key_id(&self, key: &GroundValue) -> Option<PreparedKeyId> {
        self.prepared_keys
            .iter()
            .position(|prepared| prepared == key)
            .map(|index| PreparedKeyId(index as u32))
    }

    pub(crate) fn bitstring_extraction(&self, id: SubjectId) -> &super::BitstringExtraction {
        let super::SubjectSource::Projection(projection) = self.subject(id) else {
            panic!("a bitstring extraction must be a projected subject");
        };
        let ProjectionKind::BitstringField(extraction) = &projection.kind else {
            panic!("a bitstring shape must name exact extraction subjects");
        };
        extraction
    }

    /// Whether some decision of this plan ends with no outcome.
    pub(crate) fn can_fail(&self) -> bool {
        self.graph.can_fail()
    }

    /// Whether this plan wins its one outcome without asking anything.
    pub(crate) fn is_direct_outcome(&self) -> bool {
        self.graph.is_outcome_at_root()
    }

    /// This plan with every test `live` narrows replaced by the one child it
    /// keeps, or `None` when no test a decision can reach is narrowed. Subject
    /// ids, outcome ids, guards and pins are the plan's own, so everything that
    /// names them reads the trimmed plan unchanged.
    pub(crate) fn trimmed(
        &self,
        live: &impl Fn(GraphNodeId) -> LiveEdges,
        literal_blind: &dyn Fn(&TypeHandle) -> bool,
    ) -> Option<Self>
    where
        TypeHandle: Clone + Eq,
    {
        let pinned = self.pinned.iter().map(|pin| pin.input).collect::<Vec<_>>();
        let guard_leaves = self.guards.iter().map(PatternGuardExpr::leaves).collect::<Vec<_>>();
        let graph = self.graph.trimmed(
            PlanInputs {
                count: self.input_count,
                pinned: &pinned,
                guard_leaves: &guard_leaves,
                literal_blind,
            },
            live,
        )?;
        Some(Self {
            graph,
            #[cfg(test)]
            source_matrix: self.source_matrix.clone(),
            input_count: self.input_count,
            outcomes: self.outcomes.clone(),
            guards: self.guards.clone(),
            pinned: self.pinned.clone(),
            prepared_keys: self.prepared_keys.clone(),
            last_resort: self.last_resort.clone(),
            proven_tuple_arities: self.proven_tuple_arities.clone(),
        })
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternDispatchPlan<MappedHandle> {
        PatternDispatchPlan {
            graph: self.graph.map_type_handle(map),
            #[cfg(test)]
            source_matrix: self.source_matrix.map_type_handle(map),
            input_count: self.input_count,
            outcomes: self.outcomes.clone(),
            guards: self.guards.iter().map(|guard| guard.map_type_handle(map)).collect(),
            pinned: self.pinned.clone(),
            prepared_keys: self.prepared_keys.clone(),
            last_resort: self.last_resort.clone(),
            proven_tuple_arities: self.proven_tuple_arities.clone(),
        }
    }
}

/// A name a pattern reaches for but does not bind. Its value was bound before
/// the pattern began: `input` names the plan input that delivers that binding
/// when the rows carry a prematch, and is `None` when the lowerer resolves the
/// name in the scope enclosing the match instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternPinnedInput {
    pub(crate) name: Var,
    pub(crate) input: Option<u32>,
    pub(crate) span: Span,
    pub(crate) kind: PinnedKind,
}

impl PatternPinnedInput {
    /// What a reader is told when this name was never bound. The wording is
    /// Elixir's: a pin says which pin and why, a plain variable is just an
    /// undefined variable.
    pub(crate) fn undefined_message(&self) -> String {
        match self.kind {
            PinnedKind::Pin => format!(
                "undefined variable ^{}. No variable \"{}\" has been defined before the current pattern",
                self.name, self.name
            ),
            PinnedKind::Variable => format!("undefined variable \"{}\"", self.name),
        }
    }
}

/// How a pattern reached for the name, which is what a diagnostic has to say
/// back to the author.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PinnedKind {
    /// `^name` in a pattern.
    Pin,
    /// A name spelled without a pin: a guard variable no pattern in the same
    /// row binds, or a bitstring `size(name)` no earlier field binds.
    Variable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchOutcome {
    pub(crate) body_id: PatternBodyId,
    pub(crate) bindings: Vec<PatternDispatchBinding>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchBinding {
    pub(crate) name: Var,
    pub(crate) source: SubjectId,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum PatternSubjectRef {
    Input(u32),
    TupleField {
        tuple: Box<PatternSubjectRef>,
        index: u32,
    },
    StructField {
        record: Box<PatternSubjectRef>,
        field: String,
    },
    ListHead(Box<PatternSubjectRef>),
    ListTail(Box<PatternSubjectRef>),
    MapValue {
        map: Box<PatternSubjectRef>,
        key: GroundValue,
    },
    Subject(SubjectId),
}

pub(crate) trait PatternResolver<TypeHandle> {
    fn struct_type(&mut self, module: &crate::ast::ModuleTarget, span: Span) -> Result<TypeHandle, SourcePatternError>;

    /// The atom a module alias written in a guard stands for.
    fn module_alias_atom(&mut self, alias: &crate::modules::identity::ModuleName)
    -> Result<String, SourcePatternError>;

    fn guard_call(
        &mut self,
        callee: &crate::ast::Callee,
        arity: usize,
    ) -> Result<Option<GuardCallee<TypeHandle>>, SourcePatternError>;

    /// Whether a type test over this type can tell one literal from another.
    /// It cannot when the type names no specific atom anywhere inside it.
    fn is_literal_blind(&self, ty: &TypeHandle) -> bool;
}

/// What a call in a guard reaches: a helper whose clauses are reified into
/// their own plan, or an extern, which has no clauses and is called as it is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GuardCallee<TypeHandle> {
    Helper(Arc<PatternGuardDispatch<TypeHandle>>),
    Extern(Arc<GuardExtern>),
}

impl<TypeHandle> GuardCallee<TypeHandle> {
    /// Whether a call can only abort: the extern returns `never`, or the
    /// helper has bodies and every one of them is a failing node.
    fn always_fails(&self) -> bool {
        match self {
            GuardCallee::Extern(extern_fn) => extern_fn.fails_the_guard(),
            GuardCallee::Helper(dispatch) => {
                !dispatch.bodies.is_empty()
                    && dispatch
                        .bodies
                        .iter()
                        .all(|body| matches!(body, PatternGuardExpr::Fails))
            }
        }
    }
}

/// An extern a guard calls. Every parameter is one of the classes all three
/// guard evaluators can carry: an integer, a float, or a reference word. The
/// return is one of those or a boolean, which the guard reads as `true` or
/// `false`. A return of `never` is the call that fails the guard, and
/// so is the failure a checked return declares: either way the clause does not
/// match.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GuardExtern {
    pub(crate) abi: ExternAbi,
    pub(crate) symbol: String,
    pub(crate) params: Vec<ExternTy>,
    pub(crate) ret: ExternReturn,
}

impl GuardExtern {
    /// The extern a guard may call, or what keeps it out. The class rule lives
    /// here, where the node is made, so no evaluator is handed a call it
    /// cannot carry.
    pub(crate) fn new(
        abi: ExternAbi,
        symbol: &str,
        params: &[ExternTy],
        ret: ExternReturn,
        variadic: bool,
    ) -> Result<Self, SourcePatternError> {
        let refuse = |why: String| SourcePatternError::GuardExternClass {
            symbol: symbol.to_string(),
            why,
        };
        if variadic {
            return Err(refuse("a variadic extern has no fixed argument classes".to_string()));
        }
        if let Some(param) = params
            .iter()
            .find(|ty| !matches!(ty, ExternTy::I64 | ExternTy::F64 | ExternTy::Any))
        {
            return Err(refuse(format!(
                "parameter class {param:?} is neither a number nor a reference word"
            )));
        }
        let carried = match &ret {
            ExternReturn::Scalar(lane) | ExternReturn::Checked(lane, _) => {
                matches!(
                    lane,
                    ExternTy::I64 | ExternTy::F64 | ExternTy::Any | ExternTy::Bool | ExternTy::Never
                )
            }
        };
        if !carried {
            return Err(refuse(format!(
                "return {ret:?} is neither a number, a boolean nor a reference word"
            )));
        }
        Ok(Self {
            abi,
            symbol: symbol.to_string(),
            params: params.to_vec(),
            ret,
        })
    }

    /// A call to this extern aborts the process, so in a guard it is the
    /// guard's failure. `guard_expr_from_ast` is the one place that reads this.
    fn fails_the_guard(&self) -> bool {
        self.ret == ExternTy::Never
    }
}

impl<TypeHandle, F> PatternResolver<TypeHandle> for F
where
    F: FnMut(&crate::ast::Callee, usize) -> Result<Option<GuardCallee<TypeHandle>>, SourcePatternError>,
{
    fn struct_type(
        &mut self,
        module: &crate::ast::ModuleTarget,
        _span: Span,
    ) -> Result<TypeHandle, SourcePatternError> {
        Err(SourcePatternError::UnresolvedStruct(module.clone()))
    }

    fn module_alias_atom(
        &mut self,
        _alias: &crate::modules::identity::ModuleName,
    ) -> Result<String, SourcePatternError> {
        Err(SourcePatternError::UnsupportedGuardExpr)
    }

    fn guard_call(
        &mut self,
        callee: &crate::ast::Callee,
        arity: usize,
    ) -> Result<Option<GuardCallee<TypeHandle>>, SourcePatternError> {
        self(callee, arity)
    }

    /// A bare closure resolver has no type calculator to ask, so it claims
    /// nothing: every type test is read as telling literals apart.
    fn is_literal_blind(&self, _ty: &TypeHandle) -> bool {
        false
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternGuardExpr<TypeHandle> {
    Const(GroundValue),
    Subject(SubjectId),
    Pinned(PinnedValueId),
    Unary {
        op: PatternGuardUnaryOp,
        expr: Box<PatternGuardExpr<TypeHandle>>,
    },
    Binary {
        op: PatternGuardBinOp,
        lhs: Box<PatternGuardExpr<TypeHandle>>,
        rhs: Box<PatternGuardExpr<TypeHandle>>,
    },
    Dispatch {
        inputs: Vec<PatternGuardExpr<TypeHandle>>,
        /// The caller-owned operands the helper call needs. A helper is fed
        /// only by its call arguments, so the one thing it borrows from its
        /// caller is the prepared constants its plan compares against.
        prepared: Vec<PreparedKeyId>,
        /// The helper this call decides. Every reference to a helper names the
        /// same plan, so the node shares it rather than carrying a copy. The
        /// share is atomic because a plan travels between scheduler threads
        /// inside `fz_ir::Term::ReceiveMatched`.
        dispatch: Arc<PatternGuardDispatch<TypeHandle>>,
    },
    /// A call to an extern. Externs are assumed pure for now, so a guard may
    /// make the call; one that returns `never` fails the guard instead.
    Extern {
        extern_fn: Arc<GuardExtern>,
        args: Vec<PatternGuardExpr<TypeHandle>>,
    },
    /// A call that can only abort the process: an extern returning `never`,
    /// or a helper every body of which is itself this node. In a guard the
    /// abort is the guard's failure, so the node carries no arguments and no
    /// evaluator builds any.
    Fails,
}

impl<TypeHandle> PatternGuardExpr<TypeHandle> {
    /// Every value this expression reads: the subjects and pins that reach it.
    /// A nested helper call contributes only what its argument expressions
    /// read, because the helper's own plan is closed over its own input space.
    fn leaves(&self) -> Vec<GuardLeaf> {
        let mut leaves = Vec::new();
        self.collect_leaves(&mut leaves);
        leaves
    }

    fn collect_leaves(&self, leaves: &mut Vec<GuardLeaf>) {
        match self {
            PatternGuardExpr::Const(_) | PatternGuardExpr::Fails => {}
            PatternGuardExpr::Subject(subject) => leaves.push(GuardLeaf::Subject(*subject)),
            PatternGuardExpr::Pinned(pinned) => leaves.push(GuardLeaf::Pinned(*pinned)),
            PatternGuardExpr::Unary { expr, .. } => expr.collect_leaves(leaves),
            PatternGuardExpr::Binary { lhs, rhs, .. } => {
                lhs.collect_leaves(leaves);
                rhs.collect_leaves(leaves);
            }
            PatternGuardExpr::Dispatch { inputs, .. } => {
                for input in inputs {
                    input.collect_leaves(leaves);
                }
            }
            PatternGuardExpr::Extern { args, .. } => {
                for arg in args {
                    arg.collect_leaves(leaves);
                }
            }
        }
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternGuardExpr<MappedHandle> {
        match self {
            PatternGuardExpr::Const(value) => PatternGuardExpr::Const(value.clone()),
            PatternGuardExpr::Fails => PatternGuardExpr::Fails,
            PatternGuardExpr::Subject(subject) => PatternGuardExpr::Subject(*subject),
            PatternGuardExpr::Pinned(pinned) => PatternGuardExpr::Pinned(*pinned),
            PatternGuardExpr::Unary { op, expr } => PatternGuardExpr::Unary {
                op: *op,
                expr: Box::new(expr.map_type_handle(map)),
            },
            PatternGuardExpr::Binary { op, lhs, rhs } => PatternGuardExpr::Binary {
                op: *op,
                lhs: Box::new(lhs.map_type_handle(map)),
                rhs: Box::new(rhs.map_type_handle(map)),
            },
            PatternGuardExpr::Dispatch {
                inputs,
                prepared,
                dispatch,
            } => PatternGuardExpr::Dispatch {
                inputs: inputs.iter().map(|input| input.map_type_handle(map)).collect(),
                prepared: prepared.clone(),
                dispatch: Arc::new(dispatch.map_type_handle(map)),
            },
            PatternGuardExpr::Extern { extern_fn, args } => PatternGuardExpr::Extern {
                extern_fn: Arc::clone(extern_fn),
                args: args.iter().map(|arg| arg.map_type_handle(map)).collect(),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternGuardDispatch<TypeHandle> {
    pub(crate) plan: Box<PatternDispatchPlan<TypeHandle>>,
    pub(crate) bodies: Vec<PatternGuardExpr<TypeHandle>>,
    /// Set when the helper only asks of each listed argument whether it has a
    /// type: a call to it holds exactly when every listed argument has its type.
    pub(crate) type_predicate: Option<Vec<(u32, TypeHandle)>>,
}

impl<TypeHandle> PatternGuardDispatch<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternGuardDispatch<MappedHandle> {
        PatternGuardDispatch {
            plan: Box::new(self.plan.map_type_handle(map)),
            bodies: self.bodies.iter().map(|body| body.map_type_handle(map)).collect(),
            type_predicate: self
                .type_predicate
                .as_ref()
                .map(|asked| asked.iter().map(|(argument, ty)| (*argument, map(ty))).collect()),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PatternGuardUnaryOp {
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PatternGuardBinOp {
    Eq,
    Neq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternDispatchError {
    SourcePattern(SourcePatternError),
    MatrixBuild(DispatchMatrixError),
    Compile(DispatchCompileError),
}

/// Reifies a helper from its clause rows. The caller builds the rows with the
/// same clause-to-row function an entry uses, so a helper's typed heads ask
/// the questions a direct call asks.
pub(crate) fn guard_dispatch_from_rows<F, TypeHandle>(
    surface: &impl CallableSurface,
    rows: Vec<PatternRow<TypeHandle>>,
    resolver: &mut F,
) -> Result<PatternGuardDispatch<TypeHandle>, SourcePatternError>
where
    F: PatternResolver<TypeHandle>,
    TypeHandle: Clone + PartialEq + Eq,
{
    let arity = surface.arity();
    if surface.clauses().is_empty() || surface.clauses().iter().any(|clause| clause.params.len() != arity) {
        return Err(SourcePatternError::UnsupportedGuardExpr);
    }

    let type_predicate = type_predicate_of(surface, &rows);

    // A helper is an ordinary function, entered with nothing bound before its
    // patterns, so a pin in one of its heads names a binding that never
    // existed and its own plan is where that is found.
    let source_patterns = SourcePatternRows::entry(arity, rows, Vec::new());
    let mut plan = pattern_dispatch_from_source_with_resolver(source_patterns, resolver).map_err(|err| match err {
        PatternDispatchError::SourcePattern(err) => err,
        other => SourcePatternError::DispatchMatrix(format!("{other:?}")),
    })?;

    // The plan above carries no pin, because a helper's rows have nothing
    // bound before them. So a name in a helper body is either one its own head
    // bound or one that was never bound at all, and lowering the body says
    // which.
    let pinned_by_name = HashMap::new();

    let mut bodies = Vec::with_capacity(surface.clauses().len());
    for clause in surface.clauses() {
        let outcome = plan
            .outcomes
            .iter()
            .find(|outcome| outcome.body_id as usize == bodies.len())
            .ok_or(SourcePatternError::UnsupportedGuardExpr)?;
        let bindings = outcome
            .bindings
            .iter()
            .map(|binding| (binding.name.clone(), binding.source))
            .collect::<HashMap<_, _>>();
        bodies.push(guard_expr_from_ast(
            &clause.body.node,
            &bindings,
            &pinned_by_name,
            &mut plan.prepared_keys,
            resolver,
        )?);
    }

    Ok(PatternGuardDispatch {
        plan: Box::new(plan),
        bodies,
        type_predicate,
    })
}

/// What a helper asks when it is only a type test: exactly two clauses, the
/// first answering `true` for annotated parameters and the second `false` for
/// anything, with every parameter a plain variable or `_` and no guard.
fn type_predicate_of<TypeHandle: Clone>(
    surface: &impl CallableSurface,
    rows: &[PatternRow<TypeHandle>],
) -> Option<Vec<(u32, TypeHandle)>> {
    let ([yes, no], [yes_row, no_row]) = (surface.clauses(), rows) else {
        return None;
    };
    let plain = |clause: &crate::ast::FnClause| {
        clause.guard.is_none()
            && clause
                .params
                .iter()
                .all(|param| matches!(param.node, Pattern::Var(_) | Pattern::Wildcard))
    };
    let answers = matches!(yes.body.node, Expr::Bool(true)) && matches!(no.body.node, Expr::Bool(false));
    if !(answers && plain(yes) && plain(no) && no_row.preconditions.is_empty()) {
        return None;
    }
    let asked = yes_row
        .preconditions
        .iter()
        .map(|(subject, ty)| match subject {
            PatternSubjectRef::Input(argument) => Some((*argument, ty.clone())),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    (!asked.is_empty()).then_some(asked)
}

/// Builds one guard expression from its source form.
fn guard_expr_from_ast<F, TypeHandle>(
    expr: &Expr,
    bindings: &HashMap<Var, SubjectId>,
    pinned_by_name: &HashMap<Var, PinnedValueId>,
    prepared_keys: &mut Vec<GroundValue>,
    resolver: &mut F,
) -> Result<PatternGuardExpr<TypeHandle>, SourcePatternError>
where
    F: PatternResolver<TypeHandle>,
{
    Ok(match expr {
        Expr::Int(value) => PatternGuardExpr::Const(GroundValue::Int(*value)),
        Expr::Float(value) => PatternGuardExpr::Const(GroundValue::Float(value.to_bits())),
        Expr::Binary(bytes) => PatternGuardExpr::Const(GroundValue::Utf8Binary(bytes.clone())),
        Expr::Atom(name) => PatternGuardExpr::Const(GroundValue::Atom(name.clone())),
        Expr::Bool(value) => PatternGuardExpr::Const(GroundValue::Bool(*value)),
        Expr::Nil => PatternGuardExpr::Const(GroundValue::Nil),
        Expr::Alias(alias) => PatternGuardExpr::Const(GroundValue::Atom(resolver.module_alias_atom(alias)?)),
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                PatternGuardExpr::Subject(*subject)
            } else if let Some(pinned) = pinned_by_name.get(name) {
                PatternGuardExpr::Pinned(*pinned)
            } else {
                return Err(SourcePatternError::UnknownGuardVar(name.to_string()));
            }
        }
        Expr::Ascribe(inner, _) => guard_expr_from_ast(&inner.node, bindings, pinned_by_name, prepared_keys, resolver)?,
        Expr::UnOp(crate::ast::UnOp::Not, arg) => PatternGuardExpr::Unary {
            op: PatternGuardUnaryOp::Not,
            expr: Box::new(guard_expr_from_ast(
                &arg.node,
                bindings,
                pinned_by_name,
                prepared_keys,
                resolver,
            )?),
        },
        Expr::UnOp(crate::ast::UnOp::Neg, arg) => guard_call_expr(
            crate::ast::Callee::Name(crate::ast::CallableName::negation()),
            [&arg.node].into_iter(),
            bindings,
            pinned_by_name,
            prepared_keys,
            resolver,
        )?,
        Expr::BinOp(op, lhs, rhs) if op.arithmetic_function().is_some() => guard_call_expr(
            crate::ast::Callee::Name(crate::ast::CallableName::source(
                op.arithmetic_function().expect("matched by the guard above"),
            )),
            [&lhs.node, &rhs.node].into_iter(),
            bindings,
            pinned_by_name,
            prepared_keys,
            resolver,
        )?,
        Expr::BinOp(op, lhs, rhs) => PatternGuardExpr::Binary {
            op: match op {
                crate::ast::BinOp::Eq => PatternGuardBinOp::Eq,
                crate::ast::BinOp::Neq => PatternGuardBinOp::Neq,
                crate::ast::BinOp::Lt => PatternGuardBinOp::Lt,
                crate::ast::BinOp::LtEq => PatternGuardBinOp::LtEq,
                crate::ast::BinOp::Gt => PatternGuardBinOp::Gt,
                crate::ast::BinOp::GtEq => PatternGuardBinOp::GtEq,
                crate::ast::BinOp::And => PatternGuardBinOp::And,
                crate::ast::BinOp::Or => PatternGuardBinOp::Or,
                crate::ast::BinOp::Add
                | crate::ast::BinOp::Sub
                | crate::ast::BinOp::Mul
                | crate::ast::BinOp::Div
                | crate::ast::BinOp::Rem => unreachable!("an arithmetic operator is a call"),
                crate::ast::BinOp::Pipe
                | crate::ast::BinOp::Cons
                | crate::ast::BinOp::ListConcat
                | crate::ast::BinOp::ListSubtract
                | crate::ast::BinOp::BinConcat
                | crate::ast::BinOp::Range
                | crate::ast::BinOp::RangeStep
                | crate::ast::BinOp::In
                | crate::ast::BinOp::NotIn => return Err(SourcePatternError::UnsupportedGuardExpr),
            },
            lhs: Box::new(guard_expr_from_ast(
                &lhs.node,
                bindings,
                pinned_by_name,
                prepared_keys,
                resolver,
            )?),
            rhs: Box::new(guard_expr_from_ast(
                &rhs.node,
                bindings,
                pinned_by_name,
                prepared_keys,
                resolver,
            )?),
        },
        Expr::Call(target, args) => {
            let Some(callee) = crate::ast::Callee::for_call(&target.node, args.len()) else {
                return Err(SourcePatternError::UnsupportedGuardExpr);
            };
            guard_call_expr(
                callee,
                args.iter().map(|arg| &arg.node),
                bindings,
                pinned_by_name,
                prepared_keys,
                resolver,
            )?
        }
        _ => return Err(SourcePatternError::UnsupportedGuardExpr),
    })
}

/// A guard's call: an operator or a named function, resolved through the same
/// namespace a body's call is.
fn guard_call_expr<'e, F, TypeHandle>(
    callee: crate::ast::Callee,
    args: impl ExactSizeIterator<Item = &'e Expr>,
    bindings: &HashMap<Var, SubjectId>,
    pinned_by_name: &HashMap<Var, PinnedValueId>,
    prepared_keys: &mut Vec<GroundValue>,
    resolver: &mut F,
) -> Result<PatternGuardExpr<TypeHandle>, SourcePatternError>
where
    F: PatternResolver<TypeHandle>,
{
    let arity = args.len();
    let callee = resolver
        .guard_call(&callee, arity)?
        .ok_or(SourcePatternError::UnsupportedGuardExpr)?;
    if callee.always_fails() {
        return Ok(PatternGuardExpr::Fails);
    }
    let args = args
        .map(|arg| guard_expr_from_ast(arg, bindings, pinned_by_name, prepared_keys, resolver))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(match callee {
        GuardCallee::Helper(dispatch) => {
            let prepared = dispatch
                .plan
                .prepared_keys
                .iter()
                .map(|key| intern_prepared_key(prepared_keys, key))
                .collect();
            PatternGuardExpr::Dispatch {
                inputs: args,
                prepared,
                dispatch,
            }
        }
        GuardCallee::Extern(extern_fn) => PatternGuardExpr::Extern { extern_fn, args },
    })
}

pub(crate) fn pattern_dispatch_from_source<TypeHandle: Clone + PartialEq + Eq>(
    patterns: SourcePatternRows<TypeHandle>,
) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError> {
    let mut resolver = |_callee: &crate::ast::Callee,
                        _arity: usize|
     -> Result<Option<GuardCallee<TypeHandle>>, SourcePatternError> { Ok(None) };
    pattern_dispatch_from_source_with_resolver(patterns, &mut resolver)
}

pub(crate) fn pattern_dispatch_from_source_with_resolver<F, TypeHandle>(
    patterns: SourcePatternRows<TypeHandle>,
    resolver: &mut F,
) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError>
where
    F: PatternResolver<TypeHandle>,
    TypeHandle: Clone + PartialEq + Eq,
{
    let mut producer = PatternDispatchProducer::new(&patterns).map_err(PatternDispatchError::SourcePattern)?;
    producer
        .add_rows(patterns.rows, resolver)
        .map_err(PatternDispatchError::SourcePattern)?;
    producer.finish(&*resolver)
}

struct PatternDispatchProducer<TypeHandle> {
    builder: DispatchMatrixBuilder<TypeHandle>,
    input_count: usize,
    prematch: source::Prematch,
    subjects: HashMap<PatternSubjectRef, SubjectId>,
    guard_subject: SubjectId,
    pinned: Vec<PatternPinnedInput>,
    pinned_by_name: HashMap<Var, PinnedValueId>,
    prepared_keys: Vec<GroundValue>,
    outcomes: Vec<PatternDispatchOutcome>,
    guards: Vec<PatternGuardExpr<TypeHandle>>,
    projections: HashMap<(SubjectId, ProjectionKind), SubjectId>,
    last_resort: Option<LastResort>,
}

impl<TypeHandle: Clone + PartialEq + Eq> PatternDispatchProducer<TypeHandle> {
    fn new(patterns: &SourcePatternRows<TypeHandle>) -> Result<Self, SourcePatternError> {
        validate_source_rows(patterns)?;
        let mut builder = DispatchMatrixBuilder::typed();
        let mut subjects = HashMap::new();
        for ordinal in 0..patterns.input_count {
            let subject = builder.add_input_subject();
            let ordinal = ordinal as u32;
            subjects.insert(PatternSubjectRef::Input(ordinal), subject);
        }
        let guard_subject = subjects
            .get(&PatternSubjectRef::Input(0))
            .copied()
            .unwrap_or_else(|| builder.add_input_subject());
        let pinned = collect_pinned_names(patterns);
        let pinned_by_name = pinned
            .iter()
            .enumerate()
            .map(|(index, pin)| (pin.name.clone(), PinnedValueId(index as u32)))
            .collect();
        Ok(Self {
            builder,
            input_count: patterns.input_count,
            prematch: patterns.prematch.clone(),
            subjects,
            guard_subject,
            pinned,
            pinned_by_name,
            prepared_keys: Vec::new(),
            outcomes: Vec::new(),
            guards: Vec::new(),
            projections: HashMap::new(),
            last_resort: patterns.last_resort.clone(),
        })
    }

    fn add_rows<F>(&mut self, rows: Vec<PatternRow<TypeHandle>>, resolver: &mut F) -> Result<(), SourcePatternError>
    where
        F: PatternResolver<TypeHandle>,
    {
        for row in rows {
            self.add_row(row, resolver)?;
        }
        Ok(())
    }

    fn add_row<F>(&mut self, row: PatternRow<TypeHandle>, resolver: &mut F) -> Result<(), SourcePatternError>
    where
        F: PatternResolver<TypeHandle>,
    {
        let mut questions: Vec<RegionQuestion<TypeHandle>> = Vec::new();
        let mut bindings = Vec::new();
        for (ordinal, pattern) in row.patterns.iter().enumerate() {
            let subject = PatternSubjectRef::Input(ordinal as u32);
            self.append_pattern(
                &pattern.node,
                pattern.span,
                &subject,
                &mut questions,
                &mut bindings,
                resolver,
            )?;
        }
        for (subject_ref, ty) in &row.preconditions {
            let subject = self.subject_id(subject_ref)?;
            questions.push(RegionQuestion::type_region(subject, ty.clone()));
        }
        if let Some(guard) = &row.guard {
            let mut bound: HashMap<Var, SubjectId> = HashMap::new();
            for binding in &bindings {
                bound.insert(binding.name.clone(), binding.source);
            }
            let mut remaining = Vec::new();
            for conjunct in and_chain(guard) {
                match type_test_of(conjunct, &bound, resolver)? {
                    Some(asked) => {
                        for (subject, ty) in asked {
                            let question = RegionQuestion::type_region(subject, ty);
                            if !questions.contains(&question) {
                                questions.push(question);
                            }
                        }
                    }
                    None => remaining.push(conjunct),
                }
            }
            let mut guard_exprs = Vec::with_capacity(remaining.len());
            for conjunct in remaining {
                guard_exprs.push(guard_expr_from_ast(
                    &conjunct.node,
                    &bound,
                    &self.pinned_by_name,
                    &mut self.prepared_keys,
                    resolver,
                )?);
            }
            let guard_expr = guard_exprs.into_iter().reduce(|lhs, rhs| PatternGuardExpr::Binary {
                op: PatternGuardBinOp::And,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
            if let Some(guard_expr) = guard_expr {
                let guard_id = GuardId(self.guards.len() as u32);
                self.guards.push(guard_expr);
                questions.push(RegionQuestion::new(RegionPredicate::new(
                    self.guard_subject,
                    Region::Guard(guard_id),
                )));
            }
        }
        let outcome = self.builder.add_outcome(OutcomeMultiplicity::Unique);
        self.builder
            .add_arm_questions(questions, EdgeEvidence::empty(), outcome)
            .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?;
        self.outcomes.push(PatternDispatchOutcome {
            body_id: row.body_id,
            bindings,
            span: row
                .patterns
                .first()
                .map(|pattern| pattern.span)
                .or_else(|| row.guard.as_ref().map(|guard| guard.span))
                .unwrap_or(Span::DUMMY),
        });
        Ok(())
    }

    fn finish(
        self,
        resolver: &impl PatternResolver<TypeHandle>,
    ) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError> {
        let undefined = self.prematch.undefined_pins(&self.pinned);
        if !undefined.is_empty() {
            return Err(PatternDispatchError::SourcePattern(SourcePatternError::UndefinedPins(
                undefined,
            )));
        }
        let matrix = self.builder.build().map_err(PatternDispatchError::MatrixBuild)?;
        assert_eq!(
            matrix.outcomes.len(),
            self.outcomes.len(),
            "source pattern production creates one payload per matrix outcome"
        );
        assert!(
            matrix
                .outcomes
                .iter()
                .enumerate()
                .all(|(index, outcome)| outcome.id.0 as usize == index),
            "the temporary matrix records outcomes in OutcomeId order"
        );
        let pinned_inputs = self.pinned.iter().map(|pin| pin.input).collect::<Vec<_>>();
        // A guard question rides a carrier subject, so only its leaves say
        // which inputs the guard demands.
        let guard_leaves = self.guards.iter().map(PatternGuardExpr::leaves).collect::<Vec<_>>();
        let inputs = PlanInputs {
            // The DECLARED input count, not the matrix's subject count: a plan
            // that declares no inputs still mints one subject to carry guards.
            count: self.input_count,
            pinned: &pinned_inputs,
            guard_leaves: &guard_leaves,
            literal_blind: &|ty| resolver.is_literal_blind(ty),
        };
        #[cfg(test)]
        let source_matrix = matrix.clone();
        let graph = compile_dispatch_matrix(matrix, inputs)
            .map_err(PatternDispatchError::Compile)?
            .graph;
        let proven_tuple_arities = (0..self.input_count)
            .map(|ordinal| graph.proven_input_arity(ordinal as u32))
            .collect();
        Ok(PatternDispatchPlan {
            graph,
            #[cfg(test)]
            source_matrix,
            input_count: self.input_count,
            outcomes: self.outcomes,
            guards: self.guards,
            pinned: self.pinned,
            prepared_keys: self.prepared_keys,
            last_resort: self.last_resort,
            proven_tuple_arities,
        })
    }

    fn append_pattern(
        &mut self,
        pattern: &Pattern,
        span: Span,
        subject: &PatternSubjectRef,
        questions: &mut Vec<RegionQuestion<TypeHandle>>,
        bindings: &mut Vec<PatternDispatchBinding>,
        resolver: &mut impl PatternResolver<TypeHandle>,
    ) -> Result<(), SourcePatternError> {
        match pattern {
            Pattern::Wildcard => {}
            Pattern::Var(name) => self.bind(name, span, subject, bindings)?,
            Pattern::Both(left, right) => {
                self.append_pattern(&left.node, left.span, subject, questions, bindings, resolver)?;
                self.append_pattern(&right.node, right.span, subject, questions, bindings, resolver)?;
            }
            Pattern::Pinned(name) => {
                let pinned = *self
                    .pinned_by_name
                    .get(name)
                    .ok_or_else(|| SourcePatternError::UnknownPinned(name.to_string()))?;
                let subject = self.subject_id(subject)?;
                questions.push(RegionQuestion::equality(subject, ComparisonValue::Pinned(pinned)));
            }
            Pattern::Int(value) => self.const_question(subject, GroundValue::Int(*value), questions)?,
            Pattern::Float(value) => self.const_question(subject, GroundValue::Float(value.to_bits()), questions)?,
            Pattern::Binary(bytes) => {
                self.const_question(subject, GroundValue::Utf8Binary(bytes.clone()), questions)?
            }
            Pattern::Atom(name) => self.const_question(subject, GroundValue::Atom(name.clone()), questions)?,
            Pattern::Bool(value) => self.const_question(subject, GroundValue::Bool(*value), questions)?,
            Pattern::Nil => self.const_question(subject, GroundValue::Nil, questions)?,
            Pattern::Tuple(fields) => {
                let subject_id = self.subject_id(subject)?;
                let mut field_subjects = Vec::with_capacity(fields.len());
                for (index, field) in fields.iter().enumerate() {
                    let field_subject = PatternSubjectRef::TupleField {
                        tuple: Box::new(subject.clone()),
                        index: index as u32,
                    };
                    let field_id = self.subject_id(&field_subject)?;
                    field_subjects.push((field_subject, field_id, field));
                }
                questions.push(RegionQuestion::tuple_arity(
                    subject_id,
                    fields.len() as u32,
                    field_subjects.iter().map(|(_, field_id, _)| *field_id),
                ));
                for (field_subject, _, field) in field_subjects {
                    self.append_pattern(&field.node, field.span, &field_subject, questions, bindings, resolver)?;
                }
            }
            Pattern::List(elems, tail) => {
                self.append_list_pattern(elems, tail.as_deref(), subject, questions, bindings, resolver)?;
            }
            Pattern::Map(entries) => {
                let subject_id = self.subject_id(subject)?;
                questions.push(RegionQuestion::new(RegionPredicate::new(subject_id, Region::MapKind)));
                for (key_pat, val_pat) in entries {
                    let key = self.map_key(&key_pat.node)?;
                    self.prepare_heap_key(&key);
                    let value_subject = PatternSubjectRef::MapValue {
                        map: Box::new(subject.clone()),
                        key: key.clone(),
                    };
                    let value_id = self.subject_id(&value_subject)?;
                    questions.push(RegionQuestion::map_key_present(subject_id, key, value_id));
                    self.append_pattern(
                        &val_pat.node,
                        val_pat.span,
                        &value_subject,
                        questions,
                        bindings,
                        resolver,
                    )?;
                }
            }
            Pattern::Struct { module, fields } => {
                let ty = resolver.struct_type(module, span)?;
                let source = self.subject_id(subject)?;
                let mut question = RegionQuestion::type_region(source, ty);
                let mut projected_fields = Vec::with_capacity(fields.len());
                for (field, value) in fields {
                    let projected = PatternSubjectRef::StructField {
                        record: Box::new(subject.clone()),
                        field: field.clone(),
                    };
                    let result = self.subject_id(&projected)?;
                    question.match_evidence.projections.push(result);
                    projected_fields.push((projected, value));
                }
                questions.push(question);
                for (projected, value) in projected_fields {
                    self.append_pattern(&value.node, value.span, &projected, questions, bindings, resolver)?;
                }
            }
            Pattern::Bitstring(fields) => {
                let question = self.bitstring_question(subject, fields)?;
                let Region::Bitstring(shape) = &question.predicate.region else {
                    unreachable!();
                };
                let field_subjects = shape.fields.clone();
                questions.push(question);
                for (field_subject, field) in field_subjects.into_iter().zip(fields) {
                    self.append_pattern(
                        &field.value.node,
                        field.value.span,
                        &PatternSubjectRef::Subject(field_subject),
                        questions,
                        bindings,
                        resolver,
                    )?;
                }
            }
        }
        Ok(())
    }

    fn append_list_pattern(
        &mut self,
        elems: &[Spanned<Pattern>],
        tail: Option<&Spanned<Pattern>>,
        subject: &PatternSubjectRef,
        questions: &mut Vec<RegionQuestion<TypeHandle>>,
        bindings: &mut Vec<PatternDispatchBinding>,
        resolver: &mut impl PatternResolver<TypeHandle>,
    ) -> Result<(), SourcePatternError> {
        if elems.is_empty() {
            if let Some(tail) = tail {
                return self.append_pattern(&tail.node, tail.span, subject, questions, bindings, resolver);
            }
            let subject_id = self.subject_id(subject)?;
            questions.push(RegionQuestion::list_empty(subject_id));
            return Ok(());
        }
        let subject_id = self.subject_id(subject)?;
        let head_subject = PatternSubjectRef::ListHead(Box::new(subject.clone()));
        let tail_subject = PatternSubjectRef::ListTail(Box::new(subject.clone()));
        let head_id = self.subject_id(&head_subject)?;
        let tail_id = self.subject_id(&tail_subject)?;
        questions.push(RegionQuestion::list_cons(subject_id, head_id, tail_id));
        self.append_pattern(
            &elems[0].node,
            elems[0].span,
            &head_subject,
            questions,
            bindings,
            resolver,
        )?;
        if elems.len() == 1 {
            if let Some(tail) = tail {
                self.append_pattern(&tail.node, tail.span, &tail_subject, questions, bindings, resolver)
            } else {
                questions.push(RegionQuestion::list_empty(tail_id));
                Ok(())
            }
        } else {
            self.append_list_pattern(&elems[1..], tail, &tail_subject, questions, bindings, resolver)
        }
    }

    fn bitstring_question(
        &mut self,
        subject: &PatternSubjectRef,
        fields: &[crate::ast::BitField<Spanned<Pattern>>],
    ) -> Result<RegionQuestion<TypeHandle>, SourcePatternError> {
        let subject_id = self.subject_id(subject)?;
        let mut binding_subjects: HashMap<Var, SubjectId> = HashMap::new();
        let mut projections = Vec::new();
        let mut shapes = Vec::new();
        for (index, field) in fields.iter().enumerate() {
            let size = match &field.spec.size {
                None => None,
                Some(BitSize::Literal(value)) => Some(BitstringFieldSize::Literal(*value)),
                Some(BitSize::Var(name)) => Some(match binding_subjects.get(name).copied() {
                    Some(subject) => BitstringFieldSize::Binding(subject),
                    // A size name no earlier field of this bitstring binds is a
                    // pin: it names a binding that existed before the pattern
                    // began.
                    None => BitstringFieldSize::Pinned(self.pin_for_name(name, field.value.span)),
                }),
                Some(BitSize::ByteSizeOf(name)) => Some(BitstringFieldSize::PinnedByteSize(
                    self.pin_for_name(name, field.value.span),
                )),
            };
            let extraction = super::BitstringExtraction {
                previous: shapes.last().copied(),
                spec: BitstringFieldShape {
                    kind: bitstring_field_kind(field.spec.ty),
                    size,
                    endian: bitstring_endian(field.spec.endian),
                    signed: field.spec.signed,
                    unit: field.spec.unit,
                },
                is_last: index + 1 == fields.len(),
            };
            let kind = ProjectionKind::BitstringField(extraction);
            let field_id = self.project(subject_id, kind)?;
            projections.push(field_id);
            let direct_bindings = direct_bitfield_bindings(&field.value.node);
            for name in &direct_bindings {
                binding_subjects.insert(name.clone(), field_id);
            }
            shapes.push(field_id);
        }
        let predicate = RegionPredicate::new(
            subject_id,
            Region::Bitstring(BitstringShape {
                fields: shapes,
                require_done: true,
            }),
        );
        let mut match_evidence = EdgeEvidence::from_proof(predicate.clone(), super::ProofSense::Holds);
        match_evidence.projections = projections;
        Ok(RegionQuestion {
            predicate: predicate.clone(),
            match_evidence,
            miss_evidence: EdgeEvidence::from_proof(predicate, super::ProofSense::DoesNotHold),
        })
    }

    fn const_question(
        &mut self,
        subject: &PatternSubjectRef,
        value: GroundValue,
        questions: &mut Vec<RegionQuestion<TypeHandle>>,
    ) -> Result<(), SourcePatternError> {
        let subject = self.subject_id(subject)?;
        questions.push(RegionQuestion::equality(subject, ComparisonValue::Const(value)));
        Ok(())
    }

    fn bind(
        &mut self,
        name: &Var,
        span: Span,
        subject: &PatternSubjectRef,
        bindings: &mut Vec<PatternDispatchBinding>,
    ) -> Result<(), SourcePatternError> {
        let source = self.subject_id(subject)?;
        bindings.push(PatternDispatchBinding {
            name: name.clone(),
            source,
            span,
        });
        Ok(())
    }

    /// A pin for a name the pattern does not bind, created on first use and
    /// resolved against the rows' prematch like every other pin.
    fn pin_for_name(&mut self, name: &Var, span: Span) -> PinnedValueId {
        if let Some(id) = self.pinned_by_name.get(name) {
            return *id;
        }
        let id = PinnedValueId(self.pinned.len() as u32);
        self.pinned.push(PatternPinnedInput {
            name: name.clone(),
            input: self.prematch.input_for(name),
            span,
            kind: PinnedKind::Variable,
        });
        self.pinned_by_name.insert(name.clone(), id);
        id
    }

    fn subject_id(&mut self, subject: &PatternSubjectRef) -> Result<SubjectId, SourcePatternError> {
        if let Some(id) = self.subjects.get(subject).copied() {
            return Ok(id);
        }
        let id = match subject {
            PatternSubjectRef::Input(_) => return Err(SourcePatternError::UnknownSubject(subject.clone())),
            PatternSubjectRef::TupleField { tuple, index } => {
                let source = self.subject_id(tuple)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::TupleField(*index))
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::StructField { record, field } => {
                let source = self.subject_id(record)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::StructField(field.clone()))
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::ListHead(list) => {
                let source = self.subject_id(list)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::ListHead)
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::ListTail(list) => {
                let source = self.subject_id(list)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::ListTail)
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::MapValue { map, key } => {
                let source = self.subject_id(map)?;
                self.builder
                    .add_projected_subject(source, ProjectionKind::MapValue { key: key.clone() })
                    .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?
            }
            PatternSubjectRef::Subject(id) => *id,
        };
        self.subjects.insert(subject.clone(), id);
        Ok(id)
    }

    fn project(&mut self, source: SubjectId, kind: ProjectionKind) -> Result<SubjectId, SourcePatternError> {
        let key = (source, kind);
        if let Some(id) = self.projections.get(&key) {
            return Ok(*id);
        }
        let id = self
            .builder
            .add_projected_subject(source, key.1.clone())
            .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?;
        self.projections.insert(key, id);
        Ok(id)
    }

    fn map_key(&mut self, pattern: &Pattern) -> Result<GroundValue, SourcePatternError> {
        match pattern {
            Pattern::Int(value) => Ok(GroundValue::Int(*value)),
            Pattern::Float(value) => Ok(GroundValue::Float(value.to_bits())),
            Pattern::Binary(bytes) => Ok(GroundValue::Utf8Binary(bytes.clone())),
            Pattern::Atom(name) => Ok(GroundValue::Atom(name.clone())),
            Pattern::Bool(value) => Ok(GroundValue::Bool(*value)),
            Pattern::Nil => Ok(GroundValue::Nil),
            _ => Err(SourcePatternError::UnsupportedMapKey),
        }
    }

    fn prepare_heap_key(&mut self, key: &GroundValue) {
        if !matches!(
            key,
            GroundValue::Float(_) | GroundValue::Atom(_) | GroundValue::Utf8Binary(_)
        ) {
            return;
        }
        intern_prepared_key(&mut self.prepared_keys, key);
    }
}

/// The conjuncts of a guard, left to right. Only a top-level `and` splits:
/// under `or` or `not` a conjunct cannot be asked on its own.
fn and_chain(guard: &Spanned<Expr>) -> Vec<&Spanned<Expr>> {
    match &guard.node {
        Expr::BinOp(crate::ast::BinOp::And, lhs, rhs) => {
            let mut chain = and_chain(lhs);
            chain.extend(and_chain(rhs));
            chain
        }
        _ => vec![guard],
    }
}

/// The type questions a conjunct amounts to: it calls a type predicate and
/// hands it only variables its row binds. Anything else stays a guard.
fn type_test_of<F, TypeHandle>(
    conjunct: &Spanned<Expr>,
    bound: &HashMap<Var, SubjectId>,
    resolver: &mut F,
) -> Result<Option<Vec<(SubjectId, TypeHandle)>>, SourcePatternError>
where
    F: PatternResolver<TypeHandle>,
    TypeHandle: Clone,
{
    let Expr::Call(target, args) = &conjunct.node else {
        return Ok(None);
    };
    let Some(callee) = crate::ast::Callee::for_call(&target.node, args.len()) else {
        return Ok(None);
    };
    let subjects = args
        .iter()
        .map(|arg| match &arg.node {
            Expr::Var(name) => bound.get(name).copied(),
            _ => None,
        })
        .collect::<Option<Vec<_>>>();
    let Some(subjects) = subjects else {
        return Ok(None);
    };
    let Some(GuardCallee::Helper(helper)) = resolver.guard_call(&callee, args.len())? else {
        return Ok(None);
    };
    Ok(helper.type_predicate.as_ref().map(|asked| {
        asked
            .iter()
            .map(|(argument, ty)| (subjects[*argument as usize], ty.clone()))
            .collect()
    }))
}

fn intern_prepared_key(keys: &mut Vec<GroundValue>, key: &GroundValue) -> PreparedKeyId {
    let index = keys.iter().position(|prepared| prepared == key).unwrap_or_else(|| {
        keys.push(key.clone());
        keys.len() - 1
    });
    PreparedKeyId(index as u32)
}

fn validate_source_rows<TypeHandle>(patterns: &SourcePatternRows<TypeHandle>) -> Result<(), SourcePatternError> {
    for row in &patterns.rows {
        let actual = row.patterns.len();
        if actual != patterns.input_count {
            return Err(SourcePatternError::RowPatternArity {
                expected: patterns.input_count,
                actual,
                body_id: row.body_id,
            });
        }
    }
    for pair in patterns.rows.windows(2) {
        let previous = pair[0].body_id;
        let current = pair[1].body_id;
        if previous >= current {
            return Err(SourcePatternError::NonMonotonicBodyId { previous, current });
        }
    }
    Ok(())
}

fn bitstring_field_kind(kind: BitType) -> BitstringFieldKind {
    match kind {
        BitType::Integer => BitstringFieldKind::Integer,
        BitType::Float => BitstringFieldKind::Float,
        BitType::Binary => BitstringFieldKind::Binary,
        BitType::Bits => BitstringFieldKind::Bits,
        BitType::Utf8 => BitstringFieldKind::Utf8,
        BitType::Utf16 => BitstringFieldKind::Utf16,
        BitType::Utf32 => BitstringFieldKind::Utf32,
    }
}

fn bitstring_endian(endian: Endian) -> BitstringEndian {
    match endian {
        Endian::Big => BitstringEndian::Big,
        Endian::Little => BitstringEndian::Little,
        Endian::Native => BitstringEndian::Native,
    }
}

#[cfg(test)]
#[path = "pattern_test.rs"]
mod pattern_test;
