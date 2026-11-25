use self::source::{collect_pinned_names, direct_bitfield_bindings};
#[cfg(test)]
use super::DispatchMatrix;
use super::{
    BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchCompileError, DispatchGraph,
    DispatchMatrixBuilder, DispatchMatrixError, EdgeEvidence, GraphNodeId, GroundValue, GuardId, GuardLeaf, LiveEdges,
    OutcomeId, OutcomeMultiplicity, PinnedValueId, PlanInputs, PreparedKeyId, ProjectedProperty, ProjectionKind,
    Region, RegionPredicate, RegionQuestion, SubjectId, compile_dispatch_matrix, demand::DispatchDemand,
};
use crate::ast::{Expr, Pattern, PatternBitSize, Spanned, Var};
use crate::fast_hash::HashMap;
use crate::function_surface::CallableSurface;
use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};
use crate::source::Span;
use std::sync::Arc;

pub(crate) mod last_resort;
pub(crate) mod roots;
pub(crate) mod source;
pub(crate) mod unfold;
pub(crate) use last_resort::{FieldTerm, LastResort, RaisedField, ReasonTerm, atom_name};
pub(crate) use roots::OutcomeRoots;
pub(crate) use source::{PatternBodyId, PatternRow, SourcePatternError, SourcePatternRows};
use unfold::{Alternatives, ClauseFacts, Conjunction, GuardFacts};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchPlan<TypeHandle> {
    pub(crate) graph: DispatchGraph<TypeHandle>,
    #[cfg(test)]
    pub(crate) source_matrix: DispatchMatrix<TypeHandle>,
    pub(crate) input_count: usize,
    /// Shared by every plan narrowed from this one: narrowing keeps outcome ids.
    pub(crate) outcomes: Arc<[PatternDispatchOutcome]>,
    pub(crate) guards: Vec<PatternGuardExpr<TypeHandle>>,
    pub(crate) pinned: Arc<[PatternPinnedInput]>,
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

    /// The ordinal of the input `subject` is, when it is one rather than a
    /// projection of one.
    pub(crate) fn subject_input(&self, subject: SubjectId) -> Option<usize> {
        match self.subject(subject) {
            super::SubjectSource::Input { ordinal } => Some(*ordinal as usize),
            super::SubjectSource::Projection(_) => None,
        }
    }

    /// The outcome that selects source body `body`: a row has one outcome.
    /// Outcomes are made in row order and rows carry strictly increasing body
    /// ids, so the outcomes are sorted by body id even when the plan was made
    /// from a subset of a function's rows.
    pub(crate) fn outcome_of_body(&self, body: PatternBodyId) -> Option<&PatternDispatchOutcome> {
        self.outcomes
            .binary_search_by_key(&body, |outcome| outcome.body_id)
            .ok()
            .map(|index| &self.outcomes[index])
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
    /// keeps, and every bitstring test `rest_whole` names has its `binary` rest
    /// read as proven whole bytes; `None` when neither changes a thing. Subject
    /// ids, outcome ids, guards and pins are the plan's own, so everything that
    /// names them reads the trimmed plan unchanged.
    pub(crate) fn trimmed(
        &self,
        live: &impl Fn(GraphNodeId) -> LiveEdges,
        rest_whole: &impl Fn(GraphNodeId) -> bool,
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
            rest_whole,
        )?;
        Some(Self {
            graph,
            #[cfg(test)]
            source_matrix: self.source_matrix.clone(),
            input_count: self.input_count,
            outcomes: Arc::clone(&self.outcomes),
            guards: self.guards.clone(),
            pinned: Arc::clone(&self.pinned),
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
            outcomes: Arc::clone(&self.outcomes),
            guards: self.guards.iter().map(|guard| guard.map_type_handle(map)).collect(),
            pinned: Arc::clone(&self.pinned),
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
        key: ComparisonValue,
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

    /// Whether a literal has the type, or `None` when the literal's type is
    /// not one the resolver can name.
    fn ground_has_type(&mut self, value: &GroundValue, ty: &TypeHandle) -> Option<bool>;

    /// The region that holds exactly where `region` does not, when one can be
    /// written: a type test over everything the tested type leaves out.
    fn complement(&mut self, region: &Region<TypeHandle>) -> Option<Region<TypeHandle>>;
}

/// What a call in a guard reaches: a helper whose clauses are reified into
/// their own plan, an extern, which has no clauses and is called as it is, or
/// a raise, which names no function and only aborts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GuardCallee<TypeHandle> {
    Helper(Arc<PatternGuardDispatch<TypeHandle>>),
    Extern(Arc<GuardExtern>),
    Raise,
}

impl<TypeHandle> GuardCallee<TypeHandle> {
    /// Whether a call can only abort: the extern returns `none`, or the
    /// helper has bodies and every one of them is a failing node.
    fn always_fails(&self) -> bool {
        match self {
            GuardCallee::Raise => true,
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
/// guard evaluators can carry: an integer, a float, a reference word, or, for
/// an `fz` extern, a `binary`, which crosses as its tagged word. A `C` extern's
/// `binary` is a byte pointer with no length, which no evaluator carries. The
/// return is one of those or a boolean, which the guard reads as `true` or
/// `false`. A return of `none` is the call that fails the guard, and
/// so is the failure a checked return declares: either way the clause does not
/// match.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GuardExtern {
    pub(crate) abi: ExternAbi,
    pub(crate) symbol: String,
    pub(crate) params: Vec<ExternTy>,
    pub(crate) ret: ExternReturn,
    /// The one property of its argument the declaration says this extern
    /// reads and nothing else.
    pub(crate) projects: Option<ProjectedProperty>,
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
        if let Some(param) = params.iter().find(|ty| {
            !matches!(
                ty,
                ExternTy::I64
                    | ExternTy::Opaque(_)
                    | ExternTy::F64
                    | ExternTy::Any
                    | ExternTy::StoredValue
                    | ExternTy::BinaryCursor
            ) && !(**ty == ExternTy::Binary && abi == ExternAbi::Fz)
        }) {
            return Err(refuse(format!(
                "parameter class {param:?} is neither a number nor a reference word"
            )));
        }
        let carried = match &ret {
            ExternReturn::Scalar(lane) | ExternReturn::Checked(lane, _) => {
                matches!(
                    lane,
                    ExternTy::I64
                        | ExternTy::Opaque(_)
                        | ExternTy::F64
                        | ExternTy::Any
                        | ExternTy::Bool
                        | ExternTy::Never
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
            projects: None,
        })
    }

    /// This extern, declared to read `property` of its argument.
    pub(crate) fn projecting(mut self, property: Option<ProjectedProperty>) -> Self {
        self.projects = property;
        self
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

    /// A bare closure resolver has no types to subtract, so no region has a
    /// complement.
    fn complement(&mut self, _region: &Region<TypeHandle>) -> Option<Region<TypeHandle>> {
        None
    }

    fn ground_has_type(&mut self, _value: &GroundValue, _ty: &TypeHandle) -> Option<bool> {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum PatternGuardExpr<TypeHandle> {
    Const(GroundValue),
    /// The empty list, `[]`: a value no `GroundValue` names, because a ground
    /// value is a scalar or a binary and the empty list is a list. Every
    /// evaluator builds it the way a body's `[]` is built.
    EmptyList,
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
    /// make the call; one that returns `none` fails the guard instead.
    Extern {
        extern_fn: Arc<GuardExtern>,
        args: Vec<PatternGuardExpr<TypeHandle>>,
    },
    /// A call that can only abort the process: an extern returning `none`,
    /// or a helper every body of which is itself this node. In a guard the
    /// abort is the guard's failure, so the node carries no arguments and no
    /// evaluator builds any.
    Fails,
}

impl<TypeHandle> PatternGuardExpr<TypeHandle> {
    /// Every value this expression reads: the subjects and pins that reach it.
    /// A nested helper call contributes only what its argument expressions
    /// read, because the helper's own plan is closed over its own input space.
    pub(crate) fn leaves(&self) -> Vec<GuardLeaf> {
        let mut leaves = Vec::new();
        self.collect_leaves(&mut leaves);
        leaves
    }

    fn collect_leaves(&self, leaves: &mut Vec<GuardLeaf>) {
        match self {
            PatternGuardExpr::Const(_) | PatternGuardExpr::EmptyList | PatternGuardExpr::Fails => {}
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
            PatternGuardExpr::EmptyList => PatternGuardExpr::EmptyList,
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
    /// The clauses as facts, when a call can be unfolded into its caller's
    /// matrix: the helper has no bitstring pattern, whose extraction names
    /// subjects of its own.
    pub(crate) facts: Option<GuardFacts<TypeHandle>>,
}

/// The subjects the bodies of a guard helper read when an outcome wins.
pub(crate) fn guard_body_subjects<TypeHandle>(bodies: &[PatternGuardExpr<TypeHandle>]) -> Vec<SubjectId> {
    bodies
        .iter()
        .flat_map(PatternGuardExpr::leaves)
        .filter_map(|leaf| match leaf {
            GuardLeaf::Subject(subject) => Some(subject),
            GuardLeaf::Pinned(_) => None,
        })
        .collect()
}

impl<TypeHandle> PatternGuardDispatch<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternGuardDispatch<MappedHandle> {
        PatternGuardDispatch {
            plan: Box::new(self.plan.map_type_handle(map)),
            bodies: self.bodies.iter().map(|body| body.map_type_handle(map)).collect(),
            facts: self.facts.as_ref().map(|facts| facts.map_type_handle(map)),
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

    // A helper is an ordinary function, entered with nothing bound before its
    // patterns, so a pin in one of its heads names a binding that never
    // existed and its own plan is where that is found.
    let source_patterns = SourcePatternRows::entry(arity, rows, Vec::new());
    let clause_bodies = surface.clauses().iter().map(|clause| &clause.body).collect::<Vec<_>>();
    let (mut plan, facts) =
        pattern_dispatch_with_facts(&source_patterns, &clause_bodies, resolver).map_err(|err| match err {
            PatternDispatchError::SourcePattern(err) => err,
            other => SourcePatternError::DispatchMatrix(format!("{other:?}")),
        })?;

    // The plan above carries no pin, because a helper's rows have nothing
    // bound before them. So a name in a helper body is either one its own head
    // bound or one that was never bound at all, and lowering the body says
    // which.
    let pinned_by_name = HashMap::default();

    let mut bodies = Vec::with_capacity(surface.clauses().len());
    for clause in surface.clauses() {
        let outcome = plan
            .outcome_of_body(bodies.len() as PatternBodyId)
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
        facts,
    })
}

/// Builds one guard expression from its source form.
pub(super) fn guard_expr_from_ast<F, TypeHandle>(
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
        Expr::List(items, None) if items.is_empty() => PatternGuardExpr::EmptyList,
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
                crate::ast::BinOp::Cons
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
        GuardCallee::Raise => PatternGuardExpr::Fails,
    })
}

pub(crate) fn pattern_dispatch_from_source<TypeHandle: Clone + PartialEq + Eq>(
    patterns: SourcePatternRows<TypeHandle>,
) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError> {
    let mut resolver = |_callee: &crate::ast::Callee,
                        _arity: usize|
     -> Result<Option<GuardCallee<TypeHandle>>, SourcePatternError> { Ok(None) };
    pattern_dispatch_from_source_with_resolver(&patterns, &mut resolver)
}

pub(crate) fn pattern_dispatch_from_source_with_resolver<F, TypeHandle>(
    patterns: &SourcePatternRows<TypeHandle>,
    resolver: &mut F,
) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError>
where
    F: PatternResolver<TypeHandle>,
    TypeHandle: Clone + PartialEq + Eq,
{
    pattern_dispatch_from_rows(
        patterns.input_count,
        &patterns.prematch,
        patterns.last_resort.as_ref(),
        patterns.rows.iter(),
        resolver,
    )
}

/// A dispatch plan over `rows`, which need not be contiguous in the source
/// rows they were taken from.
pub(crate) fn pattern_dispatch_from_rows<'a, F, TypeHandle>(
    input_count: usize,
    prematch: &source::Prematch,
    last_resort: Option<&LastResort>,
    rows: impl Iterator<Item = &'a PatternRow<TypeHandle>> + Clone,
    resolver: &mut F,
) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError>
where
    F: PatternResolver<TypeHandle>,
    TypeHandle: Clone + PartialEq + Eq + 'a,
{
    let mut producer = PatternDispatchProducer::new(input_count, prematch, last_resort, rows.clone(), false)
        .map_err(PatternDispatchError::SourcePattern)?;
    for row in rows {
        producer
            .add_row(row, None, resolver)
            .map_err(PatternDispatchError::SourcePattern)?;
    }
    producer.finish(&*resolver).map(|(plan, _)| plan)
}

/// A guard helper's plan, and its clauses as facts a caller can unfold. The
/// clause bodies are read beside the rows, in clause order.
fn pattern_dispatch_with_facts<F, TypeHandle>(
    patterns: &SourcePatternRows<TypeHandle>,
    bodies: &[&Spanned<Expr>],
    resolver: &mut F,
) -> Result<(PatternDispatchPlan<TypeHandle>, Option<GuardFacts<TypeHandle>>), PatternDispatchError>
where
    F: PatternResolver<TypeHandle>,
    TypeHandle: Clone + PartialEq + Eq,
{
    let rows = patterns.rows.iter();
    let mut producer = PatternDispatchProducer::new(
        patterns.input_count,
        &patterns.prematch,
        patterns.last_resort.as_ref(),
        rows.clone(),
        true,
    )
    .map_err(PatternDispatchError::SourcePattern)?;
    for (row, body) in rows.zip(bodies) {
        producer
            .add_row(row, Some(body), resolver)
            .map_err(PatternDispatchError::SourcePattern)?;
    }
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
    /// Each row's facts, kept when the rows are a guard helper's clauses.
    clause_facts: Option<Vec<ClauseFacts<TypeHandle>>>,
}

impl<TypeHandle: Clone + PartialEq + Eq> PatternDispatchProducer<TypeHandle> {
    fn new<'a>(
        input_count: usize,
        prematch: &source::Prematch,
        last_resort: Option<&LastResort>,
        rows: impl Iterator<Item = &'a PatternRow<TypeHandle>> + Clone,
        keep_clause_facts: bool,
    ) -> Result<Self, SourcePatternError>
    where
        TypeHandle: 'a,
    {
        validate_source_rows(input_count, rows.clone())?;
        let mut builder = DispatchMatrixBuilder::typed();
        let mut subjects = HashMap::default();
        for ordinal in 0..input_count {
            let subject = builder.add_input_subject();
            let ordinal = ordinal as u32;
            subjects.insert(PatternSubjectRef::Input(ordinal), subject);
        }
        let guard_subject = subjects
            .get(&PatternSubjectRef::Input(0))
            .copied()
            .unwrap_or_else(|| builder.add_input_subject());
        let pinned = collect_pinned_names(prematch, rows);
        let pinned_by_name = pinned
            .iter()
            .enumerate()
            .map(|(index, pin)| (pin.name.clone(), PinnedValueId(index as u32)))
            .collect();
        Ok(Self {
            builder,
            input_count,
            prematch: prematch.clone(),
            subjects,
            guard_subject,
            pinned,
            pinned_by_name,
            prepared_keys: Vec::new(),
            outcomes: Vec::new(),
            guards: Vec::new(),
            projections: HashMap::default(),
            last_resort: last_resort.cloned(),
            clause_facts: keep_clause_facts.then(Vec::new),
        })
    }

    fn add_row<F>(
        &mut self,
        row: &PatternRow<TypeHandle>,
        body: Option<&Spanned<Expr>>,
        resolver: &mut F,
    ) -> Result<(), SourcePatternError>
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
        let mut bound: HashMap<Var, SubjectId> = HashMap::default();
        for binding in &bindings {
            bound.insert(binding.name.clone(), binding.source);
        }
        let ways = match &row.guard {
            Some(guard) => self.admit_guard(guard, &bound, resolver)?,
            None => Alternatives::single(Conjunction::default()),
        }
        .after(&questions);
        if self.clause_facts.is_some() {
            let body = body.ok_or(SourcePatternError::UnsupportedGuardExpr)?;
            let answer = self.admit_body(body, &bound, resolver)?;
            if let Some(facts) = self.clause_facts.as_mut() {
                facts.push(ClauseFacts {
                    matches: ways.clone(),
                    answer,
                });
            }
        }
        self.add_arms(ways)?;
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

    /// One arm for each way the clause can match, all to the clause's one
    /// outcome, in the order the ways are tried.
    fn add_arms(&mut self, ways: Alternatives<TypeHandle>) -> Result<(), SourcePatternError> {
        let multiplicity = match ways.ways() {
            [_] => OutcomeMultiplicity::Unique,
            _ => OutcomeMultiplicity::Shared,
        };
        let outcome = self.builder.add_outcome(multiplicity);
        for way in ways.ways().iter().cloned() {
            let mut questions = way.questions.clone();
            if let Some(guard_expr) = way.guard_expr() {
                let guard_id = GuardId(self.guards.len() as u32);
                self.guards.push(guard_expr);
                questions.push(RegionQuestion::new(RegionPredicate::new(
                    self.guard_subject,
                    Region::Guard(guard_id),
                )));
            }
            self.builder
                .add_arm_questions(questions, EdgeEvidence::empty(), outcome)
                .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?;
        }
        Ok(())
    }

    fn finish(
        self,
        resolver: &impl PatternResolver<TypeHandle>,
    ) -> Result<(PatternDispatchPlan<TypeHandle>, Option<GuardFacts<TypeHandle>>), PatternDispatchError> {
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
        let facts = self.clause_facts.map(|clauses| GuardFacts {
            subjects: matrix.subjects.clone(),
            clauses,
        });
        #[cfg(test)]
        let source_matrix = matrix.clone();
        let mut graph = compile_dispatch_matrix(matrix, inputs)
            .map_err(PatternDispatchError::Compile)?
            .graph;
        // Raising the last resort reads the inputs it shows, whether or not
        // any test did.
        let raised = self.last_resort.as_ref().map_or(0, LastResort::consumed_inputs);
        debug_assert!(
            raised <= self.input_count,
            "a last resort that consumes {raised} inputs was given a plan of {} inputs",
            self.input_count
        );
        for demand in graph.input_demand.iter_mut().take(raised) {
            demand.join_assign(DispatchDemand::Whole);
        }
        let proven_tuple_arities = (0..self.input_count)
            .map(|ordinal| graph.proven_input_arity(ordinal as u32))
            .collect();
        let plan = PatternDispatchPlan {
            graph,
            #[cfg(test)]
            source_matrix,
            input_count: self.input_count,
            outcomes: self.outcomes.into(),
            guards: self.guards,
            pinned: self.pinned.into(),
            prepared_keys: self.prepared_keys,
            last_resort: self.last_resort,
            proven_tuple_arities,
        };
        Ok((plan, facts.filter(GuardFacts::is_portable)))
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
            Pattern::Var(name) => self.bind(name, span, subject, questions, bindings)?,
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
                let fields = crate::ast::binary_literal_fields(bytes, span);
                self.append_bitstring_pattern(&fields, subject, questions, bindings, resolver)?
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
                self.append_bitstring_pattern(fields, subject, questions, bindings, resolver)?
            }
        }
        Ok(())
    }

    fn append_bitstring_pattern(
        &mut self,
        fields: &[crate::ast::PatternField],
        subject: &PatternSubjectRef,
        questions: &mut Vec<RegionQuestion<TypeHandle>>,
        bindings: &mut Vec<PatternDispatchBinding>,
        resolver: &mut impl PatternResolver<TypeHandle>,
    ) -> Result<(), SourcePatternError> {
        let question = self.bitstring_question(subject, fields, resolver)?;
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
        fields: &[crate::ast::PatternField],
        resolver: &mut impl PatternResolver<TypeHandle>,
    ) -> Result<RegionQuestion<TypeHandle>, SourcePatternError> {
        let subject_id = self.subject_id(subject)?;
        let mut binding_subjects: HashMap<Var, SubjectId> = HashMap::default();
        let mut projections = Vec::new();
        let mut shapes = Vec::new();
        for (index, field) in fields.iter().enumerate() {
            let size = match &field.spec.size {
                None => None,
                Some(PatternBitSize::Literal(value)) => Some(BitstringFieldSize::Literal(*value)),
                Some(PatternBitSize::Var(name)) => Some(match binding_subjects.get(name).copied() {
                    Some(subject) => BitstringFieldSize::Binding(subject),
                    // A size name no earlier field of this bitstring binds is a
                    // pin: it names a binding that existed before the pattern
                    // began.
                    None => BitstringFieldSize::Pinned(self.pin_for_name(name, field.value.span)),
                }),
                Some(PatternBitSize::ByteSizeOf(name)) => Some(BitstringFieldSize::PinnedByteSize(
                    self.pin_for_name(name, field.value.span),
                )),
                Some(PatternBitSize::Expr(expr)) => Some(self.size_guard(expr, &binding_subjects, resolver)?),
            };
            let extraction = super::BitstringExtraction {
                previous: shapes.last().copied(),
                spec: BitstringFieldShape {
                    kind: field.spec.ty,
                    size,
                    endian: field.spec.endian,
                    signed: field.spec.signed,
                    unit: field.spec.unit,
                    rest_proven_whole: false,
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
        questions: &mut Vec<RegionQuestion<TypeHandle>>,
        bindings: &mut Vec<PatternDispatchBinding>,
    ) -> Result<(), SourcePatternError> {
        let source = self.subject_id(subject)?;
        match bindings.iter().find(|binding| binding.name == *name) {
            Some(first) if first.source == source => {}
            Some(first) => questions.push(RegionQuestion::equality(source, ComparisonValue::Subject(first.source))),
            None => bindings.push(PatternDispatchBinding {
                name: name.clone(),
                source,
                span,
            }),
        }
        Ok(())
    }

    /// A size written as an expression is a guard expression whose value is the
    /// size: its names are earlier fields of the bitstring, or pins.
    fn size_guard(
        &mut self,
        expr: &Spanned<Expr>,
        earlier_fields: &HashMap<Var, SubjectId>,
        resolver: &mut impl PatternResolver<TypeHandle>,
    ) -> Result<BitstringFieldSize, SourcePatternError> {
        let earlier_names = earlier_fields.keys().cloned().collect();
        let mut captured = Vec::new();
        source::collect_guard_capture_names(expr, &earlier_names, &mut captured);
        for pin in captured {
            self.pin_for_name(&pin.name, pin.span);
        }
        let guard = guard_expr_from_ast(
            &expr.node,
            earlier_fields,
            &self.pinned_by_name,
            &mut self.prepared_keys,
            resolver,
        )?;
        let id = GuardId(self.guards.len() as u32);
        self.guards.push(guard);
        Ok(BitstringFieldSize::Guard(id))
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
                self.project(source, ProjectionKind::TupleField(*index))?
            }
            PatternSubjectRef::StructField { record, field } => {
                let source = self.subject_id(record)?;
                self.project(source, ProjectionKind::StructField(field.clone()))?
            }
            PatternSubjectRef::ListHead(list) => {
                let source = self.subject_id(list)?;
                self.project(source, ProjectionKind::ListHead)?
            }
            PatternSubjectRef::ListTail(list) => {
                let source = self.subject_id(list)?;
                self.project(source, ProjectionKind::ListTail)?
            }
            PatternSubjectRef::MapValue { map, key } => {
                let source = self.subject_id(map)?;
                self.project(source, ProjectionKind::MapValue { key: key.clone() })?
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

    /// The key a map pattern looks up: a literal, or the value a pinned
    /// variable holds.
    fn map_key(&mut self, pattern: &Pattern) -> Result<ComparisonValue, SourcePatternError> {
        let literal = match pattern {
            Pattern::Pinned(name) => {
                return self
                    .pinned_by_name
                    .get(name)
                    .map(|pinned| ComparisonValue::Pinned(*pinned))
                    .ok_or_else(|| SourcePatternError::UnknownPinned(name.to_string()));
            }
            Pattern::Int(value) => GroundValue::Int(*value),
            Pattern::Float(value) => GroundValue::Float(value.to_bits()),
            Pattern::Binary(bytes) => GroundValue::Utf8Binary(bytes.clone()),
            Pattern::Atom(name) => GroundValue::Atom(name.clone()),
            Pattern::Bool(value) => GroundValue::Bool(*value),
            Pattern::Nil => GroundValue::Nil,
            _ => return Err(SourcePatternError::UnsupportedMapKey),
        };
        self.prepare_heap_key(&literal);
        Ok(ComparisonValue::Const(literal))
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

/// The conjuncts of a guard, left to right. Only a top-level `and` splits;
/// an `or` is read as the sides it is made of when one is live, and a `not` as its complement.
pub(super) fn and_chain(guard: &Spanned<Expr>) -> Vec<&Spanned<Expr>> {
    match &guard.node {
        Expr::BinOp(crate::ast::BinOp::And, lhs, rhs) => {
            let mut chain = and_chain(lhs);
            chain.extend(and_chain(rhs));
            chain
        }
        _ => vec![guard],
    }
}

/// The sides of an `or`, left to right, however it nests.
pub(super) fn or_chain(expr: &Spanned<Expr>) -> Vec<&Spanned<Expr>> {
    match &expr.node {
        Expr::BinOp(crate::ast::BinOp::Or, lhs, rhs) => {
            let mut chain = or_chain(lhs);
            chain.extend(or_chain(rhs));
            chain
        }
        _ => vec![expr],
    }
}

pub(super) fn intern_prepared_key(keys: &mut Vec<GroundValue>, key: &GroundValue) -> PreparedKeyId {
    let index = keys.iter().position(|prepared| prepared == key).unwrap_or_else(|| {
        keys.push(key.clone());
        keys.len() - 1
    });
    PreparedKeyId(index as u32)
}

fn validate_source_rows<'a, TypeHandle: 'a>(
    input_count: usize,
    rows: impl Iterator<Item = &'a PatternRow<TypeHandle>> + Clone,
) -> Result<(), SourcePatternError> {
    for row in rows.clone() {
        let actual = row.patterns.len();
        if actual != input_count {
            return Err(SourcePatternError::RowPatternArity {
                expected: input_count,
                actual,
                body_id: row.body_id,
            });
        }
    }
    for (previous, current) in rows.clone().zip(rows.skip(1)).map(|(a, b)| (a.body_id, b.body_id)) {
        if previous >= current {
            return Err(SourcePatternError::NonMonotonicBodyId { previous, current });
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "pattern_test.rs"]
mod pattern_test;
