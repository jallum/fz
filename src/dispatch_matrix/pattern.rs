use self::source::{collect_pinned_names, direct_bitfield_bindings};
use super::{
    BitstringEndian, BitstringFieldKind, BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue,
    DispatchCompileError, DispatchGraph, DispatchMatrix, DispatchMatrixBuilder, DispatchMatrixError, EdgeEvidence,
    GroundValue, GuardId, GuardLeaf, OutcomeId, OutcomeMultiplicity, PinnedValueId, PlanInputs, PreparedKeyId,
    ProjectionKind, Region, RegionPredicate, RegionQuestion, SubjectId, compile_dispatch_matrix,
    demand::DispatchDemand,
};
use crate::ast::{BitSize, BitType, Endian, Expr, Pattern, Spanned};
use crate::function_surface::CallableSurface;
use crate::source::Span;
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) mod source;
pub(crate) use source::{PatternBodyId, PatternRow, SourcePatternError, SourcePatternRows};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchPlan<TypeHandle> {
    pub(crate) matrix: DispatchMatrix<TypeHandle>,
    pub(crate) graph: DispatchGraph<TypeHandle>,
    pub(crate) input_count: usize,
    pub(crate) outcomes: Vec<PatternDispatchOutcome>,
    pub(crate) guards: Vec<PatternGuardExpr<TypeHandle>>,
    pub(crate) pinned: Vec<PatternPinnedInput>,
    pub(crate) prepared_keys: Vec<GroundValue>,
}

impl<TypeHandle> PatternDispatchPlan<TypeHandle> {
    pub(crate) fn outcome(&self, id: OutcomeId) -> Option<&PatternDispatchOutcome> {
        self.outcomes.iter().find(|entry| entry.outcome == id)
    }

    /// The body a winning outcome names. Every outcome the graph can reach is
    /// one this plan carries, so a decision always has a body.
    pub(crate) fn body_id(&self, outcome: OutcomeId) -> PatternBodyId {
        self.outcome(outcome).expect("a winning outcome names a body").body_id
    }

    pub(crate) fn subject(&self, id: SubjectId) -> &super::SubjectSource {
        &self.matrix.subjects[id.0 as usize].source
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

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternDispatchPlan<MappedHandle> {
        PatternDispatchPlan {
            matrix: self.matrix.map_type_handle(map),
            graph: self.graph.map_type_handle(map),
            input_count: self.input_count,
            outcomes: self.outcomes.clone(),
            guards: self.guards.iter().map(|guard| guard.map_type_handle(map)).collect(),
            pinned: self.pinned.clone(),
            prepared_keys: self.prepared_keys.clone(),
        }
    }
}

/// A name a pattern reaches for but does not bind. Its value was bound before
/// the pattern began: `input` names the plan input that delivers that binding
/// when the rows carry a prematch, and is `None` when the lowerer resolves the
/// name in the scope enclosing the match instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternPinnedInput {
    pub(crate) name: String,
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
    pub(crate) outcome: OutcomeId,
    pub(crate) body_id: PatternBodyId,
    pub(crate) bindings: Vec<PatternDispatchBinding>,
    pub(crate) span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternDispatchBinding {
    pub(crate) name: String,
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

    fn guard_call(
        &mut self,
        callee: &crate::ast::Callee,
        arity: usize,
    ) -> Result<Option<Arc<PatternGuardDispatch<TypeHandle>>>, SourcePatternError>;
}

impl<TypeHandle, F> PatternResolver<TypeHandle> for F
where
    F: FnMut(&crate::ast::Callee, usize) -> Result<Option<Arc<PatternGuardDispatch<TypeHandle>>>, SourcePatternError>,
{
    fn struct_type(
        &mut self,
        module: &crate::ast::ModuleTarget,
        _span: Span,
    ) -> Result<TypeHandle, SourcePatternError> {
        Err(SourcePatternError::UnresolvedStruct(module.clone()))
    }

    fn guard_call(
        &mut self,
        callee: &crate::ast::Callee,
        arity: usize,
    ) -> Result<Option<Arc<PatternGuardDispatch<TypeHandle>>>, SourcePatternError> {
        self(callee, arity)
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
            PatternGuardExpr::Const(_) => {}
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
        }
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternGuardExpr<MappedHandle> {
        match self {
            PatternGuardExpr::Const(value) => PatternGuardExpr::Const(value.clone()),
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
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PatternGuardDispatch<TypeHandle> {
    pub(crate) plan: Box<PatternDispatchPlan<TypeHandle>>,
    pub(crate) bodies: Vec<PatternGuardExpr<TypeHandle>>,
}

impl<TypeHandle> PatternGuardDispatch<TypeHandle> {
    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> PatternGuardDispatch<MappedHandle> {
        PatternGuardDispatch {
            plan: Box::new(self.plan.map_type_handle(map)),
            bodies: self.bodies.iter().map(|body| body.map_type_handle(map)).collect(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PatternGuardUnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PatternGuardBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
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

pub(crate) fn guard_dispatch_from_surface<F, TypeHandle>(
    surface: &impl CallableSurface,
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
    let source_patterns = SourcePatternRows::entry(
        arity,
        surface
            .clauses()
            .iter()
            .enumerate()
            .map(|(i, clause)| PatternRow {
                patterns: clause.params.clone(),
                preconditions: Vec::new(),
                guard: clause.guard.clone(),
                body_id: i as PatternBodyId,
            })
            .collect(),
        Vec::new(),
    );
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
    })
}

/// Builds one guard expression from its source form.
fn guard_expr_from_ast<F, TypeHandle>(
    expr: &Expr,
    bindings: &HashMap<String, SubjectId>,
    pinned_by_name: &HashMap<String, PinnedValueId>,
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
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                PatternGuardExpr::Subject(*subject)
            } else if let Some(pinned) = pinned_by_name.get(name) {
                PatternGuardExpr::Pinned(*pinned)
            } else {
                return Err(SourcePatternError::UnknownGuardVar(name.clone()));
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
        Expr::UnOp(crate::ast::UnOp::Neg, arg) => PatternGuardExpr::Unary {
            op: PatternGuardUnaryOp::Neg,
            expr: Box::new(guard_expr_from_ast(
                &arg.node,
                bindings,
                pinned_by_name,
                prepared_keys,
                resolver,
            )?),
        },
        Expr::BinOp(op, lhs, rhs) => PatternGuardExpr::Binary {
            op: match op {
                crate::ast::BinOp::Add => PatternGuardBinOp::Add,
                crate::ast::BinOp::Sub => PatternGuardBinOp::Sub,
                crate::ast::BinOp::Mul => PatternGuardBinOp::Mul,
                crate::ast::BinOp::Div => PatternGuardBinOp::Div,
                crate::ast::BinOp::Rem => PatternGuardBinOp::Rem,
                crate::ast::BinOp::Eq => PatternGuardBinOp::Eq,
                crate::ast::BinOp::Neq => PatternGuardBinOp::Neq,
                crate::ast::BinOp::Lt => PatternGuardBinOp::Lt,
                crate::ast::BinOp::LtEq => PatternGuardBinOp::LtEq,
                crate::ast::BinOp::Gt => PatternGuardBinOp::Gt,
                crate::ast::BinOp::GtEq => PatternGuardBinOp::GtEq,
                crate::ast::BinOp::And => PatternGuardBinOp::And,
                crate::ast::BinOp::Or => PatternGuardBinOp::Or,
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
            let arity = args.len();
            let Some(callee) = crate::ast::Callee::for_call(&target.node, arity) else {
                return Err(SourcePatternError::UnsupportedGuardExpr);
            };
            let args = args
                .iter()
                .map(|arg| guard_expr_from_ast(&arg.node, bindings, pinned_by_name, prepared_keys, resolver))
                .collect::<Result<Vec<_>, _>>()?;
            let dispatch = resolver
                .guard_call(&callee, arity)?
                .ok_or(SourcePatternError::UnsupportedGuardExpr)?;
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
        _ => return Err(SourcePatternError::UnsupportedGuardExpr),
    })
}

pub(crate) fn pattern_dispatch_from_source<TypeHandle: Clone + PartialEq + Eq>(
    patterns: SourcePatternRows<TypeHandle>,
) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError> {
    let mut resolver = |_callee: &crate::ast::Callee,
                        _arity: usize|
     -> Result<Option<Arc<PatternGuardDispatch<TypeHandle>>>, SourcePatternError> { Ok(None) };
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
    producer.finish()
}

struct PatternDispatchProducer<TypeHandle> {
    builder: DispatchMatrixBuilder<TypeHandle>,
    input_count: usize,
    prematch: source::Prematch,
    subjects: HashMap<PatternSubjectRef, SubjectId>,
    guard_subject: SubjectId,
    pinned: Vec<PatternPinnedInput>,
    pinned_by_name: HashMap<String, PinnedValueId>,
    prepared_keys: Vec<GroundValue>,
    outcomes: Vec<PatternDispatchOutcome>,
    guards: Vec<PatternGuardExpr<TypeHandle>>,
    projections: HashMap<(SubjectId, ProjectionKind), SubjectId>,
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
            let mut bound = HashMap::new();
            for binding in &bindings {
                bound.insert(binding.name.clone(), binding.source);
            }
            let guard_expr = guard_expr_from_ast(
                &guard.node,
                &bound,
                &self.pinned_by_name,
                &mut self.prepared_keys,
                resolver,
            )?;
            let guard_id = GuardId(self.guards.len() as u32);
            self.guards.push(guard_expr);
            questions.push(RegionQuestion::new(RegionPredicate::new(
                self.guard_subject,
                Region::Guard(guard_id),
            )));
        }
        let outcome = self.builder.add_outcome(OutcomeMultiplicity::Unique);
        self.builder
            .add_arm_questions(questions, EdgeEvidence::empty(), outcome)
            .map_err(|err| SourcePatternError::DispatchMatrix(format!("{err:?}")))?;
        self.outcomes.push(PatternDispatchOutcome {
            outcome,
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

    fn finish(self) -> Result<PatternDispatchPlan<TypeHandle>, PatternDispatchError> {
        let undefined = self.prematch.undefined_pins(&self.pinned);
        if !undefined.is_empty() {
            return Err(PatternDispatchError::SourcePattern(SourcePatternError::UndefinedPins(
                undefined,
            )));
        }
        let matrix = self.builder.build().map_err(PatternDispatchError::MatrixBuild)?;
        let pinned_inputs = self.pinned.iter().map(|pin| pin.input).collect::<Vec<_>>();
        // A guard question rides a carrier subject, so only its leaves say
        // which inputs the guard demands.
        let guard_leaves = self.guards.iter().map(PatternGuardExpr::leaves).collect::<Vec<_>>();
        let inputs = PlanInputs {
            // The DECLARED input count, not the matrix's subject count: a plan
            // that declares no inputs still mints one subject to carry guards.
            count: self.input_count,
            subjects: &matrix.subjects,
            pinned: &pinned_inputs,
            guard_leaves: &guard_leaves,
        };
        let graph = compile_dispatch_matrix(&matrix, inputs)
            .map_err(PatternDispatchError::Compile)?
            .graph;
        Ok(PatternDispatchPlan {
            matrix,
            graph,
            input_count: self.input_count,
            outcomes: self.outcomes,
            guards: self.guards,
            pinned: self.pinned,
            prepared_keys: self.prepared_keys,
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
            Pattern::As(name, inner) => {
                self.bind(name, span, subject, bindings)?;
                self.append_pattern(&inner.node, inner.span, subject, questions, bindings, resolver)?;
            }
            Pattern::Pinned(name) => {
                let pinned = *self
                    .pinned_by_name
                    .get(name)
                    .ok_or_else(|| SourcePatternError::UnknownPinned(name.clone()))?;
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
        let mut binding_subjects = HashMap::new();
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
        name: &str,
        span: Span,
        subject: &PatternSubjectRef,
        bindings: &mut Vec<PatternDispatchBinding>,
    ) -> Result<(), SourcePatternError> {
        let source = self.subject_id(subject)?;
        bindings.push(PatternDispatchBinding {
            name: name.to_string(),
            source,
            span,
        });
        Ok(())
    }

    /// A pin for a name the pattern does not bind, created on first use and
    /// resolved against the rows' prematch like every other pin.
    fn pin_for_name(&mut self, name: &str, span: Span) -> PinnedValueId {
        if let Some(id) = self.pinned_by_name.get(name) {
            return *id;
        }
        let id = PinnedValueId(self.pinned.len() as u32);
        self.pinned.push(PatternPinnedInput {
            name: name.to_string(),
            input: self.prematch.input_for(name),
            span,
            kind: PinnedKind::Variable,
        });
        self.pinned_by_name.insert(name.to_string(), id);
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
