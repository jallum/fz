//! fz-ul4.23.5.2 — IR interpreter on LegacyTaggedWord, heap, and runtime substrate.
//!
//! Walks a `fz_ir::Module` directly, just like the legacy ir_interp.rs, but
//! uses the SAME value representation, heap, and runtime FFI as the JIT.
//! Spawn/send/receive call into the same runtime.rs scheduler. Print
//! renders through `fz_runtime::ir_runtime::fz_print_value`. Heap allocations
//! go through the current Process's Heap.
//!
//! Scope at .5.2: minimal for fixtures/add1/input.fz —
//!   Const::{Int, Atom, Nil, True, False}
//!   BinOp::Add  (Int + Int)
//!   Term::{Call, Return, Halt}
//!
//! Subsequent atoms expand the surface fixture by fixture:
//!   .5.3 scalars + print + other arith
//!   .5.4 closures + higher-order
//!   .5.5 pattern dispatch
//!   .5.6 modules
//!   .5.7 tail recursion (TCO)
//!   .5.8 spawn/send/receive

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use crate::types::Types;

use crate::fz_ir::{BinOp, Const, ExternId, ExternTy, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use fz_runtime::fz_value::LegacyTaggedWord;
use fz_runtime::process::Process;

fn legacy_tagged_word_from_fz_value(value: fz_runtime::fz_value::FzValue) -> LegacyTaggedWord {
    fz_runtime::fz_value::legacy_tagged_word_from_fz_value(value)
}

fn legacy_tagged_int_word(value: i64) -> LegacyTaggedWord {
    legacy_tagged_word_from_fz_value(fz_runtime::fz_value::FzValue::int(value))
}

fn legacy_tagged_atom_word(atom_id: u32) -> LegacyTaggedWord {
    legacy_tagged_word_from_fz_value(fz_runtime::fz_value::FzValue::atom(atom_id))
}

#[derive(Clone, Copy, Debug)]
enum InterpValue {
    Int(i64),
    Tagged(LegacyTaggedWord),
    Float(f64),
}

impl From<LegacyTaggedWord> for InterpValue {
    fn from(value: LegacyTaggedWord) -> Self {
        Self::Tagged(value)
    }
}

impl InterpValue {
    fn to_fz(self) -> Result<LegacyTaggedWord, String> {
        match self {
            InterpValue::Int(value) => {
                let encoded = legacy_tagged_int_word(value);
                if encoded.unbox_int() == Some(value) {
                    Ok(encoded)
                } else {
                    Err(format!(
                        "raw interpreter int {value} cannot be materialized as LegacyTaggedWord"
                    ))
                }
            }
            InterpValue::Tagged(value) => Ok(value),
            InterpValue::Float(_) => {
                Err("raw interpreter float cannot be materialized as LegacyTaggedWord".into())
            }
        }
    }

    fn tagged_bits(self) -> Result<u64, String> {
        Ok(self.to_fz()?.0)
    }

    fn mid_flight_strict_value(self) -> fz_runtime::fz_value::FzValue {
        use fz_runtime::fz_value::{FzValue, TAG_MASK};
        match self {
            InterpValue::Int(value) => FzValue::int(value),
            InterpValue::Tagged(value) => {
                let kind_tag = (value.0 & TAG_MASK) as u8;
                FzValue::decode_parts(value.0, kind_tag).expect("strict mid-flight tag")
            }
            InterpValue::Float(value) => FzValue::float(value),
        }
    }

    fn mid_flight_parts(self) -> (u64, u8) {
        let value = self.mid_flight_strict_value();
        (value.raw(), value.kind().tag())
    }

    fn from_mid_flight_parts(bits: u64, tag: u8) -> Self {
        match fz_runtime::fz_value::FzValue::decode_parts(bits, tag).map(|value| value.kind()) {
            Some(fz_runtime::fz_value::ValueKind::FLOAT) => Self::Float(f64::from_bits(bits)),
            Some(fz_runtime::fz_value::ValueKind::INT) => Self::Int(bits as i64),
            _ => Self::Tagged(LegacyTaggedWord(bits)),
        }
    }

    fn strict_slot_value(self) -> Result<fz_runtime::fz_value::FzValue, String> {
        use fz_runtime::fz_value::{FzValue, ValueKind};
        Ok(match self {
            InterpValue::Int(value) => FzValue::int(value),
            InterpValue::Tagged(value) => FzValue::from_parts(value.0, ValueKind::NULL),
            InterpValue::Float(value) => FzValue::float(value),
        })
    }

    fn slot_parts(self) -> Result<(u64, u8), String> {
        let value = self.strict_slot_value()?;
        Ok((value.raw(), value.kind().tag()))
    }

    fn mailbox_slot(self) -> fz_runtime::fz_value::MailboxSlot {
        use fz_runtime::fz_value::{FzValue, MailboxSlot};
        match self {
            InterpValue::Int(value) => MailboxSlot::from_strict(FzValue::int(value)),
            InterpValue::Tagged(value) => fz_runtime::process::current_process()
                .heap
                .mailbox_slot_from_legacy_tagged_word(value),
            InterpValue::Float(value) => MailboxSlot::from_strict(FzValue::float(value)),
        }
    }

    fn from_mailbox_slot(slot: fz_runtime::fz_value::MailboxSlot) -> Self {
        match slot.kind() {
            fz_runtime::fz_value::ValueKind::FLOAT => Self::Float(f64::from_bits(slot.value)),
            fz_runtime::fz_value::ValueKind::INT => Self::Int(slot.value as i64),
            _ => {
                let value = fz_runtime::process::current_process()
                    .heap
                    .legacy_tagged_word_from_mailbox_slot(slot);
                Self::Tagged(value)
            }
        }
    }

    fn as_float(self) -> Option<f64> {
        match self {
            InterpValue::Int(value) => Some(value as f64),
            InterpValue::Float(value) => Some(value),
            InterpValue::Tagged(value) => value.unbox_int().map(|n| n as f64),
        }
    }

    fn unbox_int(self) -> Option<i64> {
        match self {
            InterpValue::Int(value) => Some(value),
            InterpValue::Tagged(value) => value.unbox_int(),
            InterpValue::Float(_) => None,
        }
    }

    fn is_empty_list(self) -> bool {
        match self {
            InterpValue::Tagged(value) => value.is_empty_list(),
            InterpValue::Int(_) => false,
            InterpValue::Float(_) => false,
        }
    }

    fn is_truthy(self) -> bool {
        match self {
            InterpValue::Tagged(value) => !(value.is_false() || value.is_nil()),
            InterpValue::Int(_) => true,
            InterpValue::Float(_) => true,
        }
    }

    fn print(self) -> Result<(), String> {
        match self {
            InterpValue::Int(value) => {
                fz_runtime::fz_print_i64(value);
                Ok(())
            }
            InterpValue::Tagged(value) => {
                fz_runtime::ir_runtime::fz_print_value(value.0);
                Ok(())
            }
            InterpValue::Float(value) => {
                fz_runtime::fz_print_f64(value);
                Ok(())
            }
        }
    }

    fn render(self) -> String {
        match self {
            InterpValue::Int(value) => value.to_string(),
            InterpValue::Tagged(value) => fz_runtime::fz_value::debug::render(value.0),
            InterpValue::Float(value) => value.to_string(),
        }
    }
}

fn bitstring_like_ptr(bits: u64) -> Option<*mut u8> {
    if matches!(
        bits & fz_runtime::fz_value::TAG_MASK,
        fz_runtime::fz_value::TAG_BITSTRING | fz_runtime::fz_value::TAG_PROCBIN
    ) {
        Some(bits as *mut u8)
    } else {
        None
    }
}

// ===== Interp-internal scheduler (fz-ul4.23.5.8 / fz-sched.3) =====
//
// The interp owns its own task registry separate from runtime.rs::Runtime
// (which is wired into the JIT trampoline). They share the Process type,
// the LegacyTaggedWord rep, and the heap — so messages and mailboxes are byte-
// compatible between paths.
//
// Scheduling model (fz-sched.3): cooperative run-queue, BEAM-correct.
// Builtin::Spawn enqueues the child and returns immediately; the parent
// continues its own quantum. Term::Receive parks the task (InterpStep::Blocked)
// if the mailbox is empty; the scheduler records the resume state and moves on.
// interp_send flips a Blocked receiver to Ready, prepends the message to its
// resume args, and re-enqueues it. run_main drives the loop until the queue
// is empty.
//
// Limitation: Blocked propagates as an error through non-tail call sites
// (Term::Call / Term::CallClosure). In practice all fixture receive sites are
// in tail position inside spawned fns, so this doesn't matter yet.

use std::collections::VecDeque;

/// Returned by run_fn to signal either completion or a receive-park.
enum InterpStep {
    Done(InterpValue),
    /// Task parked on receive. `resume_fn(msg, cap_vals...)` is called when
    /// the message arrives. `after` is a chain of (fn_id, caps) continuations
    /// to call in order with each successive return value — built up when
    /// Blocked propagates through Term::Call frames.
    Blocked(FnId, Vec<InterpValue>, Vec<(FnId, Vec<InterpValue>)>),
    /// fz-yxs/fz-2v3 — task parked on a selective `receive do … end`. The
    /// park record snapshots every clause's pattern + body / guard FnId
    /// plus the pinned ^name and capture FzValues from the receive site
    /// so that `interp_send` can probe new messages without recreating
    /// any of that state.
    BlockedMatched(ParkRecord, Vec<(FnId, Vec<InterpValue>)>),
}

/// fz-yxs/fz-2v3 — interp park record for a selective receive.
/// `after` is consumed inline at park time (the `after 0` case fires
/// before we park; non-zero/`:infinity` is treated as "no timer" in the
/// interp since there's no wall clock — the real timer wiring lands
/// for JIT/AOT in B2 via F2). So this struct only stores what the
/// sender-side probe needs.
#[derive(Clone)]
struct ParkRecord {
    clauses: Vec<MatchedClause>,
    matcher: std::sync::Arc<crate::matcher::Matcher>,
    pinned: HashMap<String, InterpValue>,
    captures: Vec<InterpValue>,
}

#[derive(Clone)]
struct MatchedClause {
    bound_names: Vec<String>,
    guard: Option<FnId>,
    body: FnId,
}

/// Per-task resume state: fn to call, captures (no message), and after-chain.
type ResumeEntry = (FnId, Vec<InterpValue>, Vec<(FnId, Vec<InterpValue>)>);

thread_local! {
    static INTERP_TASKS: RefCell<HashMap<u32, Box<Process>>> =
        RefCell::new(HashMap::new());
    static INTERP_NEXT_PID: Cell<u32> = const { Cell::new(2) };
    static INTERP_SCHEMAS: RefCell<Option<std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>>> =
        const { RefCell::new(None) };
    /// fz-ul4.35 — per-run map from tuple arity to heap schema id.
    /// Populated lazily by Prim::MakeTuple via interp_tuple_schema_id; cleared
    /// at run_main / run_test_fn entry so each run starts fresh.
    static INTERP_TUPLE_SCHEMA_IDS: RefCell<HashMap<usize, u32>> =
        RefCell::new(HashMap::new());
    /// FIFO run-queue of pids ready to execute.
    static INTERP_RUN_QUEUE: RefCell<VecDeque<u32>> = const { RefCell::new(VecDeque::new()) };
    /// Per-task resume state: (resume_fn, cap_vals, after_chain).
    /// cap_vals holds captures only (no message); interp_send prepends the
    /// message. after_chain is the sequence of (fn_id, caps) continuations to
    /// invoke in order after resume_fn returns, passing each return value on.
    static INTERP_RESUME: RefCell<HashMap<u32, ResumeEntry>> =
        RefCell::new(HashMap::new());
    /// fz-yxs/fz-2v3 — selective-receive park records. Keyed by pid so
    /// that `interp_send` can probe an arriving message against the
    /// receiver's parked matcher without unwinding the scheduler.
    static INTERP_PARKED: RefCell<HashMap<u32, InterpParked>> =
        RefCell::new(HashMap::new());
}

/// fz-yxs/fz-2v3 — value type for `INTERP_PARKED`. Factored out so
/// the TLS entry doesn't trip clippy's "very complex type" lint.
type InterpParked = (ParkRecord, Vec<(FnId, Vec<InterpValue>)>);

/// fz-ul4.35 — get-or-register a heap schema for a tuple of `arity`,
/// matching the JIT codegen layout in src/ir_codegen.rs (Tuple{N}, N*8
/// payload bytes, N LegacyTaggedWord fields at offsets 0, 8, 16, ...).
fn interp_tuple_schema_id(arity: usize) -> u32 {
    INTERP_TUPLE_SCHEMA_IDS.with(|m| {
        if let Some(&id) = m.borrow().get(&arity) {
            return id;
        }
        use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
        let s = Schema {
            name: format!("Tuple{}", arity),
            size: (arity * 8) as u32,
            fields: (0..arity)
                .map(|i| FieldDescriptor {
                    offset: (i * 8) as u32,
                    kind: FieldKind::FzValue,
                })
                .collect(),
        };
        let registry = fz_runtime::process::current_process()
            .heap
            .schemas_registry();
        let id = registry.borrow_mut().register(s);
        m.borrow_mut().insert(arity, id);
        id
    })
}

#[derive(Default)]
struct MatcherExecState {
    values: HashMap<crate::matcher::SubjectRef, InterpValue>,
    bitstring_fields: HashMap<(crate::matcher::SubjectRef, u32), LegacyTaggedWord>,
}

fn interp_list_ptr(value: LegacyTaggedWord) -> Option<*mut u8> {
    let direct = fz_runtime::fz_value::list_addr_from_tagged(value.0);
    if let Some(p) = direct
        && !p.is_null()
    {
        return Some(p);
    }
    let from_raw_i64 = value
        .unbox_int()
        .map(|n| (n as u64).wrapping_shl(3) as *mut u8);
    from_raw_i64.filter(|p| {
        !p.is_null()
            && fz_runtime::process::current_process()
                .heap
                .contains_heap_addr(*p)
    })
}

fn interp_is_list_cons(value: LegacyTaggedWord) -> bool {
    interp_list_ptr(value).is_some()
}

fn interp_list_head(value: LegacyTaggedWord) -> Result<InterpValue, String> {
    if !interp_is_list_cons(value) {
        return Err(format!(
            "ListHead: subject is not a list cons ({:#x})",
            value.0
        ));
    }
    let p = interp_list_ptr(value).expect("checked list");
    let typed = unsafe { (*(p as *const fz_runtime::fz_value::ListCons)).head_typed() };
    Ok(interp_typed_value_to_value(typed))
}

fn interp_list_tail(value: LegacyTaggedWord) -> Result<LegacyTaggedWord, String> {
    if !interp_is_list_cons(value) {
        return Err(format!(
            "ListTail: subject is not a list cons ({:#x})",
            value.0
        ));
    }
    let p = interp_list_ptr(value).expect("checked list");
    Ok(LegacyTaggedWord(unsafe {
        (*(p as *const fz_runtime::fz_value::ListCons)).tail_bits()
    }))
}

fn execute_matcher(
    module: &Module,
    matcher: &crate::matcher::Matcher,
    root: InterpValue,
    pinned: &HashMap<String, InterpValue>,
) -> Option<(crate::matcher::BodyId, Vec<(String, InterpValue)>)> {
    let mut state = MatcherExecState::default();
    execute_matcher_node(module, matcher, matcher.root, &[root], pinned, &mut state)
}

fn execute_matcher_node(
    module: &Module,
    matcher: &crate::matcher::Matcher,
    node_id: crate::matcher::NodeId,
    inputs: &[InterpValue],
    pinned: &HashMap<String, InterpValue>,
    state: &mut MatcherExecState,
) -> Option<(crate::matcher::BodyId, Vec<(String, InterpValue)>)> {
    use crate::matcher::MatcherNode;
    match matcher.node(node_id)? {
        MatcherNode::Fail { .. } => None,
        MatcherNode::Leaf(leaf) => {
            let mut out = Vec::with_capacity(leaf.bindings.len());
            for binding in &leaf.bindings {
                let value = resolve_matcher_subject(
                    module,
                    matcher,
                    &binding.source,
                    inputs,
                    pinned,
                    state,
                )?;
                out.push((binding.name.clone(), value));
            }
            Some((leaf.body_id, out))
        }
        MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => {
            let value = resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)?;
            for (key, case_node) in cases {
                if matcher_switch_hit(module, value, kind, key) {
                    return execute_matcher_node(
                        module, matcher, *case_node, inputs, pinned, state,
                    );
                }
            }
            execute_matcher_node(module, matcher, *default, inputs, pinned, state)
        }
        MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => {
            let next = if matcher_test_hit(module, matcher, test, inputs, pinned, state) {
                *on_true
            } else {
                *on_false
            };
            execute_matcher_node(module, matcher, next, inputs, pinned, state)
        }
        MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let value = eval_matcher_guard(module, matcher, expr, inputs, pinned, state)?;
            let next = if value.is_false() || value.is_nil() {
                *on_false
            } else {
                *on_true
            };
            execute_matcher_node(module, matcher, next, inputs, pinned, state)
        }
    }
}

fn eval_matcher_guard(
    module: &Module,
    matcher: &crate::matcher::Matcher,
    expr: &crate::matcher::GuardExpr,
    inputs: &[InterpValue],
    pinned: &HashMap<String, InterpValue>,
    state: &MatcherExecState,
) -> Option<LegacyTaggedWord> {
    use crate::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    use fz_runtime::fz_value::{FALSE_BITS, TRUE_BITS};
    Some(match expr {
        GuardExpr::Const(c) => matcher_const_to_value(module, c)?,
        GuardExpr::Subject(subject) => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)?
                .to_fz()
                .ok()?
        }
        GuardExpr::Pinned(pinned_id) => {
            let p = matcher.pinned.get(pinned_id.0 as usize)?;
            if let Some(var) = p.var {
                return inputs.get(var.0 as usize).copied()?.to_fz().ok();
            }
            pinned.get(&p.name)?.to_fz().ok()?
        }
        GuardExpr::Unary { op, expr } => {
            let v = eval_matcher_guard(module, matcher, expr, inputs, pinned, state)?;
            match op {
                GuardUnaryOp::Not => {
                    if v.is_false() || v.is_nil() {
                        LegacyTaggedWord(TRUE_BITS)
                    } else {
                        LegacyTaggedWord(FALSE_BITS)
                    }
                }
                GuardUnaryOp::Neg => LegacyTaggedWord(((-guard_int(v)?) as u64) << 3 | 1),
            }
        }
        GuardExpr::Binary { op, lhs, rhs } => {
            let l = eval_matcher_guard(module, matcher, lhs, inputs, pinned, state)?;
            let short = match op {
                GuardBinOp::And if l.is_false() || l.is_nil() => Some(LegacyTaggedWord(FALSE_BITS)),
                GuardBinOp::Or if !(l.is_false() || l.is_nil()) => {
                    Some(LegacyTaggedWord(TRUE_BITS))
                }
                _ => None,
            };
            if let Some(v) = short {
                return Some(v);
            }
            let r = eval_matcher_guard(module, matcher, rhs, inputs, pinned, state)?;
            match op {
                GuardBinOp::Add => {
                    LegacyTaggedWord(((guard_int(l)? + guard_int(r)?) as u64) << 3 | 1)
                }
                GuardBinOp::Sub => {
                    LegacyTaggedWord(((guard_int(l)? - guard_int(r)?) as u64) << 3 | 1)
                }
                GuardBinOp::Mul => {
                    LegacyTaggedWord(((guard_int(l)? * guard_int(r)?) as u64) << 3 | 1)
                }
                GuardBinOp::Div => {
                    LegacyTaggedWord(((guard_int(l)? / guard_int(r)?) as u64) << 3 | 1)
                }
                GuardBinOp::Rem => {
                    LegacyTaggedWord(((guard_int(l)? % guard_int(r)?) as u64) << 3 | 1)
                }
                GuardBinOp::Eq => bool_value(l.0 == r.0),
                GuardBinOp::Neq => bool_value(l.0 != r.0),
                GuardBinOp::Lt => bool_value(guard_int(l)? < guard_int(r)?),
                GuardBinOp::LtEq => bool_value(guard_int(l)? <= guard_int(r)?),
                GuardBinOp::Gt => bool_value(guard_int(l)? > guard_int(r)?),
                GuardBinOp::GtEq => bool_value(guard_int(l)? >= guard_int(r)?),
                GuardBinOp::And | GuardBinOp::Or => bool_value(!(r.is_false() || r.is_nil())),
            }
        }
        GuardExpr::Dispatch {
            inputs: dispatch_inputs,
            dispatch,
        } => {
            let values = dispatch_inputs
                .iter()
                .map(|input| eval_matcher_guard(module, matcher, input, inputs, pinned, state))
                .collect::<Option<Vec<_>>>()?;
            let interp_values: Vec<InterpValue> = values.iter().copied().map(Into::into).collect();
            let mut dispatch_state = MatcherExecState::default();
            let (body_id, _) = execute_matcher_node(
                module,
                &dispatch.matcher,
                dispatch.matcher.root,
                &interp_values,
                pinned,
                &mut dispatch_state,
            )?;
            let body = dispatch.bodies.get(body_id as usize)?;
            eval_matcher_guard(
                module,
                &dispatch.matcher,
                body,
                &interp_values,
                pinned,
                &dispatch_state,
            )?
        }
    })
}

fn matcher_const_to_value(
    module: &Module,
    c: &crate::matcher::MatcherConst,
) -> Option<LegacyTaggedWord> {
    use crate::matcher::MatcherConst;
    use fz_runtime::fz_value::{FALSE_BITS, NIL_BITS, TRUE_BITS};
    match c {
        MatcherConst::Int(n) => Some(LegacyTaggedWord(((*n as u64) << 3) | 1)),
        MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| LegacyTaggedWord(((id as u64) << 3) | 2)),
        MatcherConst::Bool(true) => Some(LegacyTaggedWord(TRUE_BITS)),
        MatcherConst::Bool(false) => Some(LegacyTaggedWord(FALSE_BITS)),
        MatcherConst::Nil => Some(LegacyTaggedWord(NIL_BITS)),
        MatcherConst::EmptyList => {
            Some(LegacyTaggedWord(crate::ir_codegen::EMPTY_LIST_BITS as u64))
        }
        MatcherConst::FloatBits(_) | MatcherConst::Utf8Binary(_) | MatcherConst::PreparedKey(_) => {
            None
        }
    }
}

fn guard_int(v: LegacyTaggedWord) -> Option<i64> {
    v.unbox_int()
}

fn bool_value(b: bool) -> LegacyTaggedWord {
    if b {
        LegacyTaggedWord(fz_runtime::fz_value::TRUE_BITS)
    } else {
        LegacyTaggedWord(fz_runtime::fz_value::FALSE_BITS)
    }
}

fn resolve_matcher_subject(
    module: &Module,
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
    inputs: &[InterpValue],
    pinned: &HashMap<String, InterpValue>,
    state: &MatcherExecState,
) -> Option<InterpValue> {
    if let Some(value) = state.values.get(subject).copied() {
        return Some(value);
    }
    match subject {
        crate::matcher::SubjectRef::Input(id) => inputs.get(id.0 as usize).copied(),
        crate::matcher::SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_matcher_subject(module, matcher, tuple, inputs, pinned, state)?
                .to_fz()
                .ok()?;
            let p = fz_runtime::fz_value::struct_addr_from_tagged(parent.0)?;
            let off = 8 + (*index as usize) * 8;
            Some(unsafe { std::ptr::read(p.add(off) as *const LegacyTaggedWord) }.into())
        }
        crate::matcher::SubjectRef::ListHead(list) => {
            let parent = resolve_matcher_subject(module, matcher, list, inputs, pinned, state)?
                .to_fz()
                .ok()?;
            interp_list_head(parent).ok()
        }
        crate::matcher::SubjectRef::ListTail(list) => {
            let parent = resolve_matcher_subject(module, matcher, list, inputs, pinned, state)?
                .to_fz()
                .ok()?;
            interp_list_tail(parent).ok().map(Into::into)
        }
        crate::matcher::SubjectRef::MapValue { map, key } => {
            let map = resolve_matcher_subject(module, matcher, map, inputs, pinned, state)?
                .to_fz()
                .ok()?;
            matcher_map_lookup(matcher, module, map, key, pinned)
        }
        crate::matcher::SubjectRef::BitstringField { bitstring, index } => state
            .bitstring_fields
            .get(&((**bitstring).clone(), *index))
            .copied()
            .map(Into::into),
    }
}

fn matcher_test_hit(
    module: &Module,
    matcher: &crate::matcher::Matcher,
    test: &crate::matcher::MatcherTest,
    inputs: &[InterpValue],
    pinned: &HashMap<String, InterpValue>,
    state: &mut MatcherExecState,
) -> bool {
    match test {
        crate::matcher::MatcherTest::EqConst { subject, value } => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| matcher_const_eq(module, v, value))
        }
        crate::matcher::MatcherTest::EqPinned {
            subject,
            pinned: pin_id,
        } => {
            let Some(value) =
                resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(pin) = matcher.pinned.get(pin_id.0 as usize) else {
                return false;
            };
            if let Some(var) = pin.var {
                return inputs
                    .get(var.0 as usize)
                    .is_some_and(|want| interp_value_eq(*want, value).unwrap_or(false));
            }
            pinned
                .get(&pin.name)
                .is_some_and(|want| interp_value_eq(*want, value).unwrap_or(false))
        }
        crate::matcher::MatcherTest::TupleArity { subject, arity } => resolve_matcher_subject(
            module, matcher, subject, inputs, pinned, state,
        )
        .is_some_and(|v| {
            v.to_fz().ok().is_some_and(|v| {
                fz_runtime::fz_value::struct_addr_from_tagged(v.0).is_some_and(|p| {
                    (unsafe { fz_runtime::fz_value::struct_schema_id(p) })
                        == interp_tuple_schema_id(*arity as usize)
                })
            })
        }),
        crate::matcher::MatcherTest::ListCons { subject } => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| v.to_fz().ok().is_some_and(interp_is_list_cons))
        }
        crate::matcher::MatcherTest::MapKind { subject } => {
            resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
                .is_some_and(|v| v.to_fz().ok().is_some_and(is_map_value))
        }
        crate::matcher::MatcherTest::MapHasKey { subject, key } => {
            let Some(v) = resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            let Some(value) = v
                .to_fz()
                .ok()
                .and_then(|v| matcher_map_lookup(matcher, module, v, key, pinned))
            else {
                return false;
            };
            state
                .values
                .insert(crate::matcher::map_value_subject(subject, key), value);
            true
        }
        crate::matcher::MatcherTest::Bitstring { subject, fields } => {
            let Some(value) =
                resolve_matcher_subject(module, matcher, subject, inputs, pinned, state)
            else {
                return false;
            };
            value
                .to_fz()
                .ok()
                .is_some_and(|value| matcher_read_bitstring(subject, value, fields, state))
        }
        crate::matcher::MatcherTest::Type { .. } => true,
    }
}

fn matcher_switch_hit(
    module: &Module,
    val: InterpValue,
    kind: &crate::matcher::SwitchKind,
    key: &crate::matcher::SwitchKey,
) -> bool {
    use fz_runtime::fz_value::Tag;
    match (kind, key) {
        (crate::matcher::SwitchKind::Atom, crate::matcher::SwitchKey::AtomName(name)) => {
            val.to_fz().ok().is_some_and(|val| {
                val.tag() == Tag::Atom
                    && val.unbox_atom().is_some_and(|id| {
                        module
                            .atom_names
                            .iter()
                            .position(|n| n == name)
                            .is_some_and(|pos| pos as u32 == id)
                    })
            })
        }
        (crate::matcher::SwitchKind::Int, crate::matcher::SwitchKey::Int(n)) => {
            val.unbox_int() == Some(*n)
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(true)) => {
            val.to_fz().ok().is_some_and(|val| val.is_true())
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(false)) => {
            val.to_fz().ok().is_some_and(|val| val.is_false())
        }
        (crate::matcher::SwitchKind::Nil, crate::matcher::SwitchKey::Nil) => {
            val.to_fz().ok().is_some_and(|val| val.is_nil())
        }
        (crate::matcher::SwitchKind::TupleArity, crate::matcher::SwitchKey::Arity(arity)) => {
            val.to_fz().ok().is_some_and(|val| {
                fz_runtime::fz_value::struct_addr_from_tagged(val.0).is_some_and(|p| {
                    (unsafe { fz_runtime::fz_value::struct_schema_id(p) })
                        == interp_tuple_schema_id(*arity as usize)
                })
            })
        }
        (crate::matcher::SwitchKind::Float, crate::matcher::SwitchKey::FloatBits(bits)) => {
            matcher_const_eq(module, val, &crate::matcher::MatcherConst::FloatBits(*bits))
        }
        (crate::matcher::SwitchKind::Binary, crate::matcher::SwitchKey::Utf8Binary(bytes)) => {
            matcher_const_eq(
                module,
                val,
                &crate::matcher::MatcherConst::Utf8Binary(bytes.clone()),
            )
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Nil) => {
            val.to_fz().ok().is_some_and(|val| val.is_nil())
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::EmptyList) => {
            val.is_empty_list()
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Cons) => {
            val.to_fz().ok().is_some_and(interp_is_list_cons)
        }
        _ => false,
    }
}

fn matcher_const_eq(
    module: &Module,
    val: InterpValue,
    value: &crate::matcher::MatcherConst,
) -> bool {
    use fz_runtime::fz_value::Tag;
    match value {
        crate::matcher::MatcherConst::Int(n) => val.unbox_int() == Some(*n),
        crate::matcher::MatcherConst::FloatBits(bits) => {
            matches!(val, InterpValue::Float(f) if f.to_bits() == *bits)
        }
        crate::matcher::MatcherConst::AtomName(name) => val.to_fz().ok().is_some_and(|val| {
            val.tag() == Tag::Atom
                && val.unbox_atom().is_some_and(|id| {
                    module
                        .atom_names
                        .iter()
                        .position(|n| n == name)
                        .is_some_and(|pos| pos as u32 == id)
                })
        }),
        crate::matcher::MatcherConst::Bool(true) => {
            val.to_fz().ok().is_some_and(|val| val.is_true())
        }
        crate::matcher::MatcherConst::Bool(false) => {
            val.to_fz().ok().is_some_and(|val| val.is_false())
        }
        crate::matcher::MatcherConst::Nil => val.to_fz().ok().is_some_and(|val| val.is_nil()),
        crate::matcher::MatcherConst::EmptyList => val.is_empty_list(),
        crate::matcher::MatcherConst::Utf8Binary(bytes) => val.to_fz().ok().is_some_and(|val| {
            bitstring_like_ptr(val.0).is_some_and(|p| {
                if !unsafe { fz_runtime::procbin::is_bitstring_like(p) } {
                    return false;
                }
                let bit_len = unsafe { fz_runtime::procbin::bitstring_bit_len(p) };
                if bit_len != (bytes.len() as u64) * 8 {
                    return false;
                }
                let ptr = unsafe { fz_runtime::procbin::bitstring_byte_ptr(p) };
                let slice = unsafe { std::slice::from_raw_parts(ptr, bytes.len()) };
                slice == bytes.as_slice()
            })
        }),
        crate::matcher::MatcherConst::PreparedKey(_) => false,
    }
}

fn is_map_value(val: LegacyTaggedWord) -> bool {
    fz_runtime::ir_runtime::fz_map_is_map(val.0) != 0
}

fn interp_typed_key_category(value: fz_runtime::fz_value::TypedValue) -> u8 {
    use fz_runtime::fz_value::ValueKind;
    match value.kind {
        ValueKind::INT => 0,
        ValueKind::ATOM => 1,
        ValueKind::NULL => 2,
        kind if kind.is_heap() => 3,
        ValueKind::FLOAT => 4,
        _ => 5,
    }
}

fn interp_typed_key_cmp(
    a: fz_runtime::fz_value::TypedValue,
    b: fz_runtime::fz_value::TypedValue,
) -> std::cmp::Ordering {
    interp_typed_key_category(a)
        .cmp(&interp_typed_key_category(b))
        .then_with(|| a.kind.tag().cmp(&b.kind.tag()))
        .then_with(|| {
            if a.kind == fz_runtime::fz_value::ValueKind::INT {
                (a.raw as i64).cmp(&(b.raw as i64))
            } else {
                a.raw.cmp(&b.raw)
            }
        })
}

fn interp_typed_value_to_value(value: fz_runtime::fz_value::TypedValue) -> InterpValue {
    match value.kind {
        fz_runtime::fz_value::ValueKind::FLOAT => InterpValue::Float(f64::from_bits(value.raw)),
        fz_runtime::fz_value::ValueKind::INT => InterpValue::Int(value.raw as i64),
        _ => fz_runtime::process::current_process()
            .heap
            .legacy_tagged_word_from_typed(value)
            .into(),
    }
}

fn interp_typed_value_eq_bits(value: fz_runtime::fz_value::TypedValue) -> u64 {
    if let Some(bits) = value.tagged_heap_bits() {
        bits
    } else {
        fz_runtime::process::current_process()
            .heap
            .legacy_tagged_word_from_typed(value)
            .0
    }
}

fn interp_matcher_key_eq(
    a: fz_runtime::fz_value::TypedValue,
    b: fz_runtime::fz_value::TypedValue,
) -> bool {
    if a.kind.is_heap() || b.kind.is_heap() {
        let a_bits = interp_typed_value_eq_bits(a);
        let b_bits = interp_typed_value_eq_bits(b);
        LegacyTaggedWord(fz_runtime::ir_runtime::fz_value_eq(a_bits, b_bits)).is_true()
    } else {
        a.kind == b.kind && a.raw == b.raw
    }
}

fn interp_value_to_typed_key(
    value: InterpValue,
) -> Result<fz_runtime::fz_value::TypedValue, String> {
    use fz_runtime::fz_value::{TypedValue, ValueKind};
    Ok(match value {
        InterpValue::Int(value) => TypedValue::new(value as u64, ValueKind::INT),
        InterpValue::Float(value) => TypedValue::new(value.to_bits(), ValueKind::FLOAT),
        InterpValue::Tagged(value) => fz_runtime::process::current_process()
            .heap
            .typed_from_legacy_tagged_word(value),
    })
}

fn interp_current_heap_addr_for_kind(
    bits: u64,
    kind: fz_runtime::fz_value::ValueKind,
) -> Option<*mut u8> {
    fz_runtime::process::current_process()
        .heap
        .current_heap_addr_for_kind(bits, kind)
}

fn interp_current_heap_map_addr(bits: u64) -> Option<*mut u8> {
    interp_current_heap_addr_for_kind(bits, fz_runtime::fz_value::ValueKind::MAP)
}

fn interp_current_heap_resource_addr(bits: u64) -> Option<*mut u8> {
    interp_current_heap_addr_for_kind(bits, fz_runtime::fz_value::ValueKind::RESOURCE)
}

fn interp_map_entry_by_typed_key(
    p: *const u8,
    key: fz_runtime::fz_value::TypedValue,
) -> Option<fz_runtime::fz_value::TypedValue> {
    let count = unsafe { fz_runtime::fz_value::map_count(p) };
    for i in 0..count {
        let (entry_key, entry_value) = unsafe { fz_runtime::fz_value::map_entry(p, i) };
        if interp_typed_key_cmp(entry_key, key).is_eq() {
            return Some(entry_value);
        }
    }
    None
}

fn interp_map_entry_by_matcher_key(
    p: *const u8,
    key: fz_runtime::fz_value::TypedValue,
) -> Option<fz_runtime::fz_value::TypedValue> {
    let count = unsafe { fz_runtime::fz_value::map_count(p) };
    for i in 0..count {
        let (entry_key, entry_value) = unsafe { fz_runtime::fz_value::map_entry(p, i) };
        if interp_matcher_key_eq(entry_key, key) {
            return Some(entry_value);
        }
    }
    None
}

fn interp_map_get(map: LegacyTaggedWord, key: InterpValue) -> Result<Option<InterpValue>, String> {
    if let Some(p) = interp_current_heap_resource_addr(map.0) {
        let _ = key;
        let rs = unsafe { fz_runtime::resource::ResourceStub::from_raw(p) };
        return Ok(Some(LegacyTaggedWord(rs.payload()).into()));
    }
    let Some(p) = interp_current_heap_map_addr(map.0) else {
        let key_bits = key.tagged_bits().unwrap_or(0);
        return Ok(Some(
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_map_get(map.0, key_bits)).into(),
        ));
    };
    let key = interp_value_to_typed_key(key)?;
    Ok(interp_map_entry_by_typed_key(p, key).map(interp_typed_value_to_value))
}

fn matcher_map_lookup(
    matcher: &crate::matcher::Matcher,
    module: &Module,
    map: LegacyTaggedWord,
    key: &crate::matcher::MatcherConst,
    pinned: &HashMap<String, InterpValue>,
) -> Option<InterpValue> {
    let (key_bits, key_kind) = matcher_const_key_parts(matcher, module, key, pinned)?;
    if !is_map_value(map) {
        return None;
    }
    let key_kind = fz_runtime::fz_value::ValueKind::new(key_kind)?;
    let key = if key_kind == fz_runtime::fz_value::ValueKind::NULL {
        fz_runtime::process::current_process()
            .heap
            .typed_from_legacy_tagged_word(LegacyTaggedWord(key_bits))
    } else {
        fz_runtime::fz_value::TypedValue::new(key_bits, key_kind)
    };
    let p = interp_current_heap_map_addr(map.0)?;
    interp_map_entry_by_matcher_key(p, key).map(interp_typed_value_to_value)
}

fn matcher_const_key_parts(
    matcher: &crate::matcher::Matcher,
    module: &Module,
    key: &crate::matcher::MatcherConst,
    pinned: &HashMap<String, InterpValue>,
) -> Option<(u64, u8)> {
    use fz_runtime::fz_value::{FALSE_BITS, NIL_BITS, TRUE_BITS, ValueKind};
    match key {
        crate::matcher::MatcherConst::Int(n) => {
            Some(((((*n as u64) << 3) | 1), ValueKind::NULL.tag()))
        }
        crate::matcher::MatcherConst::FloatBits(bits) => Some((*bits, ValueKind::FLOAT.tag())),
        crate::matcher::MatcherConst::Bool(true) => Some((TRUE_BITS, ValueKind::NULL.tag())),
        crate::matcher::MatcherConst::Bool(false) => Some((FALSE_BITS, ValueKind::NULL.tag())),
        crate::matcher::MatcherConst::Nil => Some((NIL_BITS, ValueKind::NULL.tag())),
        crate::matcher::MatcherConst::AtomName(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| (((id as u64) << 3) | 2, ValueKind::NULL.tag())),
        crate::matcher::MatcherConst::PreparedKey(index) => matcher
            .prepared_keys
            .get(*index as usize)
            .and_then(|_| pinned.get(&crate::matcher::prepared_key_name(*index as usize)))
            .and_then(|value| value.slot_parts().ok()),
        _ => None,
    }
}

fn matcher_read_bitstring(
    subject: &crate::matcher::SubjectRef,
    value: LegacyTaggedWord,
    fields: &[crate::matcher::MatcherBitField],
    state: &mut MatcherExecState,
) -> bool {
    let Some(p) = bitstring_like_ptr(value.0) else {
        return false;
    };
    if !unsafe { fz_runtime::procbin::is_bitstring_like(p) } {
        return false;
    }
    let mut reader = LegacyTaggedWord(fz_runtime::ir_runtime::fz_bs_reader_init(value.0));
    let mut size_bindings: HashMap<String, InterpValue> = HashMap::new();
    for (index, field) in fields.iter().enumerate() {
        let Some((size_present, size_value)) = matcher_bit_size_value(&field.size, &size_bindings)
        else {
            return false;
        };
        let result = LegacyTaggedWord(fz_runtime::ir_runtime::fz_bs_read_field(
            reader.0,
            matcher_bit_type_tag(field.ty),
            size_present,
            size_value,
            field.unit.unwrap_or(default_matcher_bit_unit(field.ty)),
            matcher_endian_tag(field.endian),
            field.signed as u32,
            (index + 1 == fields.len()) as u32,
        ));
        let Some(rp) = fz_runtime::fz_value::struct_addr_from_tagged(result.0) else {
            return false;
        };
        let ok: LegacyTaggedWord = unsafe { std::ptr::read(rp.add(8) as *const LegacyTaggedWord) };
        if ok.is_false() || ok.is_nil() {
            return false;
        }
        let extracted: LegacyTaggedWord =
            unsafe { std::ptr::read(rp.add(16) as *const LegacyTaggedWord) };
        let next_reader: LegacyTaggedWord =
            unsafe { std::ptr::read(rp.add(24) as *const LegacyTaggedWord) };
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            size_bindings.insert(name.clone(), extracted.into());
        }
        reader = next_reader;
    }
    let Some(rp) = fz_runtime::fz_value::struct_addr_from_tagged(reader.0) else {
        return false;
    };
    let bit_len = LegacyTaggedWord(unsafe { std::ptr::read(rp.add(16) as *const u64) }).unbox_int();
    let pos = LegacyTaggedWord(unsafe { std::ptr::read(rp.add(24) as *const u64) }).unbox_int();
    bit_len == pos
}

fn matcher_bit_size_value(
    size: &Option<crate::matcher::MatcherBitSize>,
    bindings: &HashMap<String, InterpValue>,
) -> Option<(u32, u32)> {
    match size {
        None => Some((0, 0)),
        Some(crate::matcher::MatcherBitSize::Literal(n)) => Some((1, *n)),
        Some(crate::matcher::MatcherBitSize::BindingName(name)) => bindings
            .get(name)
            .and_then(|v| v.unbox_int())
            .map(|n| (1, n as u32)),
    }
}

fn matcher_bit_type_tag(ty: crate::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::matcher::MatcherBitType::Integer => 0,
        crate::matcher::MatcherBitType::Float => 1,
        crate::matcher::MatcherBitType::Binary => 2,
        crate::matcher::MatcherBitType::Bits => 3,
        crate::matcher::MatcherBitType::Utf8 => 4,
        crate::matcher::MatcherBitType::Utf16 => 5,
        crate::matcher::MatcherBitType::Utf32 => 6,
    }
}

fn matcher_endian_tag(endian: crate::matcher::MatcherEndian) -> u32 {
    match endian {
        crate::matcher::MatcherEndian::Big => 0,
        crate::matcher::MatcherEndian::Little => 1,
        crate::matcher::MatcherEndian::Native => 2,
    }
}

fn default_matcher_bit_unit(ty: crate::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::matcher::MatcherBitType::Integer
        | crate::matcher::MatcherBitType::Float
        | crate::matcher::MatcherBitType::Bits => 1,
        crate::matcher::MatcherBitType::Binary => 8,
        crate::matcher::MatcherBitType::Utf8
        | crate::matcher::MatcherBitType::Utf16
        | crate::matcher::MatcherBitType::Utf32 => 1,
    }
}

/// fz-yxs/fz-2v3 — try matching the message against each clause's
/// pattern + guard in order; first match wins. Returns the matched
/// clause index plus the bindings list (in source order, aligned with
/// `MatchedClause::bound_names`) on success.
///
/// Receive probes execute the cached AST-free Matcher lowered at the
/// receive site; misses return None without compiling or walking AST.
fn try_match_clauses<T: Types<Ty = crate::types::Ty>>(
    _t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    clauses: &[MatchedClause],
    matcher: &crate::matcher::Matcher,
    msg: InterpValue,
    pinned: &HashMap<String, InterpValue>,
    _captures: &[InterpValue],
) -> Result<Option<(usize, Vec<InterpValue>)>, String> {
    let matched = execute_matcher(module, matcher, msg, pinned);
    let Some((body_id, binds)) = matched else {
        tel.execute(
            &["fz", "interp", "receive", "probe_miss"],
            &crate::measurements! {
                clause_count: clauses.len() as u64
            },
            &crate::telemetry::Metadata::new(),
        );
        return Ok(None);
    };
    let i = body_id as usize;
    let c = &clauses[i];
    // Align with declared bound_names order. The matrix's bindings list
    // is keyed by source name and reflects pattern-walk order; the
    // explicit reorder protects against any future drift.
    let mut bound_vals: Vec<InterpValue> = Vec::with_capacity(c.bound_names.len());
    for name in &c.bound_names {
        let Some((_, v)) = binds.iter().rev().find(|(n, _)| n == name) else {
            return Err(format!(
                "try_match_clauses: bound name `{}` missing from pattern walk",
                name
            ));
        };
        bound_vals.push(*v);
    }
    tel.execute(
        &["fz", "interp", "receive", "probe_hit"],
        &crate::measurements! {
            clause_idx: i as u64,
            bound_count: bound_vals.len() as u64,
            clause_count: clauses.len() as u64
        },
        &crate::telemetry::Metadata::new(),
    );
    debug_assert!(
        c.guard.is_none(),
        "receive guards execute inside the cached Matcher"
    );
    Ok(Some((i, bound_vals)))
}

fn interp_register_task(pid: u32, process: Box<Process>) -> *mut Process {
    INTERP_TASKS.with(|t| {
        let mut tasks = t.borrow_mut();
        tasks.insert(pid, process);
        tasks
            .get_mut(&pid)
            .map(|b| b.as_mut() as *mut Process)
            .unwrap()
    })
}

fn interp_next_pid() -> u32 {
    INTERP_NEXT_PID.with(|n| {
        let p = n.get();
        n.set(p + 1);
        p
    })
}

fn interp_send<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    receiver_pid: u32,
    msg: InterpValue,
) -> Result<(), String> {
    use fz_runtime::process::ProcessState;
    let sender_heap = &fz_runtime::process::current_process().heap as *const fz_runtime::heap::Heap;
    // fz-yxs/fz-2v3 — sender-side probe for selective receive. If the
    // receiver is parked on a Term::ReceiveMatched, run the parked
    // matcher inline against the new message; on a hit, set up the
    // matched clause's body as the receiver's next resume and wake it
    // without touching the mailbox.
    let parked = INTERP_PARKED.with(|p| p.borrow_mut().remove(&receiver_pid));
    if let Some((park, after_chain)) = parked {
        let hit = try_match_clauses(
            t,
            module,
            tel,
            &park.clauses,
            &park.matcher,
            msg,
            &park.pinned,
            &park.captures,
        )?;
        match hit {
            Some((idx, bound_vals)) => {
                let body = park.clauses[idx].body;
                let mut args = bound_vals;
                args.extend(park.captures.iter().copied());
                INTERP_RESUME.with(|r| {
                    r.borrow_mut()
                        .insert(receiver_pid, (body, args, after_chain));
                });
                INTERP_TASKS.with(|t| {
                    if let Some(task) = t.borrow_mut().get_mut(&receiver_pid) {
                        task.state = ProcessState::Ready;
                    }
                });
                INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(receiver_pid));
                return Ok(());
            }
            None => {
                // Miss: park stays in place; message lands in mailbox.
                INTERP_PARKED.with(|p| {
                    p.borrow_mut().insert(receiver_pid, (park, after_chain));
                });
                let msg_slot = msg.mailbox_slot();
                INTERP_TASKS.with(|t| {
                    let mut tasks = t.borrow_mut();
                    if let Some(task) = tasks.get_mut(&receiver_pid) {
                        let mut forwarding = std::collections::HashMap::new();
                        let slot = fz_runtime::heap::deep_copy_mailbox_slot(
                            msg_slot,
                            unsafe { &*sender_heap },
                            &mut task.heap,
                            &mut forwarding,
                        );
                        task.mailbox.push_back(slot);
                    } else {
                        tel.event(
                            &["fz", "runtime", "send_to_unknown_pid"],
                            crate::metadata! { pid: receiver_pid as u64 },
                        );
                    }
                });
                return Ok(());
            }
        }
    }

    let was_blocked = INTERP_TASKS.with(|t| {
        let mut tasks = t.borrow_mut();
        match tasks.get_mut(&receiver_pid) {
            Some(task) => {
                let mut forwarding = std::collections::HashMap::new();
                let msg_slot = msg.mailbox_slot();
                let slot = fz_runtime::heap::deep_copy_mailbox_slot(
                    msg_slot,
                    unsafe { &*sender_heap },
                    &mut task.heap,
                    &mut forwarding,
                );
                if task.state == ProcessState::Blocked {
                    let copied_msg = InterpValue::from_mailbox_slot(slot);
                    INTERP_RESUME.with(|r| {
                        let mut resume = r.borrow_mut();
                        if let Some(entry) = resume.get_mut(&receiver_pid) {
                            entry.1.insert(0, copied_msg);
                        }
                    });
                    task.state = ProcessState::Ready;
                    true
                } else {
                    task.mailbox.push_back(slot);
                    false
                }
            }
            None => {
                tel.event(
                    &["fz", "runtime", "send_to_unknown_pid"],
                    crate::metadata! { pid: receiver_pid as u64 },
                );
                false
            }
        }
    });
    if was_blocked {
        INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(receiver_pid));
    }
    Ok(())
}

fn interp_reset_state() {
    INTERP_TASKS.with(|t| t.borrow_mut().clear());
    INTERP_NEXT_PID.with(|n| n.set(2));
    INTERP_RUN_QUEUE.with(|q| q.borrow_mut().clear());
    INTERP_RESUME.with(|r| r.borrow_mut().clear());
    INTERP_PARKED.with(|p| p.borrow_mut().clear());
    INTERP_TUPLE_SCHEMA_IDS.with(|m| m.borrow_mut().clear());
}

/// Run `module`'s `main` fn through the interpreter.
///
/// Drives a cooperative run-queue loop: main starts at pid=1, spawned tasks
/// are enqueued and run one quantum at a time in FIFO order. Tasks that block
/// on receive park until a send wakes them. Loop exits when the queue is empty.
pub fn run_main(tel: &dyn crate::telemetry::Telemetry, module: &Module) -> Result<i64, String> {
    use fz_runtime::process::ProcessState;
    let main_id = module.fn_by_name("main").ok_or("no `main/0` fn found")?.id;
    interp_reset_state();
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = {
        let mut reg = user_schemas.borrow_mut();
        let arity1 = reg.register(fz_runtime::heap::Schema::tuple_of_arity(1));
        let arity3 = reg.register(fz_runtime::heap::Schema::tuple_of_arity(3));
        INTERP_TUPLE_SCHEMA_IDS.with(|m| {
            let mut m = m.borrow_mut();
            m.insert(1, arity1);
            m.insert(3, arity3);
        });
        (arity1, arity3)
    };
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = Some(user_schemas.clone()));
    let mut main_process = Box::new(Process::new(user_schemas));
    main_process.pid = 1;
    main_process.atom_names = module.atom_names.clone();
    main_process.state = ProcessState::Ready;
    main_process.bs_tuple_arity1_schema = Some(bs_tuple_arity1_schema);
    main_process.bs_tuple_arity3_schema = Some(bs_tuple_arity3_schema);
    interp_register_task(1, main_process);
    INTERP_RESUME.with(|r| r.borrow_mut().insert(1, (main_id, vec![], vec![])));
    INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(1));
    let mut t = crate::types::ConcreteTypes;

    let mut halt_val = 0i64;
    'sched: while let Some(pid) = INTERP_RUN_QUEUE.with(|q| q.borrow_mut().pop_front()) {
        let (fn_id, args, mut after) = INTERP_RESUME
            .with(|r| r.borrow_mut().remove(&pid))
            .expect("pid in run_queue with no resume entry");
        let proc_ptr = INTERP_TASKS
            .with(|t| {
                t.borrow()
                    .get(&pid)
                    .map(|b| b.as_ref() as *const _ as *mut Process)
            })
            .expect("pid in run_queue with no process entry");
        unsafe { (*proc_ptr).state = ProcessState::Running };
        let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(proc_ptr));
        let mut step = run_fn(&mut t, module, tel, fn_id, args);
        // Process the after-chain: each Done value is threaded into the next fn.
        loop {
            match step {
                Ok(InterpStep::Done(val)) => {
                    if let Some((next_fn, next_caps)) = after.first().cloned() {
                        after.remove(0);
                        let mut next_args = vec![val];
                        next_args.extend(next_caps);
                        step = run_fn(&mut t, module, tel, next_fn, next_args);
                        // loop continues
                    } else {
                        // fz-4mk — shutdown drain: walk the MSO chain to
                        // enqueue every still-live resource's dtor, then
                        // dispatch each as a real fz call while the process
                        // is still alive (CURRENT_PROCESS is `proc_ptr`,
                        // heap is intact, scheduler can drive callbacks
                        // into externs the dtor body invokes).
                        unsafe {
                            fz_runtime::procbin::mso_drop_all_deferred(&mut (*proc_ptr).heap);
                        }
                        if let Err(e) = drain_pending_dtors_interp(&mut t, module, tel) {
                            tel.event(
                                &["fz", "runtime", "dtor_drain_failed"],
                                crate::metadata! { error: e },
                            );
                        }
                        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                        INTERP_TASKS.with(|t| {
                            if let Some(p) = t.borrow_mut().get_mut(&pid) {
                                p.state = ProcessState::Exited;
                            }
                        });
                        if pid == 1 {
                            halt_val = value_to_halt(val);
                        }
                        continue 'sched;
                    }
                }
                Ok(InterpStep::Blocked(resume_fn, cap_vals, mut new_after)) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    new_after.extend(after);
                    INTERP_TASKS.with(|t| {
                        if let Some(p) = t.borrow_mut().get_mut(&pid) {
                            p.state = ProcessState::Blocked;
                        }
                    });
                    INTERP_RESUME
                        .with(|r| r.borrow_mut().insert(pid, (resume_fn, cap_vals, new_after)));
                    continue 'sched;
                }
                // fz-yxs/fz-2v3 — park record + after-chain stashed under
                // INTERP_PARKED so the next interp_send can probe the
                // matcher against the arriving message without unwinding.
                Ok(InterpStep::BlockedMatched(park, mut new_after)) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    new_after.extend(after);
                    INTERP_TASKS.with(|t| {
                        if let Some(p) = t.borrow_mut().get_mut(&pid) {
                            p.state = ProcessState::Blocked;
                        }
                    });
                    INTERP_PARKED.with(|p| {
                        p.borrow_mut().insert(pid, (park, new_after));
                    });
                    continue 'sched;
                }
                Err(e) => {
                    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
                    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
                    return Err(e);
                }
            }
        }
    }

    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
    Ok(halt_val)
}

/// Run a single test fn (no args) through the interp on a fresh Process.
/// Used by `fz test` (src/test_runner.rs). Each test gets its own heap +
/// mailbox so state can't leak between tests in the same module.
///
/// Returns Ok(()) if the test completes without an assertion failure;
/// returns Err(msg) on any interp/runtime/assertion error.
pub fn run_test_fn(
    tel: &dyn crate::telemetry::Telemetry,
    module: &Module,
    fn_id: FnId,
) -> Result<(), String> {
    interp_reset_state();
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = Some(user_schemas.clone()));
    let mut task = Box::new(Process::new(user_schemas));
    task.pid = 1;
    task.atom_names = module.atom_names.clone();
    let task_ptr = interp_register_task(1, task);
    let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(task_ptr));
    let mut t = crate::types::ConcreteTypes;
    let result = run_fn(&mut t, module, tel, fn_id, Vec::new());
    // fz-4mk — shutdown drain mirrors run_main's exit path: enqueue every
    // surviving resource's dtor and dispatch each as a real fz call while
    // CURRENT_PROCESS is still pointing at the test task's heap.
    unsafe {
        fz_runtime::procbin::mso_drop_all_deferred(&mut (*task_ptr).heap);
    }
    if let Err(e) = drain_pending_dtors_interp(&mut t, module, tel) {
        tel.event(
            &["fz", "runtime", "dtor_drain_failed"],
            crate::metadata! { error: e },
        );
    }
    fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
    INTERP_SCHEMAS.with(|s| *s.borrow_mut() = None);
    match result {
        Ok(InterpStep::Done(_)) => Ok(()),
        Ok(InterpStep::Blocked(..)) | Ok(InterpStep::BlockedMatched(..)) => {
            Err("test fn blocked on receive with empty mailbox".to_string())
        }
        Err(e) => Err(e),
    }
}

/// Spawn a new task: enqueue it and return its pid immediately.
/// The child runs in a later scheduler quantum, not in the parent's.
fn interp_spawn(module: &Module, fn_id: FnId, args: Vec<InterpValue>) -> Result<u32, String> {
    use fz_runtime::process::ProcessState;
    let pid = interp_next_pid();
    let user_schemas = INTERP_SCHEMAS
        .with(|s| s.borrow().as_ref().cloned())
        .ok_or("interp_spawn: no INTERP_SCHEMAS installed (call run_main first)")?;
    let mut child = Box::new(Process::new(user_schemas));
    child.pid = pid;
    child.atom_names = module.atom_names.clone();
    child.state = ProcessState::Ready;
    interp_register_task(pid, child);
    INTERP_RESUME.with(|r| r.borrow_mut().insert(pid, (fn_id, args, vec![])));
    INTERP_RUN_QUEUE.with(|q| q.borrow_mut().push_back(pid));
    Ok(pid)
}

fn value_to_halt(v: InterpValue) -> i64 {
    let v = match v {
        InterpValue::Int(i) => return i,
        InterpValue::Float(f) => return f.to_bits() as i64,
        InterpValue::Tagged(v) => v,
    };
    use fz_runtime::fz_value::Tag;
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap(),
        // fz-yan.1 — see ir_runtime::fz_halt for the same shape.
        // nil/true/false flow through this atom arm now.
        Tag::Atom => v.unbox_atom().unwrap() as i64,
        Tag::Ptr | Tag::Reserved => v.0 as i64,
    }
}

/// Run an fz fn. Tail calls reuse this stack frame (O(1) Rust stack).
/// Returns Done(val) on Halt/Return or Blocked(fn_id, cap_vals) when a
/// Term::Receive fires on an empty mailbox.
fn run_fn<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    mut fn_id: FnId,
    mut args: Vec<InterpValue>,
) -> Result<InterpStep, String> {
    'tail: loop {
        let fn_ir = module.fn_by_id(fn_id);
        let mut env: HashMap<Var, InterpValue> = HashMap::new();
        let entry = fn_ir.block(fn_ir.entry);
        if entry.params.len() != args.len() {
            return Err(format!(
                "fn {} expected {} args, got {}",
                fn_ir.name,
                entry.params.len(),
                args.len()
            ));
        }
        for (p, v) in entry.params.iter().zip(args.iter()) {
            env.insert(*p, *v);
        }
        let mut cur = fn_ir.entry;
        loop {
            let blk = fn_ir.block(cur);
            for Stmt::Let(v, prim) in &blk.stmts {
                let val = eval_prim(t, module, tel, prim, &env)?;
                env.insert(*v, val);
            }
            match &blk.terminator {
                Term::Goto(b, gargs) => {
                    let vals: Vec<InterpValue> = gargs
                        .iter()
                        .map(|v| env_get(&env, *v))
                        .collect::<Result<_, _>>()?;
                    let next = fn_ir.block(*b);
                    for (p, val) in next.params.iter().zip(vals) {
                        env.insert(*p, val);
                    }
                    cur = *b;
                }
                Term::If {
                    cond,
                    then_b,
                    else_b,
                    ..
                } => {
                    let cv = env_get(&env, *cond)?;
                    cur = if is_truthy(cv) { *then_b } else { *else_b };
                }
                Term::Call {
                    ident: _,
                    callee,
                    args: call_args,
                    continuation,
                } => {
                    let arg_vals = collect(&env, call_args)?;
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn(t, module, tel, *callee, arg_vals)? {
                        InterpStep::Done(val) => {
                            let mut cont_args = vec![val];
                            cont_args.extend(outer_cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        InterpStep::Blocked(rf, cv, mut inner_after) => {
                            // Append our continuation to the chain so the
                            // scheduler calls it after the blocked task resumes.
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Blocked(rf, cv, inner_after));
                        }
                        InterpStep::BlockedMatched(park, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::BlockedMatched(park, inner_after));
                        }
                    }
                }
                Term::TailCall {
                    ident: _,
                    callee,
                    args: call_args,
                    is_back_edge,
                } => {
                    let mut arg_vals = collect(&env, call_args)?;
                    // fz-02r.6 — interpreter back-edge cooperative GC.
                    // Check FZ_SHOULD_YIELD at annotated back-edges; if set,
                    // forward live args through gc_mid_flight and clear the
                    // flag. The interpreter runs synchronously so no yield or
                    // re-enqueue is needed — just GC in place and continue.
                    if *is_back_edge {
                        use std::sync::atomic::Ordering;
                        if fz_runtime::yield_flag::FZ_SHOULD_YIELD.load(Ordering::Relaxed) != 0 {
                            let p = fz_runtime::process::current_process();
                            let root_parts: Vec<(u64, u8)> =
                                arg_vals.iter().map(|v| v.mid_flight_parts()).collect();
                            let mut root_words: Vec<u64> =
                                root_parts.iter().map(|(bits, _)| *bits).collect();
                            let mut root_tags: Vec<u8> =
                                root_parts.iter().map(|(_, tag)| *tag).collect();
                            p.heap
                                .gc_mid_flight(&mut root_words, &mut root_tags, &mut p.mailbox);
                            arg_vals = root_words
                                .into_iter()
                                .zip(root_tags)
                                .map(|(bits, tag)| InterpValue::from_mid_flight_parts(bits, tag))
                                .collect();
                            p.quiet_quanta = 0;
                            fz_runtime::yield_flag::FZ_SHOULD_YIELD.store(0, Ordering::Relaxed);
                        } else {
                            let p = fz_runtime::process::current_process();
                            p.quiet_quanta = p.quiet_quanta.saturating_add(1);
                        }
                    }
                    fn_id = *callee;
                    args = arg_vals;
                    continue 'tail;
                }
                Term::CallClosure {
                    ident: _,
                    closure,
                    args: call_args,
                    continuation,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl.to_fz()?)?;
                    clos_args.extend(collect(&env, call_args)?);
                    let outer_cap_vals = collect(&env, &continuation.captured)?;
                    match run_fn(t, module, tel, lam_fn, clos_args)? {
                        InterpStep::Done(val) => {
                            let mut cont_args = vec![val];
                            cont_args.extend(outer_cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        InterpStep::Blocked(rf, cv, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::Blocked(rf, cv, inner_after));
                        }
                        InterpStep::BlockedMatched(park, mut inner_after) => {
                            inner_after.push((continuation.fn_id, outer_cap_vals));
                            return Ok(InterpStep::BlockedMatched(park, inner_after));
                        }
                    }
                }
                Term::TailCallClosure {
                    ident: _,
                    closure,
                    args: call_args,
                } => {
                    let cl = env_get(&env, *closure)?;
                    let (lam_fn, mut clos_args) = unpack_closure(cl.to_fz()?)?;
                    clos_args.extend(collect(&env, call_args)?);
                    fn_id = lam_fn;
                    args = clos_args;
                    continue 'tail;
                }
                Term::Return(v) => return Ok(InterpStep::Done(env_get(&env, *v)?)),
                Term::Halt(v) => return Ok(InterpStep::Done(env_get(&env, *v)?)),
                Term::Receive {
                    continuation,
                    ident: _,
                } => {
                    let cap_vals = collect(&env, &continuation.captured)?;
                    match fz_runtime::process::current_process().mailbox.pop_front() {
                        Some(msg) => {
                            let msg = InterpValue::from_mailbox_slot(msg);
                            let mut cont_args = vec![msg];
                            cont_args.extend(cap_vals);
                            fn_id = continuation.fn_id;
                            args = cont_args;
                            continue 'tail;
                        }
                        None => {
                            return Ok(InterpStep::Blocked(continuation.fn_id, cap_vals, vec![]));
                        }
                    }
                }
                // fz-yxs/fz-2v3 — selective receive. Walk the mailbox
                // head-to-tail trying each clause in order; first match
                // wins. On miss, return BlockedMatched so the scheduler
                // can stash a park record for `interp_send`'s sender-side
                // probe to consult on the next arrival.
                Term::ReceiveMatched {
                    clauses,
                    matcher,
                    after,
                    pinned,
                    captures,
                    ..
                } => {
                    let pinned_map: HashMap<String, InterpValue> = pinned
                        .iter()
                        .map(|(name, var)| env_get(&env, *var).map(|v| (name.clone(), v)))
                        .collect::<Result<_, _>>()?;
                    let capture_vals: Vec<InterpValue> = collect(&env, captures)?;

                    let matched_clauses: Vec<MatchedClause> = clauses
                        .iter()
                        .map(|c| MatchedClause {
                            bound_names: c.bound_names.clone(),
                            guard: c.guard,
                            body: c.body,
                        })
                        .collect();

                    // Initial mailbox scan.
                    let mailbox_len = fz_runtime::process::current_process().mailbox.len();
                    let mut hit: Option<(usize, usize, Vec<InterpValue>)> = None;
                    for mb_idx in 0..mailbox_len {
                        let msg = {
                            let p = fz_runtime::process::current_process();
                            InterpValue::from_mailbox_slot(p.mailbox[mb_idx])
                        };
                        if let Some((clause_idx, binds)) = try_match_clauses(
                            t,
                            module,
                            tel,
                            &matched_clauses,
                            matcher,
                            msg,
                            &pinned_map,
                            &capture_vals,
                        )? {
                            hit = Some((mb_idx, clause_idx, binds));
                            break;
                        }
                    }

                    if let Some((mb_idx, clause_idx, bound_vals)) = hit {
                        fz_runtime::process::current_process()
                            .mailbox
                            .remove(mb_idx);
                        let body = matched_clauses[clause_idx].body;
                        let mut new_args = bound_vals;
                        new_args.extend(capture_vals);
                        fn_id = body;
                        args = new_args;
                        continue 'tail;
                    }

                    // Miss — `after 0` (timeout literal 0) fires the after
                    // body inline; any other after value (including
                    // `:infinity`) parks without a timer since the interp
                    // has no wall clock.
                    if let Some(a) = after {
                        let timeout_val = env_get(&env, a.timeout)?;
                        if timeout_val.unbox_int() == Some(0) {
                            fn_id = a.body;
                            args = capture_vals;
                            continue 'tail;
                        }
                    }

                    let park = ParkRecord {
                        clauses: matched_clauses,
                        matcher: matcher.clone(),
                        pinned: pinned_map,
                        captures: capture_vals,
                    };
                    return Ok(InterpStep::BlockedMatched(park, vec![]));
                }
            }
        }
    }
}

fn collect(env: &HashMap<Var, InterpValue>, vars: &[Var]) -> Result<Vec<InterpValue>, String> {
    vars.iter().map(|v| env_get(env, *v)).collect()
}

fn env_get(env: &HashMap<Var, InterpValue>, v: Var) -> Result<InterpValue, String> {
    env.get(&v)
        .copied()
        .ok_or_else(|| format!("unbound Var({})", v.0))
}

fn is_truthy(v: InterpValue) -> bool {
    v.is_truthy()
}

fn eval_prim<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    prim: &Prim,
    env: &HashMap<Var, InterpValue>,
) -> Result<InterpValue, String> {
    Ok(match prim {
        Prim::Const(c) => const_to_interp(c),
        Prim::BinOp(op, a, b) => {
            let av = env_get(env, *a)?;
            let bv = env_get(env, *b)?;
            eval_binop(*op, av, bv)?
        }
        Prim::UnOp(op, a) => {
            let av = env_get(env, *a)?;
            eval_unop(*op, av)?
        }
        Prim::Extern(eid, args) => {
            let arg_vals = collect(env, args)?;
            call_extern(t, module, tel, *eid, &arg_vals)?
        }
        Prim::MakeBitstring(fields) => {
            // fz-cty.7 — mirror src/ir_codegen.rs Prim::MakeBitstring: drive the
            // same runtime BitWriter through the same extern "C" calls the JIT
            // and AOT paths use, so all three paths funnel through the shared
            // bitstring substrate.
            use crate::ast::BitType as AstBitType;
            use crate::fz_ir::BitSizeIr;
            fn encode_bit_type(t: AstBitType) -> u32 {
                match t {
                    AstBitType::Integer => 0,
                    AstBitType::Float => 1,
                    AstBitType::Binary => 2,
                    AstBitType::Bits => 3,
                    AstBitType::Utf8 => 4,
                    AstBitType::Utf16 => 5,
                    AstBitType::Utf32 => 6,
                }
            }
            fn encode_endian(e: crate::ast::Endian) -> u32 {
                use crate::ast::Endian;
                match e {
                    Endian::Big => 0,
                    Endian::Little => 1,
                    Endian::Native => 2,
                }
            }
            fn default_unit_for(ty: AstBitType) -> u32 {
                match ty {
                    AstBitType::Integer | AstBitType::Float | AstBitType::Bits => 1,
                    AstBitType::Binary => 8,
                    AstBitType::Utf8 | AstBitType::Utf16 | AstBitType::Utf32 => 1,
                }
            }
            fz_runtime::ir_runtime::fz_bs_begin();
            for f in fields {
                let value_v = env_get(env, f.value)?;
                let ty_tag = encode_bit_type(f.ty);
                let unit = f.unit.unwrap_or(default_unit_for(f.ty));
                let endian_tag = encode_endian(f.endian);
                let signed = f.signed as u32;
                let (size_present, size_value) = match &f.size {
                    None => (0u32, 0u32),
                    Some(BitSizeIr::Literal(n)) => (1, *n),
                    Some(BitSizeIr::Var(v)) => {
                        let raw = env_get(env, *v)?;
                        let n = raw
                            .unbox_int()
                            .ok_or_else(|| "bit size var must be an integer".to_string())?;
                        (1, n as u32)
                    }
                };
                fz_runtime::ir_runtime::fz_bs_write_field(
                    value_v.tagged_bits()?,
                    ty_tag,
                    size_present,
                    size_value,
                    unit,
                    endian_tag,
                    signed,
                );
            }
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_bs_finalize()).into()
        }
        Prim::ConstBitstring(bytes, bit_len) => {
            // fz-cty.8 — bytes are owned by the Module (and live as long as
            // the interp run), so it's safe to alloc straight from them via
            // the shared runtime FFI; identical to the JIT/AOT lowering.
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_alloc_bitstring_const(
                bytes.as_ptr() as u64,
                bytes.len() as u64,
                *bit_len,
            ))
            .into()
        }
        Prim::MakeClosure(_, fn_id, captured) => {
            // Strict closure layout: schema_id preserves the body FnId,
            // fn_ptr is left null because the interpreter dispatches by FnId.
            let cap_vals: Vec<InterpValue> = collect(env, captured)?;
            let cap_fz: Vec<LegacyTaggedWord> = cap_vals
                .iter()
                .map(|v| v.to_fz())
                .collect::<Result<_, _>>()?;
            let bits = fz_runtime::process::current_process().heap.alloc_closure(
                fn_id.0,
                cap_fz.len(),
                0,
                0,
                &cap_fz,
            );
            LegacyTaggedWord(bits).into()
        }
        Prim::MakeTuple(elems) => {
            // fz-ul4.35 — mirror src/ir_codegen.rs MakeTuple: alloc a heap
            // Struct with `arity` LegacyTaggedWord slots and write each captured
            // value at offset 8 + i*8 (after the strict Struct prefix).
            // Schemas are registered lazily on first use of each arity; the
            // map is per-run (run_main / run_test_fn clear it), so schema
            // ids are stable across spawned tasks that share the registry.
            let arity = elems.len();
            let schema_id = interp_tuple_schema_id(arity);
            let p = fz_runtime::process::current_process()
                .heap
                .alloc_struct(schema_id);
            for (i, v) in elems.iter().enumerate() {
                let val = env_get(env, *v)?;
                let val = val.to_fz()?;
                unsafe {
                    let dst = p.add(8 + i * 8) as *mut LegacyTaggedWord;
                    std::ptr::write(dst, val);
                }
            }
            LegacyTaggedWord(fz_runtime::fz_value::tagged_struct_bits(p)).into()
        }
        Prim::TupleField(c, idx) => {
            let cv = env_get(env, *c)?;
            let cv = cv.to_fz()?;
            let p = fz_runtime::fz_value::struct_addr_from_tagged(cv.0)
                .ok_or_else(|| "TupleField: subject is not a tagged Struct".to_string())?;
            let off = 8 + (*idx as usize) * 8;
            unsafe {
                let src = p.add(off) as *const LegacyTaggedWord;
                std::ptr::read(src).into()
            }
        }
        Prim::MakeVec(kind, elems) => {
            use crate::fz_ir::VecKindIr;
            let kind_tag = match kind {
                VecKindIr::I64 => fz_runtime::fz_value::TAG_VEC_I64 as u32,
                VecKindIr::F64 => fz_runtime::fz_value::TAG_VEC_F64 as u32,
                VecKindIr::U8 => fz_runtime::fz_value::TAG_VEC_U8 as u32,
                VecKindIr::Bit => fz_runtime::fz_value::TAG_VEC_BIT as u32,
            };
            fz_runtime::ir_runtime::fz_vec_begin(kind_tag);
            for elem in elems {
                let value = env_get(env, *elem)?;
                let (bits, kind) = value.slot_parts()?;
                fz_runtime::ir_runtime::fz_vec_push_typed(bits, kind);
            }
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_vec_finalize()).into()
        }
        Prim::TypeTest(v, descr) => {
            use fz_runtime::fz_value::{Tag, ValueKind};
            let descr = crate::concrete_types::ty_descr(descr.as_ref());
            let val = env_get(env, *v)?;
            if matches!(val, InterpValue::Float(_)) {
                return Ok(bool_value(descr.type_test_has_floats()).into());
            }
            if matches!(val, InterpValue::Int(_)) {
                return Ok(bool_value(descr.type_test_has_ints()).into());
            }
            let val = val.to_fz()?;
            let tag = val.tag();
            let mut matched = false;
            if descr.type_test_has_ints() {
                matched |= tag == Tag::Int;
            }
            if descr.type_test_atom_is_any() {
                matched |= tag == Tag::Atom;
            } else if descr.type_test_atom_is_cofinite() {
                return Err(
                    "TypeTest: cofinite atom literal sets not yet supported in interpreter".into(),
                );
            } else {
                let names = descr.type_test_atom_literals();
                if !names.is_empty() {
                    matched |= tag == Tag::Atom;
                    // fz-yan.2 — atoms axis subsumes the old nil/bool bit axes.
                    if tag == Tag::Atom {
                        let id = val.unbox_atom().expect("atom-tagged");
                        for name in &names {
                            if let Some(pos) = module.atom_names.iter().position(|n| n == name)
                                && pos as u32 == id
                            {
                                matched = true;
                                break;
                            }
                        }
                    }
                }
            }
            if let Some(kind) = fz_runtime::fz_value::vec_addr_from_tagged(val.0)
                .filter(|p| {
                    !p.is_null()
                        && fz_runtime::process::current_process()
                            .heap
                            .contains_heap_addr(*p)
                })
                .and_then(|_| fz_runtime::fz_value::vec_kind_from_tagged(val.0))
            {
                if descr.type_test_has_vec_i64() && kind == ValueKind::VEC_I64 {
                    matched = true;
                }
                if descr.type_test_has_vec_f64() && kind == ValueKind::VEC_F64 {
                    matched = true;
                }
                if descr.type_test_has_vec_u8() && kind == ValueKind::VEC_U8 {
                    matched = true;
                }
                if descr.type_test_has_vec_bit() && kind == ValueKind::VEC_BIT {
                    matched = true;
                }
            }
            // fz-ul4.36 — match if value is a strict struct pointer with matching
            // schema_id. Negated tuple clauses unsupported.
            assert!(
                !descr.type_test_tuple_has_negations(),
                "TypeTest: negated tuple clauses not yet supported"
            );
            if let Some(sp) = fz_runtime::fz_value::struct_addr_from_tagged(val.0) {
                let actual_schema =
                    unsafe { fz_runtime::fz_value::struct_schema_id(sp as *const u8) };
                for arity in descr.type_test_tuple_arities() {
                    let want_schema = interp_tuple_schema_id(arity);
                    if actual_schema == want_schema {
                        matched = true;
                        break;
                    }
                }
            }
            if matched {
                LegacyTaggedWord::TRUE.into()
            } else {
                LegacyTaggedWord::FALSE.into()
            }
        }
        // fz-fyq.5 — list primitives. Same runtime helpers and memory
        // layout as ir_codegen's JIT/AOT paths use (strict 16-byte cons
        // cells); the empty list is the
        // single bit pattern `LegacyTaggedWord::EMPTY_LIST`. Until this lands,
        // every interp run of a program containing a list literal
        // exited 75 "Deferred" and the fixture matrix silently skipped
        // it.
        Prim::ListCons(h, t) => {
            let hv = env_get(env, *h)?;
            let tv = env_get(env, *t)?;
            let (head_bits, head_kind) = hv.slot_parts()?;
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_alloc_list_cons_typed(
                head_bits,
                head_kind,
                tv.tagged_bits()?,
            ))
            .into()
        }
        Prim::ListHead(c) => {
            let cv = env_get(env, *c)?;
            interp_list_head(cv.to_fz()?)?
        }
        Prim::ListTail(c) => {
            let cv = env_get(env, *c)?;
            interp_list_tail(cv.to_fz()?)?.into()
        }
        Prim::IsEmptyList(c) => {
            let cv = env_get(env, *c)?;
            if cv.is_empty_list() {
                LegacyTaggedWord::TRUE.into()
            } else {
                LegacyTaggedWord::FALSE.into()
            }
        }
        Prim::MapGet(m, k) => {
            let mv = env_get(env, *m)?;
            let kv = env_get(env, *k)?;
            match interp_map_get(mv.to_fz()?, kv)? {
                Some(value) => value,
                None => LegacyTaggedWord::NIL.into(),
            }
        }
        Prim::MatcherMapGet(m, k) => {
            let mv = env_get(env, *m)?;
            let kv = env_get(env, *k)?;
            let (key_bits, key_kind) = kv.slot_parts()?;
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_matcher_map_get_typed(
                mv.tagged_bits()?,
                key_bits,
                key_kind,
            ))
            .into()
        }
        Prim::IsMatcherMapMiss(v) => {
            let value = env_get(env, *v)?;
            if value.tagged_bits()? == fz_runtime::fz_value::MATCHER_MAP_MISS_BITS {
                LegacyTaggedWord::TRUE.into()
            } else {
                LegacyTaggedWord::FALSE.into()
            }
        }
        Prim::MakeMap(entries) => {
            // fz-puj.47 (X6) — interp side of the same fz_map_*
            // builder triple JIT/AOT use. Begin → push each (k, v) →
            // finalize. The current_process()-scoped builder is fine
            // because interp runs single-threaded inside one Process.
            fz_runtime::ir_runtime::fz_map_begin();
            for (kv, vv) in entries {
                let k = env_get(env, *kv)?;
                let v = env_get(env, *vv)?;
                let (kb, kk) = k.slot_parts()?;
                let (vb, vk) = v.slot_parts()?;
                fz_runtime::ir_runtime::fz_map_push_typed(kb, kk, vb, vk);
            }
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_map_finalize()).into()
        }
        Prim::MapUpdate(base, entries) => {
            let base = env_get(env, *base)?;
            fz_runtime::ir_runtime::fz_map_clone(base.tagged_bits()?);
            for (kv, vv) in entries {
                let k = env_get(env, *kv)?;
                let v = env_get(env, *vv)?;
                let (kb, kk) = k.slot_parts()?;
                let (vb, vk) = v.slot_parts()?;
                fz_runtime::ir_runtime::fz_map_push_typed(kb, kk, vb, vk);
            }
            LegacyTaggedWord(fz_runtime::ir_runtime::fz_map_finalize()).into()
        }
        Prim::MakeList(elems, tail) => {
            // Mirror ir_codegen: fold cons from right, starting with
            // `tail` (defaulted to the empty list).
            let mut acc = match tail {
                Some(t) => env_get(env, *t)?,
                None => LegacyTaggedWord::EMPTY_LIST.into(),
            };
            for e in elems.iter().rev() {
                let ev = env_get(env, *e)?;
                let (head_bits, head_kind) = ev.slot_parts()?;
                acc = LegacyTaggedWord(fz_runtime::ir_runtime::fz_alloc_list_cons_typed(
                    head_bits,
                    head_kind,
                    acc.tagged_bits()?,
                ))
                .into();
            }
            acc
        }
        // fz-axu.23 (M2) — lower_program_full erases Prim::Brand
        // before the interp sees the module. Surface a stray Brand
        // instead of silently aliasing.
        Prim::Brand(_, _) => unreachable!(
            "Prim::Brand reached interp — erasure should run inside lower_program_full"
        ),
        _ => {
            return Err(format!(
                "interp .5.2: prim {:?} not yet supported (lands in fz-ul4.23.5.3+)",
                std::mem::discriminant(prim)
            ));
        }
    })
}

/// Read an interp-side closure value. fz-ul4.29.5 layout:
///   header (16) + stub_fp (8) + captured: [LegacyTaggedWord; n] (offset 24+)
///   header._reserved = callee FnId; header.flags = captured count.
/// fz-4mk — interpreter-leg drain of `Heap::pending_dtors`. Pops each
/// `(closure_bits, payload)` enqueued by `mso_sweep`/`mso_drop_all`,
/// unpacks the closure to its body FnId + captures, and runs the body
/// as a fully fz-side call via `run_fn`. The dtor's return value is
/// discarded. Errors from the dtor body propagate to the caller; the
/// run-loop logs and continues.
///
/// Pre-conditions: `CURRENT_PROCESS` is set to the heap owning the
/// queue. Closures in the queue point into that heap.
fn drain_pending_dtors_interp<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<(), String> {
    loop {
        let entry = {
            let p = fz_runtime::process::current_process();
            p.heap.pending_dtors.pop_front()
        };
        let Some((closure_bits, payload)) = entry else {
            break;
        };
        let closure = LegacyTaggedWord(closure_bits);
        let (fn_id, captured) = match unpack_closure(closure) {
            Ok(x) => x,
            Err(e) => {
                tel.event(
                    &["fz", "runtime", "bad_dtor_closure"],
                    crate::metadata! { error: e },
                );
                continue;
            }
        };
        let mut args = captured;
        args.push(LegacyTaggedWord(payload).into());
        match run_fn(t, module, tel, fn_id, args)? {
            InterpStep::Done(_) => {}
            InterpStep::Blocked(_, _, _) | InterpStep::BlockedMatched(_, _) => {
                return Err("fz-4mk drain: dtor blocked on receive (unsupported in v1)".into());
            }
        }
    }
    Ok(())
}

fn unpack_closure(v: LegacyTaggedWord) -> Result<(FnId, Vec<InterpValue>), String> {
    let p = fz_runtime::fz_value::closure_addr_from_tagged(v.0).ok_or_else(|| {
        format!(
            "call_closure on non-closure value: {}",
            fz_runtime::fz_value::debug::render(v.0)
        )
    })?;
    let fn_id = FnId(unsafe { fz_runtime::fz_value::closure_schema_id(p) });
    let cap_count = unsafe { fz_runtime::fz_value::closure_captured_count(p) };
    let captured: Vec<InterpValue> = (0..cap_count)
        .map(|i| {
            LegacyTaggedWord(unsafe {
                std::ptr::read(fz_runtime::fz_value::closure_capture_slot(p, i)).0
            })
            .into()
        })
        .collect();
    Ok((fn_id, captured))
}

fn const_to_interp(c: &Const) -> InterpValue {
    match c {
        Const::Int(n) => InterpValue::Int(*n),
        Const::Atom(id) => legacy_tagged_atom_word(*id).into(),
        Const::Nil => LegacyTaggedWord::NIL.into(),
        Const::True => LegacyTaggedWord::TRUE.into(),
        Const::False => LegacyTaggedWord::FALSE.into(),
        Const::Float(f) => InterpValue::Float(*f),
    }
}

fn eval_binop(op: BinOp, a: InterpValue, b: InterpValue) -> Result<InterpValue, String> {
    macro_rules! int_arith {
        ($op:tt) => {
            match (a.unbox_int(), b.unbox_int()) {
                (Some(x), Some(y)) => Ok(InterpValue::Int(x $op y)),
                _ => {
                    let af = a.as_float().ok_or_else(|| "lhs is not numeric".to_string())?;
                    let bf = b.as_float().ok_or_else(|| "rhs is not numeric".to_string())?;
                    Ok(InterpValue::Float(af $op bf))
                }
            }
        };
    }
    macro_rules! float_cmp {
        ($op:tt) => {{
            let af = a.as_float().ok_or_else(|| "lhs is not numeric".to_string())?;
            let bf = b.as_float().ok_or_else(|| "rhs is not numeric".to_string())?;
            Ok(bool_value(af $op bf).into())
        }};
    }
    match op {
        BinOp::Add => int_arith!(+),
        BinOp::Sub => int_arith!(-),
        BinOp::Mul => int_arith!(*),
        BinOp::Div => int_arith!(/),
        BinOp::Mod => int_arith!(%),
        BinOp::Eq => Ok(bool_value(interp_value_eq(a, b)?).into()),
        BinOp::Neq => Ok(bool_value(!interp_value_eq(a, b)?).into()),
        BinOp::Lt => float_cmp!(<),
        BinOp::Le => float_cmp!(<=),
        BinOp::Gt => float_cmp!(>),
        BinOp::Ge => float_cmp!(>=),
        BinOp::And => Ok(if !is_truthy(a) { a } else { b }),
        BinOp::Or => Ok(if is_truthy(a) { a } else { b }),
    }
}

fn eval_unop(op: UnOp, a: InterpValue) -> Result<InterpValue, String> {
    match op {
        UnOp::Neg => match a {
            InterpValue::Int(value) => Ok(InterpValue::Int(-value)),
            InterpValue::Float(value) => Ok(InterpValue::Float(-value)),
            InterpValue::Tagged(value) => {
                if let Some(value) = value.unbox_int() {
                    Ok(InterpValue::Int(-value))
                } else {
                    Err(format!(
                        "`-` on {}",
                        fz_runtime::fz_value::debug::render(value.0)
                    ))
                }
            }
        },
        UnOp::Not => Ok(bool_value(!is_truthy(a)).into()),
    }
}

fn interp_value_eq(a: InterpValue, b: InterpValue) -> Result<bool, String> {
    match (a, b) {
        (InterpValue::Int(a), InterpValue::Int(b)) => Ok(a == b),
        (InterpValue::Int(a), InterpValue::Tagged(b))
        | (InterpValue::Tagged(b), InterpValue::Int(a)) => Ok(b.unbox_int() == Some(a)),
        (InterpValue::Int(_), InterpValue::Float(_))
        | (InterpValue::Float(_), InterpValue::Int(_)) => Ok(false),
        (InterpValue::Float(a), InterpValue::Float(b)) => Ok(a == b),
        (InterpValue::Float(_), InterpValue::Tagged(_))
        | (InterpValue::Tagged(_), InterpValue::Float(_)) => Ok(false),
        (InterpValue::Tagged(a), InterpValue::Tagged(b)) => {
            Ok(LegacyTaggedWord(fz_runtime::ir_runtime::fz_value_eq(a.0, b.0)).is_true())
        }
    }
}

/// fz-4mk — shared work behind both the interp `fz_make_resource` BIF and
/// the JIT/AOT `MakeResourceHook` thunk: validate the dtor closure, then
/// allocate the off-heap `Resource` + on-heap stub on the current process
/// heap. The dtor body fires as real fz code at scheduler-boundary drain
/// via `fz_drain_dtor_entry` (JIT/AOT) or `run_fn` (interp); the
/// Resource's C-side dtor slot is the no-op so refcount→0 paths that
/// bypass the drain don't double-fire.
pub(crate) fn make_resource_in_current_process(
    _module: &Module,
    payload: u64,
    dtor_closure: LegacyTaggedWord,
) -> Result<LegacyTaggedWord, String> {
    fz_runtime::fz_value::closure_addr_from_tagged(dtor_closure.0)
        .ok_or_else(|| "make_resource: dtor arg is not a closure".to_string())?;
    let handle = fz_runtime::resource::ResourceHandle::new(
        payload,
        fz_runtime::resource::fz_resource_destructor_noop,
    );
    let heap = &mut fz_runtime::process::current_process().heap;
    let stub = fz_runtime::resource::alloc_resource(heap, handle, dtor_closure);
    Ok(LegacyTaggedWord(
        fz_runtime::fz_value::tagged_resource_bits(stub.as_raw() as *const u8),
    ))
}

fn call_extern<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    eid: ExternId,
    args: &[InterpValue],
) -> Result<InterpValue, String> {
    let decl = module.extern_by_id(eid);
    // Assert fns use std::process::abort on failure — fatal for the JIT/AOT
    // path, but unusable in the interpreter where failures must return Err.
    // Handle them inline with the same logic as run_builtin::Assert*.
    match decl.symbol.as_str() {
        "fz_assert" => {
            if args.len() != 1 {
                return Err(format!("fz_assert/1 got {} args", args.len()));
            }
            return if is_truthy(args[0]) {
                Ok(LegacyTaggedWord::NIL.into())
            } else {
                Err("assertion failed".into())
            };
        }
        "fz_assert_eq" => {
            if args.len() != 2 {
                return Err(format!("fz_assert_eq/2 got {} args", args.len()));
            }
            let eq = bool_value(interp_value_eq(args[0], args[1])?);
            return if eq.is_true() {
                Ok(LegacyTaggedWord::NIL.into())
            } else {
                Err(format!(
                    "assertion failed: assert_eq({}, {})",
                    args[0].render(),
                    args[1].render(),
                ))
            };
        }
        "fz_assert_neq" => {
            if args.len() != 2 {
                return Err(format!("fz_assert_neq/2 got {} args", args.len()));
            }
            let eq = bool_value(interp_value_eq(args[0], args[1])?);
            return if eq.is_false() {
                Ok(LegacyTaggedWord::NIL.into())
            } else {
                Err(format!(
                    "assertion failed: assert_neq({}, {})",
                    args[0].render(),
                    args[1].render(),
                ))
            };
        }
        "fz_print_value" => {
            if args.len() != 1 {
                return Err(format!("fz_print_value/1 got {} args", args.len()));
            }
            args[0].print()?;
            return Ok(LegacyTaggedWord::NIL.into());
        }
        "fz_print_i64" => {
            if args.len() != 1 {
                return Err(format!("fz_print_i64/1 got {} args", args.len()));
            }
            if let Some(n) = args[0].unbox_int() {
                let candidate_addr = (n as u64).wrapping_shl(3);
                if candidate_addr != 0
                    && fz_runtime::process::current_process()
                        .heap
                        .contains_heap_addr(candidate_addr as *mut u8)
                {
                    fz_runtime::ir_runtime::fz_print_value(
                        candidate_addr | fz_runtime::fz_value::TAG_LIST,
                    );
                } else {
                    fz_runtime::fz_print_i64(n);
                }
            } else {
                args[0].print()?;
            }
            return Ok(LegacyTaggedWord::NIL.into());
        }
        "fz_print_f64" => {
            if args.len() != 1 {
                return Err(format!("fz_print_f64/1 got {} args", args.len()));
            }
            args[0].print()?;
            return Ok(LegacyTaggedWord::NIL.into());
        }
        // Spawn/send/self need the interpreter's own scheduler — the C
        // implementations require a Runtime spawn hook which is only
        // installed on the JIT/AOT path.
        "fz_spawn" | "fz_spawn_opt" => {
            if args.is_empty() {
                return Err(format!("{}/1+ got 0 args", &decl.symbol));
            }
            // args[0] is the thunk closure (wrapping the user's closure);
            // args[1] (fz_spawn_opt) is a min_heap_size hint — ignored here.
            let (fn_id, captured) = unpack_closure(args[0].to_fz()?)?;
            let pid = interp_spawn(module, fn_id, captured)?;
            return Ok(legacy_tagged_int_word(pid as i64).into());
        }
        "fz_self" => {
            return Ok(
                legacy_tagged_int_word(fz_runtime::process::current_process().pid as i64).into(),
            );
        }
        "fz_make_ref" => {
            // fz-ht5 — route through the runtime FFI so interp and JIT
            // share the same counter; otherwise an interp run followed
            // by a JIT run in the same process could collide.
            let bits = fz_runtime::ir_runtime::fz_make_ref();
            return Ok(LegacyTaggedWord(bits).into());
        }
        "fz_send" => {
            if args.len() != 2 {
                return Err(format!("fz_send/2 got {} args", args.len()));
            }
            let receiver = args[0]
                .unbox_int()
                .ok_or_else(|| "send/2: pid must be Int".to_string())?
                as u32;
            interp_send(t, module, tel, receiver, args[1])?;
            return Ok(args[1]);
        }
        "fz_make_resource" => {
            // fz-swt.7 / fz-swt.10 — interp BIF: routes through the same
            // shared helper used by the runtime's `MakeResourceHook` for
            // the JIT/AOT legs, so dtor-resolution semantics are uniform
            // across paths.
            if args.len() != 2 {
                return Err(format!("fz_make_resource/2 got {} args", args.len()));
            }
            return make_resource_in_current_process(
                module,
                args[0].tagged_bits()?,
                args[1].to_fz()?,
            )
            .map(Into::into);
        }
        _ => {}
    }
    let fp = resolve_symbol(&decl.symbol)?;
    let raw_args: Vec<u64> = args
        .iter()
        .zip(decl.params.iter())
        .map(|(v, ty)| match ty {
            ExternTy::I64 => v.unbox_int().unwrap_or(0) as u64,
            // fz-8up — Binary/CString call into the runtime helpers from
            // [[fz-9ss]] and pass the returned pointer as the C arg.
            ExternTy::Binary => {
                (unsafe {
                    fz_runtime::extern_binary::fz_binary_as_ptr(v.tagged_bits().unwrap_or(0))
                }) as u64
            }
            ExternTy::CString => {
                (unsafe {
                    fz_runtime::extern_binary::fz_binary_as_cstring(v.tagged_bits().unwrap_or(0))
                }) as u64
            }
            _ => v.tagged_bits().unwrap_or(0),
        })
        .collect();
    let returns_value = !matches!(decl.ret, ExternTy::Unit | ExternTy::Never);
    let ret = if returns_value {
        unsafe { dispatch_fn_returning(fp, &raw_args) }
    } else {
        unsafe { dispatch_fn_void(fp, &raw_args) };
        0
    };
    // fz-rb8 — `:: integer` returns a raw signed 64-bit value from C;
    // auto-box to LegacyTaggedWord::Int. Other return classes treat the bits as
    // an already-tagged LegacyTaggedWord.
    let boxed = match decl.ret {
        ExternTy::I64 => legacy_tagged_int_word(ret as i64).0,
        _ => ret,
    };
    Ok(LegacyTaggedWord(boxed).into())
}

/// Return the function pointer for a named C symbol.
///
/// Checks the built-in native table first (all symbols declared in runtime.fz
/// are registered here so that the interpreter finds them even when the runtime
/// is statically linked and dlsym(RTLD_DEFAULT) cannot reach the symbols).
/// Falls back to dlsym for any name not in the table.
fn resolve_symbol(name: &str) -> Result<*const (), String> {
    // Native table: every symbol declared in runtime.fz. These Rust functions
    // are linked into the binary; using their address directly avoids relying
    // on dlsym visibility, which is unreliable for statically-linked rlibs.
    #[cfg(test)]
    if let Some(fp) = tests_support::lookup_test_symbol(name) {
        return Ok(fp);
    }
    let native: Option<*const ()> = match name {
        "fz_print_i64" => Some(fz_runtime::fz_print_i64 as *const ()),
        "fz_print_value" => Some(fz_runtime::ir_runtime::fz_print_value as *const ()),
        "fz_assert" => Some(fz_runtime::fz_assert as *const ()),
        "fz_assert_eq" => Some(fz_runtime::fz_assert_eq as *const ()),
        "fz_assert_neq" => Some(fz_runtime::fz_assert_neq as *const ()),
        "fz_vec_get" => Some(fz_runtime::ir_runtime::fz_vec_get as *const ()),
        "fz_spawn" => Some(fz_runtime::ir_runtime::fz_spawn as *const ()),
        "fz_spawn_opt" => Some(fz_runtime::ir_runtime::fz_spawn_opt as *const ()),
        "fz_self" => Some(fz_runtime::ir_runtime::fz_self as *const ()),
        "fz_make_ref" => Some(fz_runtime::ir_runtime::fz_make_ref as *const ()),
        "fz_send" => Some(fz_runtime::ir_runtime::fz_send as *const ()),
        // fz-swt.11 — fixture/test dtor exported from the runtime crate.
        // Bound here so interp-leg invocations of fixtures using this
        // symbol (e.g. when `fz interp` is run by hand on the AOT-only
        // fixture) reach the same Rust fn the AOT-linked binary uses.
        "fz_resource_test_print_dtor" => {
            Some(fz_runtime::resource::fz_resource_test_print_dtor as *const ())
        }
        // fz-swt.13 — tmpfile helper for file fixtures. Same rationale as
        // the print-dtor binding above: keep the interp leg of the fixture
        // matrix self-contained, no dlsym dependence.
        "fz_test_open_tmpfile" => Some(fz_runtime::resource::fz_test_open_tmpfile as *const ()),
        // fz-axu.14 (R1) — utf8 runtime support. Bound here so the
        // interp leg of the matrix can resolve them without relying on
        // dlsym; statically-linked rlibs don't expose these via
        // RTLD_DEFAULT on Linux.
        "fz_bitstring_valid_utf8" => {
            Some(fz_runtime::ir_runtime::fz_bitstring_valid_utf8 as *const ())
        }
        "fz_brand_bitstring_as_utf8" => {
            Some(fz_runtime::ir_runtime::fz_brand_bitstring_as_utf8 as *const ())
        }
        _ => None,
    };
    if let Some(fp) = native {
        return Ok(fp);
    }
    // Fallback: dlsym for user-declared externs not in the native table.
    use std::ffi::CString;
    let cname = CString::new(name).map_err(|e| format!("bad symbol name: {}", e))?;
    #[cfg(unix)]
    let ptr = unsafe { libc::dlsym(libc::RTLD_DEFAULT, cname.as_ptr()) };
    #[cfg(not(unix))]
    let ptr: *mut std::ffi::c_void = std::ptr::null_mut();
    if ptr.is_null() {
        return Err(format!("dlsym: symbol `{}` not found", name));
    }
    Ok(ptr as *const ())
}

unsafe fn dispatch_fn_returning(fp: *const (), args: &[u64]) -> u64 {
    match args.len() {
        0 => unsafe {
            let f: unsafe extern "C" fn() -> u64 = std::mem::transmute(fp);
            f()
        },
        1 => unsafe {
            let f: unsafe extern "C" fn(u64) -> u64 = std::mem::transmute(fp);
            f(args[0])
        },
        2 => unsafe {
            let f: unsafe extern "C" fn(u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1])
        },
        3 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1], args[2])
        },
        4 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64, u64) -> u64 = std::mem::transmute(fp);
            f(args[0], args[1], args[2], args[3])
        },
        n => panic!("extern arity {} not supported (max 4)", n),
    }
}

unsafe fn dispatch_fn_void(fp: *const (), args: &[u64]) {
    match args.len() {
        0 => unsafe {
            let f: unsafe extern "C" fn() = std::mem::transmute(fp);
            f()
        },
        1 => unsafe {
            let f: unsafe extern "C" fn(u64) = std::mem::transmute(fp);
            f(args[0])
        },
        2 => unsafe {
            let f: unsafe extern "C" fn(u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1])
        },
        3 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1], args[2])
        },
        4 => unsafe {
            let f: unsafe extern "C" fn(u64, u64, u64, u64) = std::mem::transmute(fp);
            f(args[0], args[1], args[2], args[3])
        },
        n => panic!("extern arity {} not supported (max 4)", n),
    }
}

// ===== Test-only symbol registry (fz-swt.7) ================================

/// fz-swt.10 — expose the test counter dtor's raw address so JIT-leg
/// fixture tests can register it with the `JITBuilder`. Lives in this
/// module to share the `DTOR_FIRED` / `DTOR_LAST_PAYLOAD` statics with
/// the interp-leg tests below.
#[cfg(test)]
pub(crate) fn tests_support_test_dtor_addr() -> *const u8 {
    tests_support::_resource_test_dtor as *const u8
}

/// fz-swt.10 — accessors for the test dtor counters, used by both the
/// interp-leg tests in this file and the JIT-leg tests in
/// `ir_codegen_tests.rs`.
#[cfg(test)]
pub(crate) fn tests_support_dtor_reset() {
    use std::sync::atomic::Ordering;
    tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
    tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_fired() -> usize {
    tests_support::DTOR_FIRED.load(std::sync::atomic::Ordering::Relaxed)
}

#[cfg(test)]
pub(crate) fn tests_support_dtor_last_payload() -> u64 {
    tests_support::DTOR_LAST_PAYLOAD.load(std::sync::atomic::Ordering::Relaxed)
}

/// fz-swt.10 — shared lock so JIT-leg and interp-leg resource tests
/// don't race on the static `DTOR_*` counters.
#[cfg(test)]
pub(crate) fn tests_support_lock() -> &'static std::sync::Mutex<()> {
    static LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    &LOCK
}

#[cfg(test)]
mod tests_support {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    pub static DTOR_FIRED: AtomicUsize = AtomicUsize::new(0);
    pub static DTOR_LAST_PAYLOAD: AtomicU64 = AtomicU64::new(0);

    /// Counter-bumping dtor. Used by the fz-side test as the
    /// `&_resource_test_dtor/1` wrapped extern: bumps a global counter
    /// and records the payload it received. Verifies that the BIF stored
    /// the right C-ABI fn ptr and that MSO sweep invoked it on the right
    /// payload.
    #[unsafe(no_mangle)]
    pub unsafe extern "C" fn _resource_test_dtor(payload: u64) {
        DTOR_FIRED.fetch_add(1, Ordering::Relaxed);
        DTOR_LAST_PAYLOAD.store(payload, Ordering::Relaxed);
    }

    pub fn lookup_test_symbol(name: &str) -> Option<*const ()> {
        match name {
            "_resource_test_dtor" => Some(_resource_test_dtor as *const ()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod typed_slot_tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        crate::ir_lower::lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower")
    }

    fn run(src: &str) -> i64 {
        let m = lower_src(src);
        super::run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run")
    }

    fn capture(src: &str) -> String {
        let m = lower_src(src);
        let _ = fz_runtime::ir_runtime::test_capture_take();
        super::run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run");
        fz_runtime::ir_runtime::test_capture_take().join("\n")
    }

    #[test]
    fn interp_typed_int_arithmetic_full_i64() {
        assert_eq!(
            run("fn main(), do: 4611686018427387904 + 7"),
            4611686018427387911
        );
    }

    #[test]
    fn interp_typed_float_raw() {
        assert_eq!(f64::from_bits(run("fn main(), do: 1.5 + 2.5") as u64), 4.0);
    }

    #[test]
    fn interp_render_raw_float_in_container() {
        assert_eq!(capture("fn main(), do: print([1.5])"), "[1.5]");
    }

    #[test]
    fn interp_equality_float_in_container() {
        assert_eq!(run("fn main(), do: [1.5] == [1.5]"), 1);
    }

    #[test]
    fn interp_receive_matcher_float_in_container() {
        assert_eq!(
            run(r#"
                fn main() do
                  send(self(), [2.5])
                  receive do
                    [2.5] -> 7
                  end
                end
            "#),
            7
        );
    }

    #[test]
    fn interp_deep_copy_float_in_container_preserves_raw_slot() {
        run(r#"
            fn main() do
              send(self(), [2.5])
              nil
            end
        "#);

        super::INTERP_TASKS.with(|tasks| {
            let tasks = tasks.borrow();
            let task = tasks.get(&1).expect("main task remains registered");
            let slot = task.mailbox.front().expect("self-send remains queued");
            assert_eq!(slot.kind(), fz_runtime::fz_value::ValueKind::LIST);
            let list = fz_runtime::fz_value::list_addr_from_tagged(slot.value)
                .expect("mailbox slot keeps tagged list pointer");
            let head = unsafe { (*(list as *const fz_runtime::fz_value::ListCons)).head_typed() };
            assert_eq!(head.kind, fz_runtime::fz_value::ValueKind::FLOAT);
            assert_eq!(f64::from_bits(head.raw), 2.5);
        });
    }

    #[test]
    fn interp_typed_int_send_receive_boundary() {
        assert_eq!(
            run(r#"
                fn main() do
                  send(self(), 4611686018427387904)
                  receive()
                end
                "#,),
            4611686018427387904
        );
    }

    #[test]
    fn interp_typed_int_list_head_boundary() {
        assert_eq!(
            run(r#"
                fn first([h | _]), do: h
                fn main(), do: first([4611686018427387904])
            "#),
            4611686018427387904
        );
    }

    #[test]
    fn interp_typed_int_map_get_boundary() {
        assert_eq!(
            run("fn main(), do: %{answer: 4611686018427387904}.answer"),
            4611686018427387904
        );
    }

    #[test]
    fn interp_typed_int_dispatch_and_return_flow() {
        assert_eq!(
            run(r#"
                fn bump(x :: integer), do: x + 7
                fn bump(_), do: 0
                fn main(), do: bump(4611686018427387904)
            "#),
            4611686018427387911
        );
    }

    #[test]
    fn interp_typed_int_sender_wakes_blocked_receiver() {
        assert_eq!(
            run(r#"
                fn child(parent) do
                  send(parent, 4611686018427387904)
                end
                fn main() do
                  me = self()
                  spawn(fn () -> child(me))
                  receive()
                end
            "#),
            4611686018427387904
        );
    }
}

#[cfg(test)]
mod resource_bif_tests {
    use super::*;
    use crate::test_runner;
    use std::sync::atomic::Ordering;

    /// fz-swt.7 acceptance — interp BIF round-trip.
    ///
    /// User-level fz source declares a wrapper around a C extern and uses
    /// `make_resource(payload, &wrapper/1)`. The interp BIF walks the
    /// closure's IR body, resolves the extern symbol to the C fn pointer
    /// in `tests_support`, allocates an off-heap Resource, and returns a
    /// `TAG_RESOURCE` stub. The process heap is dropped at test
    /// scope exit; MSO sweep invokes the dtor on the payload exactly once.
    #[test]
    fn make_resource_bif_round_trip() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_make_resource() do
  r = make_resource(42, &dwrap/1)
  assert(true)
end
"#;
        test_runner::run_str(src).expect("test_runner run_str succeeded");

        // Force the interp's task registry to drop. Process drop drops
        // its Heap, which fires `mso_drop_all` and invokes our dtor.
        super::interp_reset_state();

        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            1,
            "dtor must fire exactly once after process heap drop"
        );
        // fz-4mk — the dtor body runs as ordinary fz code through
        // dispatched closure; the extern's `:: integer` marshal class
        // unboxes the payload before the C fn sees it. So the C dtor
        // receives the *unboxed* int 42, not the tagged LegacyTaggedWord bits.
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            42,
            "dtor (called via fz dispatch + extern unboxing) receives the unboxed int payload"
        );
    }

    /// fz-swt.9 acceptance — aliasing inside a single process.
    ///
    /// `r2 = r1` copies the LegacyTaggedWord tag bits; both names refer to the
    /// same on-heap stub which holds a single refcount edge to the
    /// off-heap Resource. The dtor must fire **exactly once** when the
    /// process heap drops — not zero times (we'd be leaking the
    /// payload), and not twice (we'd be double-freeing).
    #[test]
    fn aliasing_in_one_process_fires_dtor_once() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_alias_once() do
  r1 = make_resource(7, &dwrap/1)
  r2 = r1
  r3 = r2
  # Three names, one off-heap Resource. Until heap drop, refcount is 1.
  assert(true)
end
"#;
        test_runner::run_str(src).expect("test_runner run_str succeeded");
        super::interp_reset_state();

        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            1,
            "aliasing three bindings must still produce exactly one dtor call",
        );
        // fz-4mk — dtor dispatches as fz code, extern unboxes (see
        // make_resource_bif_round_trip).
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            7,
            "dtor receives the unboxed int payload",
        );
    }

    /// fz-swt.9 acceptance — two *distinct* `make_resource` calls each
    /// fire their dtor exactly once. Confirms we're counting allocations,
    /// not bindings, and that the MSO sweep walks the chain correctly
    /// when it contains more than one Resource stub.
    #[test]
    fn two_distinct_resources_each_fire_once() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        let src = r#"
extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)
fn test_two_resources() do
  a = make_resource(11, &dwrap/1)
  b = make_resource(22, &dwrap/1)
  assert(true)
end
"#;
        test_runner::run_str(src).expect("test_runner run_str succeeded");
        super::interp_reset_state();

        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            2,
            "two distinct make_resource calls must each fire their dtor once",
        );
    }

    /// fz-swt.8 acceptance — `.value` round-trip through the interp.
    ///
    /// `get/1` lives in module `R` (the declaring module of the opaque
    /// alias `t`) and returns `h.value`. The test invokes it from a
    /// `test_*` fn — also in `R` — to satisfy the opaque-visibility
    /// gate. The handle is constructed via `make_resource(99, ...)`;
    /// after `.value` the interp must read back the raw `99` payload.
    #[test]
    fn value_accessor_round_trip_in_interp() {
        let _g = super::tests_support_lock()
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        tests_support::DTOR_FIRED.store(0, Ordering::Relaxed);
        tests_support::DTOR_LAST_PAYLOAD.store(0, Ordering::Relaxed);

        // Note: test fns must live at top level (the test_runner only
        // discovers `test_*` fns by their FINAL segment). We therefore
        // keep the dtor wrapper, the resource ctor wrapper, the
        // accessor and the assertion at top-level too, and rely on
        // the opaque alias being a top-level (unqualified) tag — its
        // visibility gate trivially passes (no owner module). This
        // exercises the runtime read path (`fz_map_get` recognising
        // `TAG_RESOURCE`) end-to-end; the visibility gate is
        // covered by the typer-side unit tests above.
        // Declaring module `R` wraps the opaque alias + accessor; the
        // dtor wrapper and the `test_*` entry stay at top level (the
        // test_runner only discovers `test_*` fns by their FINAL
        // segment, and item-macros inside a `defmodule` body produce
        // bare-named fns per fz-ul4.16.5). `get_value` lives inside
        // `R`, where the visibility gate accepts the `.value` access.
        // `test_value_round_trip` calls `R.get_value` from top level
        // — visibility is irrelevant on the call site, only on the
        // `.value` syntax itself.
        let src = r#"
defmodule R do
  @type t :: opaque resource(integer)

  fn get_value(h), do: h.value
end

extern "C" fn _resource_test_dtor(integer) :: nil
fn dwrap(x), do: _resource_test_dtor(x)

fn test_value_round_trip() do
  r = make_resource(99, &dwrap/1)
  assert_eq(R.get_value(r), 99)
end
"#;
        crate::test_runner::run_str(src).expect("test_runner run_str succeeded");
        // Clean up; verify the dtor fired exactly once with payload 99
        // (LegacyTaggedWord bits) once the process heap drops.
        super::interp_reset_state();
        assert_eq!(
            tests_support::DTOR_FIRED.load(Ordering::Relaxed),
            1,
            "dtor fires once on heap drop",
        );
        // fz-4mk — see make_resource_bif_round_trip; dtor sees unboxed.
        assert_eq!(
            tests_support::DTOR_LAST_PAYLOAD.load(Ordering::Relaxed),
            99,
            "dtor receives the unboxed int payload",
        );
    }
}

// ----- fz-yxs/fz-2v3 — selective receive interp tests -----

#[cfg(test)]
mod receive_tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        crate::ir_lower::lower_program(&mut crate::types::ConcreteTypes, &prog).expect("lower")
    }

    fn run_and_capture(src: &str) -> Result<String, String> {
        let m = lower_src(src);
        let _ = fz_runtime::ir_runtime::test_capture_take();
        run_main(&crate::telemetry::NullTelemetry, &m)?;
        Ok(fz_runtime::ir_runtime::test_capture_take().join("\n"))
    }

    /// Initial-scan hit: the message is already in the mailbox at the
    /// point the receive runs (self-send then receive).
    #[test]
    fn initial_scan_pinned_match() {
        let src = r#"
            fn main() do
              ref = make_ref()
              send(self(), {:reply, ref, 7})
              v = receive do
                {:reply, ^ref, val} -> val
              end
              print(v)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains("7"), "expected 7, got: {}", out);
    }

    /// Sender-side probe hit: receiver parks, then a sender delivers a
    /// matching message; the sender-side probe wakes the receiver with
    /// the matched body.
    #[test]
    fn sender_side_probe_match() {
        let src = r#"
            fn child(parent) do
              send(parent, {:reply, :tag, 99})
            end
            fn main() do
              me = self()
              spawn(fn () -> child(me))
              v = receive do
                {:reply, :tag, val} -> val
              end
              print(v)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains("99"), "expected 99, got: {}", out);
    }

    /// `after 0` fires the after body when nothing in the mailbox matches.
    #[test]
    fn after_zero_fires_immediately_on_empty_mailbox() {
        let src = r#"
            fn main() do
              v = receive do
                {:never, _} -> 11
              after 0 -> 12
              end
              print(v)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains("12"), "expected 12, got: {}", out);
    }

    /// Receiver-side scan finds a message left in the mailbox by an
    /// earlier `receive` that skipped it.
    #[test]
    fn receiver_scan_finds_earlier_skipped_message() {
        let src = r#"
            fn main() do
              me = self()
              send(me, {:a, 1})
              send(me, {:b, 2})
              vb = receive do
                {:b, x} -> x
              end
              va = receive do
                {:a, x} -> x
              end
              print(va + vb)
            end
        "#;
        let out = run_and_capture(src).expect("interp run");
        assert!(out.contains("3"), "expected 3, got: {}", out);
    }

    #[test]
    fn receive_reuses_lowered_matcher_during_interp_probes() {
        use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

        let src = r#"
            fn main() do
              me = self()
              send(me, {:skip, 0})
              send(me, {:skip, 1})
              send(me, {:hit, 2})
              v = receive do
                {:hit, x} -> x
              end
              print(v)
            end
        "#;
        let m = lower_src(src);
        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&["fz", "interp", "receive"], cap.handler());
        crate::pattern_matrix::reset_compile_count();
        let _ = fz_runtime::ir_runtime::test_capture_take();
        super::run_main(&tel, &m).expect("interp run");
        let out = fz_runtime::ir_runtime::test_capture_take().join("\n");
        assert!(out.contains("2"), "expected 2, got: {}", out);
        assert_eq!(
            cap.count(&["fz", "interp", "receive", "probe_miss"]),
            2,
            "two skipped mailbox messages should be observed as receive matcher misses"
        );
        let hits = cap.find(&["fz", "interp", "receive", "probe_hit"]);
        assert_eq!(hits.len(), 1, "exactly one receive matcher hit expected");
        let hit = &hits[0];
        assert!(matches!(
            hit.measurements.get("clause_idx"),
            Some(Value::U64(0))
        ));
        assert!(matches!(
            hit.measurements.get("bound_count"),
            Some(Value::U64(1))
        ));
        assert_eq!(
            crate::pattern_matrix::compile_count(),
            0,
            "interp receive probes must reuse the lowered Matcher instead of recompiling per message"
        );
    }

    #[test]
    fn receive_map_probe_uses_matcher_without_ast_pattern_walk() {
        let src = r#"
            fn main() do
              me = self()
              send(me, :skip)
              send(me, %{name: 42, age: 30})
              v = receive do
                %{name: n} -> n
              end
              print(v)
            end
        "#;
        let m = lower_src(src);
        let _ = fz_runtime::ir_runtime::test_capture_take();
        super::run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run");
        let out = fz_runtime::ir_runtime::test_capture_take().join("\n");
        assert!(out.contains("42"), "expected 42, got: {}", out);
    }

    #[test]
    fn receive_map_pattern_matches_present_nil_value() {
        let src = r#"
            fn main() do
              me = self()
              send(me, %{other: 1})
              send(me, %{name: nil})
              send(me, %{name: :later})
              v = receive do
                %{name: n} -> n
              end
              print(v)
            end
        "#;
        let m = lower_src(src);
        let _ = fz_runtime::ir_runtime::test_capture_take();
        super::run_main(&crate::telemetry::NullTelemetry, &m).expect("interp run");
        let out = fz_runtime::ir_runtime::test_capture_take().join("\n");
        assert_eq!(out, "nil", "present nil map value must match, got: {}", out);
    }

    /// fixtures/receive_selective_refs/input.fz — the design proof point
    /// for fz-recv: sender-side miss, sender-side hit, and receiver-side
    /// scan hit in a single trace. See docs/receive-matched-stress-test.html.
    #[test]
    fn fixture_receive_selective_refs() {
        let src = std::fs::read_to_string("fixtures/receive_selective_refs/input.fz")
            .expect("read fixture");
        let out = run_and_capture(&src).expect("interp run");
        assert!(out.contains("3"), "expected 3, got: {}", out);
    }
}
