//! Immutable finite programs for runtime value predicates.
//!
//! A program is metadata, not a runtime value: nodes hold only immediate
//! values and indices into the program's edge table. It can therefore live in
//! compiled static data and never participates in process-heap tracing.

use crate::any_value::{AnyValueRef, ValueKind, struct_schema_id};
use crate::heap::{SchemaIdentity, list_head_ref, list_tail_ref};
use crate::process::Process;
use std::collections::{HashMap, VecDeque};
use std::marker::PhantomData;
use std::sync::Arc;

pub const RUNTIME_PREDICATE_PROGRAM_ABI_VERSION: u32 = 1;

const OP_TRUE: u8 = 0;
const OP_FALSE: u8 = 1;
const OP_TAG: u8 = 2;
const OP_ATOM: u8 = 3;
const OP_ANY_OF: u8 = 4;
const OP_ALL_OF: u8 = 5;
const OP_LIST_EMPTY: u8 = 6;
const OP_LIST_CONS: u8 = 7;
const OP_TUPLE: u8 = 8;

/// One POD node in a [`RuntimePredicateProgramStatic`] table.
///
/// `first_edge..first_edge + edge_count` indexes the program's `u32` edge
/// table. `payload` is opcode-specific: a [`ValueKind`] tag for `tag`, an atom
/// id for `atom`, and an arity for `tuple`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimePredicateNode {
    opcode: u8,
    reserved: [u8; 3],
    first_edge: u32,
    edge_count: u32,
    payload: u64,
}

impl RuntimePredicateNode {
    pub fn true_() -> Self {
        Self::terminal(OP_TRUE, 0)
    }

    pub fn false_() -> Self {
        Self::terminal(OP_FALSE, 0)
    }

    pub fn tag(kind: ValueKind) -> Self {
        Self::terminal(OP_TAG, u64::from(kind.tag()))
    }

    pub fn atom(atom_id: u32) -> Self {
        Self::terminal(OP_ATOM, u64::from(atom_id))
    }

    pub fn any_of(first_edge: u32, edge_count: u32) -> Self {
        Self::with_edges(OP_ANY_OF, first_edge, edge_count, 0)
    }

    pub fn all_of(first_edge: u32, edge_count: u32) -> Self {
        Self::with_edges(OP_ALL_OF, first_edge, edge_count, 0)
    }

    pub fn list_empty() -> Self {
        Self::terminal(OP_LIST_EMPTY, 0)
    }

    pub fn list_cons(first_edge: u32) -> Self {
        Self::with_edges(OP_LIST_CONS, first_edge, 2, 0)
    }

    pub fn tuple(arity: u32, first_edge: u32, edge_count: u32) -> Self {
        Self::with_edges(OP_TUPLE, first_edge, edge_count, u64::from(arity))
    }

    fn terminal(opcode: u8, payload: u64) -> Self {
        Self::with_edges(opcode, 0, 0, payload)
    }

    fn with_edges(opcode: u8, first_edge: u32, edge_count: u32, payload: u64) -> Self {
        Self {
            opcode,
            reserved: [0; 3],
            first_edge,
            edge_count,
            payload,
        }
    }
}

/// The C/static-data ABI consumed by `fz_runtime_predicate_program_matches`.
///
/// A compiler owns this header and its two read-only tables for as long as any
/// generated code can pass its address to the runtime. Its tables contain no
/// process-heap references, so the garbage collector neither traces nor moves
/// them. The pointer fields are valid for their stated counts; zero-length
/// tables may use a null pointer.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct RuntimePredicateProgramStatic {
    abi_version: u32,
    root: u32,
    nodes: *const RuntimePredicateNode,
    node_count: usize,
    edges: *const u32,
    edge_count: usize,
}

impl RuntimePredicateProgramStatic {
    /// View static data emitted by a compiler which obeys this ABI.
    ///
    /// # Safety
    ///
    /// The node and edge pointers must remain readable for the returned
    /// view's use, with their corresponding counts. This is exactly the
    /// ownership contract of generated static data.
    pub unsafe fn from_raw_parts(
        root: u32,
        nodes: *const RuntimePredicateNode,
        node_count: usize,
        edges: *const u32,
        edge_count: usize,
    ) -> Self {
        Self {
            abi_version: RUNTIME_PREDICATE_PROGRAM_ABI_VERSION,
            root,
            nodes,
            node_count,
            edges,
            edge_count,
        }
    }

    /// # Safety
    ///
    /// The header and its tables must still satisfy the lifetime contract of
    /// [`Self::from_raw_parts`].
    pub unsafe fn matches(self, process: &Process, value: AnyValueRef) -> Result<bool, RuntimePredicateProgramError> {
        let program = self.borrow()?;
        Ok(program.matches(process, value))
    }

    fn borrow(self) -> Result<RuntimePredicateProgramView<'static>, RuntimePredicateProgramError> {
        if self.abi_version != RUNTIME_PREDICATE_PROGRAM_ABI_VERSION {
            return Err(RuntimePredicateProgramError::UnsupportedAbiVersion(self.abi_version));
        }
        // The caller that produced this C ABI view owns the backing static
        // data. `borrow` does not extend that ownership; the `'static` here
        // models the ABI requirement, which `from_raw_parts` makes explicit.
        let nodes = unsafe { static_slice(self.nodes, self.node_count)? };
        let edges = unsafe { static_slice(self.edges, self.edge_count)? };
        RuntimePredicateProgramView {
            root: self.root,
            nodes,
            edges,
        }
        .validate()
    }
}

unsafe fn static_slice<T>(ptr: *const T, len: usize) -> Result<&'static [T], RuntimePredicateProgramError> {
    if len == 0 {
        return Ok(&[]);
    }
    if ptr.is_null() {
        return Err(RuntimePredicateProgramError::NullStaticTable);
    }
    Ok(unsafe { std::slice::from_raw_parts(ptr, len) })
}

/// An owned runtime predicate artifact. Clones share the same immutable tables
/// and keep them alive until the last owner is released.
#[derive(Clone, Debug)]
pub struct RuntimePredicateProgram {
    storage: Arc<RuntimePredicateProgramStorage>,
}

#[derive(Debug)]
struct RuntimePredicateProgramStorage {
    root: u32,
    nodes: Box<[RuntimePredicateNode]>,
    edges: Box<[u32]>,
}

/// A static ABI header whose borrow cannot outlive its owning program.
pub struct RuntimePredicateProgramStaticView<'a> {
    header: RuntimePredicateProgramStatic,
    owner: PhantomData<&'a RuntimePredicateProgramStorage>,
}

impl RuntimePredicateProgramStaticView<'_> {
    pub fn matches(&self, process: &Process, value: AnyValueRef) -> Result<bool, RuntimePredicateProgramError> {
        unsafe { self.header.matches(process, value) }
    }

    pub fn as_ptr(&self) -> *const RuntimePredicateProgramStatic {
        &self.header
    }
}

impl RuntimePredicateProgram {
    pub fn new(
        root: u32,
        nodes: Vec<RuntimePredicateNode>,
        edges: Vec<u32>,
    ) -> Result<Self, RuntimePredicateProgramError> {
        let storage = RuntimePredicateProgramStorage {
            root,
            nodes: nodes.into_boxed_slice(),
            edges: edges.into_boxed_slice(),
        };
        RuntimePredicateProgramView {
            root: storage.root,
            nodes: &storage.nodes,
            edges: &storage.edges,
        }
        .validate()?;
        Ok(Self {
            storage: Arc::new(storage),
        })
    }

    pub fn static_data(&self) -> RuntimePredicateProgramStaticView<'_> {
        RuntimePredicateProgramStaticView {
            header: RuntimePredicateProgramStatic {
                abi_version: RUNTIME_PREDICATE_PROGRAM_ABI_VERSION,
                root: self.storage.root,
                nodes: self.storage.nodes.as_ptr(),
                node_count: self.storage.nodes.len(),
                edges: self.storage.edges.as_ptr(),
                edge_count: self.storage.edges.len(),
            },
            owner: PhantomData,
        }
    }

    pub fn matches(&self, process: &Process, value: AnyValueRef) -> bool {
        RuntimePredicateProgramView {
            root: self.storage.root,
            nodes: &self.storage.nodes,
            edges: &self.storage.edges,
        }
        .matches(process, value)
    }
}

/// The runtime entry generated code calls with a pointer to its immutable
/// predicate-program header. A malformed program or value answers false; a
/// compiler-generated header is validated when its owner builds it.
///
/// # Safety
///
/// `process` must name a live process and `program` must name a live header
/// whose tables obey [`RuntimePredicateProgramStatic::from_raw_parts`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_runtime_predicate_program_matches(
    process: *const Process,
    value_word: u64,
    program: *const RuntimePredicateProgramStatic,
) -> u8 {
    if process.is_null() || program.is_null() {
        return 0;
    }
    let Ok(value) = AnyValueRef::from_raw_word(value_word) else {
        return 0;
    };
    let process = unsafe { &*process };
    let program = unsafe { *program };
    u8::from(unsafe { program.matches(process, value) }.unwrap_or(false))
}

#[derive(Clone, Copy)]
struct RuntimePredicateProgramView<'a> {
    root: u32,
    nodes: &'a [RuntimePredicateNode],
    edges: &'a [u32],
}

impl RuntimePredicateProgramView<'_> {
    fn validate(self) -> Result<Self, RuntimePredicateProgramError> {
        let root = usize::try_from(self.root).expect("u32 fits usize");
        if root >= self.nodes.len() {
            return Err(RuntimePredicateProgramError::InvalidRoot(self.root));
        }
        for (index, node) in self.nodes.iter().enumerate() {
            let opcode = Opcode::from_raw(node.opcode).ok_or(RuntimePredicateProgramError::UnknownOpcode {
                node: index as u32,
                opcode: node.opcode,
            })?;
            let edges = self.edges_for(index as u32, node)?;
            match opcode {
                Opcode::True | Opcode::False | Opcode::Atom | Opcode::ListEmpty => require_edge_count(index, edges, 0)?,
                Opcode::Tag => {
                    require_edge_count(index, edges, 0)?;
                    let Some(tag) = u8::try_from(node.payload).ok().and_then(ValueKind::new) else {
                        return Err(RuntimePredicateProgramError::InvalidTag {
                            node: index as u32,
                            tag: node.payload,
                        });
                    };
                    if u64::from(tag.tag()) != node.payload {
                        return Err(RuntimePredicateProgramError::InvalidTag {
                            node: index as u32,
                            tag: node.payload,
                        });
                    }
                }
                Opcode::AnyOf | Opcode::AllOf => {}
                Opcode::ListCons => require_edge_count(index, edges, 2)?,
                Opcode::Tuple => {
                    let arity = usize::try_from(node.payload).map_err(|_| {
                        RuntimePredicateProgramError::TupleArityOverflow {
                            node: index as u32,
                            arity: node.payload,
                        }
                    })?;
                    require_edge_count(index, edges, arity)?;
                }
            }
            for &child in edges {
                if child as usize >= self.nodes.len() {
                    return Err(RuntimePredicateProgramError::InvalidEdge {
                        node: index as u32,
                        child,
                    });
                }
            }
        }
        Ok(self)
    }

    fn edges_for(&self, node_index: u32, node: &RuntimePredicateNode) -> Result<&[u32], RuntimePredicateProgramError> {
        let start = node.first_edge as usize;
        let len = node.edge_count as usize;
        let end = start
            .checked_add(len)
            .ok_or(RuntimePredicateProgramError::EdgeRangeOverflow { node: node_index })?;
        self.edges
            .get(start..end)
            .ok_or(RuntimePredicateProgramError::EdgeRangeOutOfBounds { node: node_index })
    }

    fn matches(&self, process: &Process, value: AnyValueRef) -> bool {
        let mut states = Vec::new();
        let mut state_ids = HashMap::new();
        let root = self.intern_state(self.root, value, &mut states, &mut state_ids);
        let mut next = 0;
        while next < states.len() {
            let (node, value) = {
                let state = &states[next];
                (state.node, state.value)
            };
            let formula = self.formula(process, node, value, &mut states, &mut state_ids);
            states[next].formula = formula;
            next += 1;
        }
        solve(&mut states, root)
    }

    fn intern_state(
        &self,
        node: u32,
        value: AnyValueRef,
        states: &mut Vec<EvaluationState>,
        state_ids: &mut HashMap<EvaluationKey, usize>,
    ) -> usize {
        let key = EvaluationKey {
            node,
            value: value.raw_word(),
        };
        if let Some(&state) = state_ids.get(&key) {
            return state;
        }
        let state = states.len();
        state_ids.insert(key, state);
        states.push(EvaluationState {
            node,
            value,
            formula: Formula::False,
        });
        state
    }

    fn formula(
        &self,
        process: &Process,
        node_index: u32,
        value: AnyValueRef,
        states: &mut Vec<EvaluationState>,
        state_ids: &mut HashMap<EvaluationKey, usize>,
    ) -> Formula {
        let node = &self.nodes[node_index as usize];
        let opcode = Opcode::from_raw(node.opcode).expect("validated program opcode");
        let edges = self.edges_for(node_index, node).expect("validated program edge range");
        match opcode {
            Opcode::True => Formula::True,
            Opcode::False => Formula::False,
            Opcode::Tag => Formula::from_bool(value.tag().tag() == node.payload as u8),
            Opcode::Atom => Formula::from_bool(value.load_atom() == Ok(node.payload)),
            Opcode::AnyOf => self.children_formula(edges, value, FormulaKind::Any, states, state_ids),
            Opcode::AllOf => self.children_formula(edges, value, FormulaKind::All, states, state_ids),
            Opcode::ListEmpty => Formula::from_bool(value.is_empty_list()),
            Opcode::ListCons => {
                let Ok(head) = list_head_ref(value) else {
                    return Formula::False;
                };
                let Ok(tail) = list_tail_ref(value) else {
                    return Formula::False;
                };
                Formula::All(vec![
                    self.intern_state(edges[0], head, states, state_ids),
                    self.intern_state(edges[1], tail, states, state_ids),
                ])
            }
            Opcode::Tuple => {
                let Ok(address) = value.struct_addr() else {
                    return Formula::False;
                };
                let schema_id = unsafe { struct_schema_id(address.cast_const()) };
                let arity = usize::try_from(node.payload).expect("validated tuple arity");
                {
                    let schemas = process.heap.schemas_registry();
                    let schemas = schemas.borrow();
                    if !matches!(schemas.get(schema_id).identity, SchemaIdentity::Tuple(found) if found == arity) {
                        return Formula::False;
                    }
                }
                let mut children = Vec::with_capacity(arity);
                for (field, &child) in edges.iter().enumerate() {
                    let Ok(field_value) = process.heap.read_struct_field_ref(value, (field * 8) as u32) else {
                        return Formula::False;
                    };
                    children.push(self.intern_state(child, field_value, states, state_ids));
                }
                Formula::All(children)
            }
        }
    }

    fn children_formula(
        &self,
        edges: &[u32],
        value: AnyValueRef,
        kind: FormulaKind,
        states: &mut Vec<EvaluationState>,
        state_ids: &mut HashMap<EvaluationKey, usize>,
    ) -> Formula {
        let children = edges
            .iter()
            .map(|&child| self.intern_state(child, value, states, state_ids))
            .collect();
        match kind {
            FormulaKind::Any => Formula::Any(children),
            FormulaKind::All => Formula::All(children),
        }
    }
}

fn require_edge_count(node: usize, edges: &[u32], expected: usize) -> Result<(), RuntimePredicateProgramError> {
    if edges.len() == expected {
        Ok(())
    } else {
        Err(RuntimePredicateProgramError::InvalidEdgeCount {
            node: node as u32,
            expected,
            actual: edges.len(),
        })
    }
}

fn solve(states: &mut [EvaluationState], root: usize) -> bool {
    let mut parents = vec![Vec::new(); states.len()];
    let mut remaining_all = vec![0usize; states.len()];
    let mut ready = VecDeque::new();

    for (parent, state) in states.iter().enumerate() {
        match &state.formula {
            Formula::True => ready.push_back(parent),
            Formula::False => {}
            Formula::Any(children) => {
                for &child in children {
                    parents[child].push(parent);
                }
            }
            Formula::All(children) => {
                remaining_all[parent] = children.len();
                if children.is_empty() {
                    ready.push_back(parent);
                }
                for &child in children {
                    parents[child].push(parent);
                }
            }
        }
    }

    let mut true_states = vec![false; states.len()];
    while let Some(state) = ready.pop_front() {
        if true_states[state] {
            continue;
        }
        true_states[state] = true;
        for &parent in &parents[state] {
            match states[parent].formula {
                Formula::Any(_) => ready.push_back(parent),
                Formula::All(_) => {
                    remaining_all[parent] -= 1;
                    if remaining_all[parent] == 0 {
                        ready.push_back(parent);
                    }
                }
                Formula::True | Formula::False => unreachable!("terminal state has no child"),
            }
        }
    }
    true_states[root]
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct EvaluationKey {
    node: u32,
    value: u64,
}

struct EvaluationState {
    node: u32,
    value: AnyValueRef,
    formula: Formula,
}

enum Formula {
    True,
    False,
    Any(Vec<usize>),
    All(Vec<usize>),
}

impl Formula {
    fn from_bool(value: bool) -> Self {
        if value { Self::True } else { Self::False }
    }
}

#[derive(Clone, Copy)]
enum FormulaKind {
    Any,
    All,
}

#[derive(Clone, Copy)]
enum Opcode {
    True,
    False,
    Tag,
    Atom,
    AnyOf,
    AllOf,
    ListEmpty,
    ListCons,
    Tuple,
}

impl Opcode {
    fn from_raw(raw: u8) -> Option<Self> {
        Some(match raw {
            OP_TRUE => Self::True,
            OP_FALSE => Self::False,
            OP_TAG => Self::Tag,
            OP_ATOM => Self::Atom,
            OP_ANY_OF => Self::AnyOf,
            OP_ALL_OF => Self::AllOf,
            OP_LIST_EMPTY => Self::ListEmpty,
            OP_LIST_CONS => Self::ListCons,
            OP_TUPLE => Self::Tuple,
            _ => return None,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimePredicateProgramError {
    UnsupportedAbiVersion(u32),
    NullStaticTable,
    InvalidRoot(u32),
    UnknownOpcode { node: u32, opcode: u8 },
    InvalidTag { node: u32, tag: u64 },
    EdgeRangeOverflow { node: u32 },
    EdgeRangeOutOfBounds { node: u32 },
    InvalidEdge { node: u32, child: u32 },
    InvalidEdgeCount { node: u32, expected: usize, actual: usize },
    TupleArityOverflow { node: u32, arity: u64 },
}

#[cfg(test)]
#[path = "predicate_program_test.rs"]
mod predicate_program_test;
