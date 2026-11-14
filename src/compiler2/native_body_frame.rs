//! One frame per body.
//!
//! A body with N non-tail calls is cut into N continuations, one per call. A
//! continuation built at exactly one site, by another continuation, resumes
//! in its builder's frame: the builder writes the values that are new at the
//! site into empty slots of the frame it runs in and hands that same frame on
//! as the continuation, and the member reads the values it uses back out of
//! it. The first continuation of such a chain, the root, is built with a slot
//! for every value the chain holds, so the body's values are written once and
//! read where they are used, however many calls the body makes.
//!
//! A continuation entered any other way -- built at two or more sites (a
//! join), reached by a direct call, a closure, a protocol, a `try` handler or a
//! `receive` -- starts no chain inside another one.

use crate::fast_hash::{HashMap, HashSet};
use crate::fz_ir::{Block, DirectCallTarget, FnId, FnIr, FrameLane, Prim, Stmt, Term, Var};
use crate::ir_dce::classify_var_uses;
use crate::source::Span;

use super::artifact::{AbiValueRepr, BodyFrame, FrameRole, NativeBodyOrigin, NativeEntryAbi, NativeProgram};
use super::types::Ty;

/// Where a continuation is built: the terminator of `block` in `builder`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Site {
    builder: FnId,
    block: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Slot {
    index: u32,
    lane: FrameLane,
}

/// Lays out every body frame of `program` and rewrites its continuations to
/// run in them. `any` types the frame values the rewrite introduces.
pub(crate) fn frame_bodies(program: &mut NativeProgram, any: Ty) {
    let bodies: HashMap<FnId, usize> = program
        .bodies
        .iter()
        .enumerate()
        .map(|(index, body)| (body.fn_id, index))
        .collect();
    let sites = ConstructionSites::of(program);
    let mut layout = FrameLayout::default();
    for function in &program.module.fns {
        layout.place_chain_to(program, &bodies, &sites, function.id);
    }
    layout.apply(program, &bodies, any)
}

fn lane_of(repr: AbiValueRepr) -> FrameLane {
    match repr {
        AbiValueRepr::ValueRef => FrameLane::Ref,
        AbiValueRepr::RawInt => FrameLane::Int,
        AbiValueRepr::RawF64 => FrameLane::Float,
        AbiValueRepr::RawAtom => FrameLane::Atom,
    }
}

/// The values a site hands to the continuation it builds, after the
/// `extra` values the continuation receives when it resumes.
fn site_captures(term: &Term, extra: usize) -> Option<&[Var]> {
    match term {
        Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => Some(&continuation.captured),
        Term::TailCall { args, .. } => args.get(extra..),
        _ => None,
    }
}

/// Every site that builds each continuation, and the functions entered some
/// other way.
struct ConstructionSites {
    built_at: HashMap<FnId, Vec<Site>>,
    entered_elsewhere: HashSet<FnId>,
    extra_params: HashMap<FnId, usize>,
}

impl ConstructionSites {
    fn of(program: &NativeProgram) -> Self {
        let mut sites = Self {
            built_at: HashMap::default(),
            entered_elsewhere: HashSet::default(),
            extra_params: program
                .bodies
                .iter()
                .filter_map(|body| match (&body.entry_abi, &body.origin) {
                    (NativeEntryAbi::Continuation { extra_params }, NativeBodyOrigin::Continuation { .. }) => {
                        Some((body.fn_id, *extra_params))
                    }
                    _ => None,
                })
                .collect(),
        };
        sites.entered_elsewhere.insert(program.entry);
        sites
            .entered_elsewhere
            .extend(program.executable_entries.iter().map(|entry| entry.fn_id));
        for boundary in &program.callable_boundaries {
            sites.entered_elsewhere.insert(boundary.identity_fn);
            sites.entered_elsewhere.insert(boundary.wrapper_fn);
        }
        sites
            .entered_elsewhere
            .extend(program.module.protocol_call_targets.keys().copied());
        for function in &program.module.fns {
            for (block_index, block) in function.blocks.iter().enumerate() {
                let site = Site {
                    builder: function.id,
                    block: block_index,
                };
                sites.note_stmts(&block.stmts);
                sites.note_terminator(&block.terminator, site);
            }
        }
        sites
    }

    fn note_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            if let Prim::MakeFnRef(_, id) | Prim::MakeClosure(_, id, _) = stmt.prim() {
                self.entered_elsewhere.insert(*id);
            }
        }
    }

    fn note_terminator(&mut self, term: &Term, site: Site) {
        match term {
            Term::Call {
                callee, continuation, ..
            } => {
                if let DirectCallTarget::Local(id) = callee {
                    self.entered_elsewhere.insert(*id);
                }
                self.built_at.entry(continuation.fn_id).or_default().push(site);
            }
            Term::CallClosure { continuation, .. } => {
                self.built_at.entry(continuation.fn_id).or_default().push(site);
            }
            Term::TailCall {
                callee: DirectCallTarget::Local(id),
                ..
            } => self.built_at.entry(*id).or_default().push(site),
            Term::Try { handler, .. } => {
                self.entered_elsewhere.insert(*handler);
            }
            Term::ReceiveMatched { clauses, after, .. } => {
                for clause in clauses {
                    self.entered_elsewhere.extend(clause.guard);
                    self.entered_elsewhere.insert(clause.body);
                }
                if let Some(after) = after {
                    self.entered_elsewhere.insert(after.body);
                }
            }
            _ => {}
        }
    }

    fn is_continuation(&self, fn_id: FnId) -> bool {
        self.extra_params.contains_key(&fn_id)
    }

    /// The one site that builds `fn_id`, when that site is in another
    /// continuation and nothing else enters `fn_id`.
    fn sole_builder(&self, fn_id: FnId) -> Option<Site> {
        if !self.is_continuation(fn_id) || self.entered_elsewhere.contains(&fn_id) {
            return None;
        }
        match self.built_at.get(&fn_id)?.as_slice() {
            [site] if site.builder != fn_id && self.is_continuation(site.builder) => Some(*site),
            _ => None,
        }
    }

    /// Every site of `fn_id` hands it exactly its captures, so each can build
    /// its descriptor with the frame's slots beyond them.
    fn every_site_builds(&self, program: &NativeProgram, fn_id: FnId, captures: usize) -> bool {
        let extra = self.extra_params[&fn_id];
        self.built_at.get(&fn_id).is_some_and(|sites| {
            sites.iter().all(|site| {
                let term = &program.module.fn_by_id(site.builder).blocks[site.block].terminator;
                site_captures(term, extra).is_some_and(|captured| captured.len() == captures)
            })
        })
    }
}

/// The slots each placed continuation holds, and the writes and reads that put
/// its values there.
#[derive(Default)]
struct FrameLayout {
    frames: HashMap<FnId, PlacedFrame>,
    root_slots: HashMap<FnId, u32>,
    joins: Vec<Join>,
    not_members: HashSet<FnId>,
    not_roots: HashSet<FnId>,
}

struct PlacedFrame {
    root: FnId,
    held: HashMap<Var, Slot>,
}

/// One member joining its builder's frame.
struct Join {
    member: FnId,
    site: Site,
    extra: usize,
    stores: Vec<(Var, Slot)>,
    clears: Vec<u32>,
    loads: Vec<(Var, Slot)>,
}

impl FrameLayout {
    /// Places `fn_id` and every unplaced builder above it, builders first.
    fn place_chain_to(
        &mut self,
        program: &NativeProgram,
        bodies: &HashMap<FnId, usize>,
        sites: &ConstructionSites,
        fn_id: FnId,
    ) {
        let mut chain: Vec<(FnId, Site)> = Vec::new();
        let mut cursor = fn_id;
        while !self.frames.contains_key(&cursor) && !self.not_members.contains(&cursor) {
            let Some(site) = sites.sole_builder(cursor) else {
                break;
            };
            if chain.iter().any(|(member, _)| *member == cursor) {
                self.not_members.extend(chain.iter().map(|(member, _)| *member));
                return;
            }
            chain.push((cursor, site));
            cursor = site.builder;
        }
        for (member, site) in chain.into_iter().rev() {
            self.place(program, bodies, sites, member, site);
        }
    }

    fn place(
        &mut self,
        program: &NativeProgram,
        bodies: &HashMap<FnId, usize>,
        sites: &ConstructionSites,
        member: FnId,
        site: Site,
    ) {
        let extra = sites.extra_params[&member];
        let builder_term = &program.module.fn_by_id(site.builder).blocks[site.block].terminator;
        let captured = site_captures(builder_term, extra).expect("a member's site builds it");
        let reprs = &program.bodies[bodies[&member]].param_reprs;
        let Some(params) = member_params(program, member, extra, reprs, captured.len()) else {
            self.not_members.insert(member);
            return;
        };
        if !self.frames.contains_key(&site.builder) && !self.start_frame(program, bodies, sites, site.builder) {
            self.not_members.insert(member);
            return;
        }
        let builder = &self.frames[&site.builder];
        let root = builder.root;
        let mut join = Join {
            member,
            site,
            extra,
            stores: Vec::new(),
            clears: Vec::new(),
            loads: Vec::new(),
        };
        let mut held = HashMap::default();
        for (position, var) in captured.iter().enumerate() {
            let lane = lane_of(reprs[extra + position]);
            let slot = match builder.held.get(var) {
                Some(slot) if slot.lane == lane => *slot,
                _ => match join
                    .stores
                    .iter()
                    .find(|(stored, slot)| stored == var && slot.lane == lane)
                {
                    Some((_, slot)) => *slot,
                    None => {
                        let next = self.root_slots.get_mut(&root).expect("a placed frame has a root");
                        let slot = Slot { index: *next, lane };
                        *next += 1;
                        join.stores.push((*var, slot));
                        slot
                    }
                },
            };
            let param = params[extra + position];
            held.insert(param, slot);
            join.loads.push((param, slot));
        }
        join.clears = dead_heap_slots(&builder.held, &held);
        self.joins.push(join);
        self.frames.insert(member, PlacedFrame { root, held });
    }

    /// Starts a frame at `root` when every descriptor of it can be built with
    /// the frame's slots.
    fn start_frame(
        &mut self,
        program: &NativeProgram,
        bodies: &HashMap<FnId, usize>,
        sites: &ConstructionSites,
        root: FnId,
    ) -> bool {
        if self.not_roots.contains(&root) || sites.entered_elsewhere.contains(&root) || !sites.is_continuation(root) {
            return false;
        }
        let extra = sites.extra_params[&root];
        let function = program.module.fn_by_id(root);
        let params = &function.block(function.entry).params;
        let reprs = &program.bodies[bodies[&root]].param_reprs;
        if reprs.len() != params.len()
            || params.len() < extra
            || !sites.every_site_builds(program, root, params.len() - extra)
        {
            self.not_roots.insert(root);
            return false;
        }
        let held = params
            .iter()
            .enumerate()
            .skip(extra)
            .filter(|(_, param)| !function.physical_entry_params.contains(param))
            .map(|(position, param)| {
                let slot = Slot {
                    index: (1 + position - extra) as u32,
                    lane: lane_of(reprs[position]),
                };
                (*param, slot)
            })
            .collect();
        self.root_slots.insert(root, (1 + params.len() - extra) as u32);
        self.frames.insert(root, PlacedFrame { root, held });
        true
    }

    fn apply(self, program: &mut NativeProgram, bodies: &HashMap<FnId, usize>, any: Ty) {
        let mut rewrite = Rewrite::new(program, bodies, any);
        for join in &self.joins {
            rewrite.hand_frame_on(join);
        }
        for join in &self.joins {
            rewrite.resume_in_frame(join);
        }
        for (fn_id, placed) in &self.frames {
            let role = if *fn_id == placed.root {
                FrameRole::Root
            } else {
                FrameRole::Member
            };
            let slots = self.root_slots[&placed.root];
            program.bodies[bodies[fn_id]].frame = Some(BodyFrame { role, slots });
        }
    }
}

/// The entry parameters of `member`, when its site hands it exactly its
/// non-physical parameters after the `extra` ones it resumes with.
fn member_params<'p>(
    program: &'p NativeProgram,
    member: FnId,
    extra: usize,
    reprs: &[AbiValueRepr],
    captured: usize,
) -> Option<&'p [Var]> {
    let function = program.module.fn_by_id(member);
    let params = &function.block(function.entry).params;
    let shaped = reprs.len() == params.len() && params.len() == extra + captured;
    let physical = || {
        params[extra..]
            .iter()
            .any(|param| function.physical_entry_params.contains(param))
    };
    (shaped && !physical()).then_some(params.as_slice())
}

/// The boxed slots the builder holds that the member does not: their values
/// die at the site.
fn dead_heap_slots(builder: &HashMap<Var, Slot>, member: &HashMap<Var, Slot>) -> Vec<u32> {
    let live: HashSet<u32> = member.values().map(|slot| slot.index).collect();
    let mut dead: Vec<u32> = builder
        .values()
        .filter(|slot| slot.lane == FrameLane::Ref && !live.contains(&slot.index))
        .map(|slot| slot.index)
        .collect();
    dead.sort_unstable();
    dead.dedup();
    dead
}

/// The IR edits that make placed continuations run in their frames.
struct Rewrite<'p> {
    program: &'p mut NativeProgram,
    bodies: &'p HashMap<FnId, usize>,
    any: Ty,
    next_var: HashMap<FnId, u32>,
    frame_var: HashMap<FnId, Var>,
}

impl<'p> Rewrite<'p> {
    fn new(program: &'p mut NativeProgram, bodies: &'p HashMap<FnId, usize>, any: Ty) -> Self {
        let next_var = program
            .module
            .fns
            .iter()
            .map(|function| (function.id, first_unused_var(function)))
            .collect();
        Self {
            program,
            bodies,
            any,
            next_var,
            frame_var: HashMap::default(),
        }
    }

    /// The builder writes the values new at the site into the frame, clears
    /// the boxed values that die there, and builds the member as the frame.
    fn hand_frame_on(&mut self, join: &Join) {
        let builder = join.site.builder;
        let mut frame = self.running_frame(builder);
        let mut appended = Vec::new();
        for (value, slot) in &join.stores {
            let next = self.fresh_var(builder);
            let store = Prim::FrameStore {
                frame,
                slot: slot.index,
                lane: slot.lane,
                value: *value,
            };
            appended.push(Stmt::Let(next, store));
            frame = next;
        }
        for slot in &join.clears {
            let next = self.fresh_var(builder);
            appended.push(Stmt::Let(next, Prim::FrameClear { frame, slot: *slot }));
            frame = next;
        }
        let appended_count = appended.len();
        let block = &mut self.function_mut(builder).blocks[join.site.block];
        let block_id = block.id;
        block.stmts.extend(appended);
        match &mut block.terminator {
            Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => {
                continuation.captured = vec![frame];
            }
            Term::TailCall { args, .. } => {
                args.truncate(join.extra);
                args.push(frame);
            }
            _ => unreachable!("a member's site builds it"),
        }
        if let Some(spans) = self.program.module.source.stmt_spans.get_mut(&(builder, block_id)) {
            spans.extend(std::iter::repeat_n(Span::DUMMY, appended_count));
        }
    }

    /// The member receives only what it resumes with, and loads from the
    /// frame the values it uses.
    fn resume_in_frame(&mut self, join: &Join) {
        let frame = self.running_frame(join.member);
        let (_, used) = classify_var_uses(self.program.module.fn_by_id(join.member));
        let loads: Vec<Stmt> = join
            .loads
            .iter()
            .filter(|(param, _)| used.contains(param))
            .map(|(param, slot)| {
                let load = Prim::FrameLoad {
                    frame,
                    slot: slot.index,
                    lane: slot.lane,
                };
                Stmt::Let(*param, load)
            })
            .collect();
        let load_count = loads.len();
        let function = self.function_mut(join.member);
        let entry = function.entry;
        let params_flagged = function.ignored_entry_params.len() == function.block(entry).params.len();
        if params_flagged {
            function.ignored_entry_params.truncate(join.extra);
        }
        let block = entry_block_mut(function);
        block.params.truncate(join.extra);
        block.stmts.splice(1..1, loads);
        if let Some(spans) = self.program.module.source.stmt_spans.get_mut(&(join.member, entry)) {
            spans.splice(1..1, std::iter::repeat_n(Span::DUMMY, load_count));
        }
        self.program.bodies[self.bodies[&join.member]]
            .param_reprs
            .truncate(join.extra);
    }

    /// The variable bound, first thing in `fn_id`, to the frame it runs in.
    fn running_frame(&mut self, fn_id: FnId) -> Var {
        if let Some(frame) = self.frame_var.get(&fn_id) {
            return *frame;
        }
        let frame = self.fresh_var(fn_id);
        let function = self.function_mut(fn_id);
        let entry = function.entry;
        entry_block_mut(function).stmts.insert(0, Stmt::Let(frame, Prim::Frame));
        if let Some(spans) = self.program.module.source.stmt_spans.get_mut(&(fn_id, entry)) {
            spans.insert(0, Span::DUMMY);
        }
        self.frame_var.insert(fn_id, frame);
        frame
    }

    fn fresh_var(&mut self, fn_id: FnId) -> Var {
        let next = self
            .next_var
            .get_mut(&fn_id)
            .expect("every function has a variable supply");
        let var = Var(*next);
        *next += 1;
        self.program.bodies[self.bodies[&fn_id]]
            .value_types
            .insert(var, self.any);
        var
    }

    fn function_mut(&mut self, fn_id: FnId) -> &mut FnIr {
        let index = self.program.module.fn_idx[&fn_id];
        &mut self.program.module.fns[index]
    }
}

fn entry_block_mut(function: &mut FnIr) -> &mut Block {
    let entry = function.entry;
    function
        .blocks
        .iter_mut()
        .find(|block| block.id == entry)
        .expect("a function has its entry block")
}

fn first_unused_var(function: &FnIr) -> u32 {
    let mut next = 0;
    for block in &function.blocks {
        for var in &block.params {
            next = next.max(var.0 + 1);
        }
        for stmt in &block.stmts {
            let defined = match stmt {
                Stmt::Let(var, _) => std::slice::from_ref(var),
                Stmt::LetMany(vars, _) => vars.as_slice(),
            };
            for var in defined {
                next = next.max(var.0 + 1);
            }
        }
    }
    next
}

#[cfg(test)]
#[path = "native_body_frame_test.rs"]
mod native_body_frame_test;
