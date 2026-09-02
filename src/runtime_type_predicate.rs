//! First-class runtime-observable membership predicates.
//!
//! Semantic types remain richer than what the runtime can inspect directly.
//! Backends and the interpreter therefore answer runtime-membership questions
//! by projecting semantic types into this explicit predicate layer.

use crate::finite_set::FiniteSet;
use crate::fz_ir::Module;
use crate::types::ClosureTarget;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind, closure_fn_ptr, struct_schema_id};
use std::collections::{BTreeSet, HashMap};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ListShape {
    Empty,
    NonEmpty,
}

/// Every axis a runtime type test can decide.
///
/// A predicate is a union over these axes and nothing else: a value reaches
/// exactly the axes [`RuntimeTestAxis::of_value`] names for it, so a test is
/// the OR of its axes' answers, containment is the AND of them, and two tests
/// overlap when they overlap on some axis.
///
/// This enum is the ONE table the layer is written against (fz-kdt.119 item
/// 6). [`RuntimeTypePredicate::overlaps_on_an_erasing_axis`] reads
/// [`RuntimeTestAxis::precision`] to decide which axes a dispatch seat may
/// treat as separation, and each of the three lowerings decides the axes by
/// matching on this enum:
///
/// - `ir_interp::backend::select_dispatch_match` through
///   [`matches_runtime_type_predicate`];
/// - `compiler2::native_codegen::prim::lower_runtime_type_predicate` and
///   `compiler2::native_codegen::receive::emit_runtime_type_predicate_region_test`,
///   which share one emitter in `compiler2::native_codegen::runtime_test`.
///
/// All three matches are exhaustive, so an axis cannot join the lattice
/// without every lowering refusing to compile until it is taught to test it.
/// `the_axis_table_names_every_axis_a_predicate_carries` closes the other
/// direction: it rebuilds `any()` out of the table alone, so a field that no
/// axis names cannot hide in the struct either.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RuntimeTestAxis {
    Ints,
    Floats,
    Atoms,
    Lists,
    Tuples,
    NamedStructs,
    OtherStructs,
    Maps,
    Binaries,
    Callables,
    Resources,
}

/// How much a decided axis tells a dispatch SEAT.
///
/// A test is a projection, and what it drops is what a body may still read. An
/// axis whose test admits values it cannot tell apart is where a seat can hand
/// a value to a body that never named it (fz-kdt.131), so seating across it
/// needs the surface-coverage check; an axis that separates does not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AxisPrecision {
    /// Passing this axis' test pins the value down far enough that no body
    /// admitted by it can misread the value.
    Separating,
    /// The test admits values it cannot distinguish, and what it erases is
    /// what a body reads: list elements, struct/map/binary/resource contents.
    Erasing,
    /// Separating exactly as far as the per-position sub-tests separate. A
    /// tuple test carries one sub-predicate per position per shape, so it
    /// separates `{:cont, int}` from `{:halt, int}` and erases the payload of
    /// `{:cont, [int]}` against `{:cont, [:ok]}` (fz-kdt.119). A list test
    /// carries one sub-predicate per cons-admitting clause -- its HEAD -- so
    /// it separates `[:ok]` from `[int]` and erases `[int]` against
    /// `[int | :ok]` (fz-kdt.107 step 3).
    PerPosition,
}

impl RuntimeTestAxis {
    pub(crate) const ALL: [Self; 11] = [
        Self::Ints,
        Self::Floats,
        Self::Atoms,
        Self::Lists,
        Self::Tuples,
        Self::NamedStructs,
        Self::OtherStructs,
        Self::Maps,
        Self::Binaries,
        Self::Callables,
        Self::Resources,
    ];

    /// What deciding this axis is worth to a seat.
    pub(crate) const fn precision(self) -> AxisPrecision {
        match self {
            // Atom membership is VALUE membership: an atom id IS the value,
            // so passing the test is being one of the named values, which the
            // arm's surface names.
            Self::Atoms => AxisPrecision::Separating,
            // Callable membership is IDENTITY membership: the heap word at
            // `+8` names the code a closure was minted from (fz-kdt.125),
            // but a surface can additionally constrain CAPTURES, which the
            // test does not read -- `#66 over int` and `#66 over float` are
            // one test. Separating is honest today only because the
            // same-fn-id/different-capture shape compiles on no path
            // (fz-kdt.127, whose population fz-kdt.119's depth-recursive
            // identity erasure GROWS); if fz-kdt.127 makes that shape
            // compile, this row must be re-judged before it ships.
            Self::Callables => AxisPrecision::Separating,
            // Numbers are PRESENCE BITS here, never value sets: the projection
            // records "INT is present" and drops literals and brands alike
            // (`Types::runtime_type_predicate`). So the reason this axis is
            // safe to seat across is NOT that the surface names the value --
            // two arms whose surfaces are `brand X of int` and `brand Y of
            // int` put the SAME question and hold incomparable surfaces. It is
            // that every value the axis admits has ONE representation: brands
            // are runtime-erased by construction (fz-bsx), so no body admitted
            // here can misread what arrives. Restoring numeric singletons to
            // the lattice would populate `ints.values`/`floats.values` and
            // this row would have to be re-derived with them (fz-kdt.131).
            Self::Ints | Self::Floats => AxisPrecision::Separating,
            // A list test decides empty-or-cons and, where the projection
            // could name the element type, the first element's own question.
            // A list type is HOMOGENEOUS by construction (`ListSig` carries
            // one element type for the whole list), so a head OUTSIDE the
            // element question proves the value outside the surface -- exact
            // on rejection -- while a head INSIDE it proves nothing about the
            // tail the test never reads. So the axis separates exactly where
            // two head questions are DISJOINT and erases wherever they are
            // not: `[:ok]` against `[int]` is a real separation, `[int]`
            // against `[int | :ok]` is one and the same question about a
            // value's first element (fz-kdt.107 step 3).
            Self::Lists => AxisPrecision::PerPosition,
            Self::Tuples => AxisPrecision::PerPosition,
            // A schema id names the struct, never its fields; a map test is a
            // kind check; a binary and a resource test likewise.
            Self::NamedStructs | Self::OtherStructs | Self::Maps | Self::Binaries | Self::Resources => {
                AxisPrecision::Erasing
            }
        }
    }

    /// The axes a runtime value can be admitted by.
    ///
    /// A value's kind chooses its axes, which is why the axes are independent
    /// and a test is their OR. Only a struct reaches more than one: a heap
    /// struct is a tuple, a named struct, or neither, and its schema id is
    /// what says which.
    fn of_value(value: RuntimeAnyValue) -> &'static [Self] {
        match value {
            RuntimeAnyValue::Null => &[],
            RuntimeAnyValue::EmptyList => &[Self::Lists],
            RuntimeAnyValue::Int(_) => &[Self::Ints],
            RuntimeAnyValue::Float(_) => &[Self::Floats],
            RuntimeAnyValue::Atom(_) => &[Self::Atoms],
            RuntimeAnyValue::HeapRef(value_ref) => match value_ref.tag() {
                ValueKind::LIST => &[Self::Lists],
                ValueKind::MAP => &[Self::Maps],
                ValueKind::BITSTRING => &[Self::Binaries],
                ValueKind::CLOSURE => &[Self::Callables],
                ValueKind::RESOURCE => &[Self::Resources],
                ValueKind::STRUCT => &[Self::Tuples, Self::NamedStructs, Self::OtherStructs],
                _ => &[],
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeTypePredicate {
    pub(crate) ints: FiniteSet<i64>,
    pub(crate) floats: FiniteSet<u64>,
    pub(crate) atoms: FiniteSet<String>,
    /// The whole list axis: which shapes, and -- where the projection could
    /// name the element type -- what a cons cell's HEAD asks. See
    /// [`ListShapes`].
    pub(crate) lists: ListShapes,
    /// The whole tuple axis: which arities, and -- where the projection could
    /// shape them -- what each position of each shape asks. See
    /// [`TupleShapes`].
    pub(crate) tuples: TupleShapes,
    pub(crate) named_structs: FiniteSet<String>,
    pub(crate) allow_other_structs: bool,
    pub(crate) maps: bool,
    pub(crate) binaries: bool,
    /// WHICH callable, not merely "a callable". A closure value's heap word at
    /// `+8` is the code it was minted from, so the callable a value is IS
    /// runtime-observable and belongs on the same finite-or-cofinite footing as
    /// an atom or a tuple arity (fz-kdt.125).
    pub(crate) callables: FiniteSet<ClosureTarget>,
    pub(crate) resources: bool,
}

impl RuntimeTypePredicate {
    pub(crate) fn none() -> Self {
        Self {
            ints: FiniteSet::none(),
            floats: FiniteSet::none(),
            atoms: FiniteSet::none(),
            lists: ListShapes::none(),
            tuples: TupleShapes::exact(Vec::new()),
            named_structs: FiniteSet::none(),
            allow_other_structs: false,
            maps: false,
            binaries: false,
            callables: FiniteSet::none(),
            resources: false,
        }
    }

    pub(crate) fn any() -> Self {
        Self {
            ints: FiniteSet::any(),
            floats: FiniteSet::any(),
            atoms: FiniteSet::any(),
            lists: ListShapes::any(),
            tuples: TupleShapes::any(),
            named_structs: FiniteSet::any(),
            allow_other_structs: true,
            maps: true,
            binaries: true,
            callables: FiniteSet::any(),
            resources: true,
        }
    }

    /// A test that asks a tuple's arity and nothing else.
    pub(crate) fn tuple_arity(arity: usize) -> Self {
        let mut predicate = Self::none();
        predicate.tuples = TupleShapes::arity_only(FiniteSet::lit(arity));
        predicate
    }

    pub(crate) fn named_struct(name: impl Into<String>) -> Self {
        let mut predicate = Self::none();
        predicate.named_structs = FiniteSet::lit(name.into());
        predicate
    }

    pub(crate) fn map_kind() -> Self {
        let mut predicate = Self::none();
        predicate.maps = true;
        predicate
    }

    /// Every tuple arity this test can put a question to, at any depth.
    ///
    /// A nested position is only testable where the runtime can name the
    /// schema behind it, so both the interpreter and the native driver
    /// register a schema per arity this reports, not merely per top-level
    /// arity (fz-kdt.119 item 1).
    pub(crate) fn tuple_arities_at_every_depth(&self) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        self.collect_tuple_arities(&mut out);
        out
    }

    fn collect_tuple_arities(&self, out: &mut BTreeSet<usize>) {
        out.extend(self.tuples.arities().values.iter().copied());
        for sub in self.sub_predicates() {
            sub.collect_tuple_arities(out);
        }
    }

    /// Every question this test puts to something INSIDE the value: a tuple
    /// position, a cons cell's head, and whatever the next nested axis adds.
    ///
    /// One walk, gathered through the ONE axis table, because the walk is what
    /// [`Self::tuple_arities_at_every_depth`] reports and an arity a walk
    /// misses is an arity no lowering registers a schema for -- which leaves
    /// that sub-test blind in the interpreter while the native doors, which
    /// register from the same walk, still ask it. That is a three-path parity
    /// break, and it is exactly what a head-blind walk produced while
    /// fz-kdt.107 step 3 was in prototype. The match below is exhaustive over
    /// the axis table, so an axis that grows a sub-predicate cannot join the
    /// lattice without answering here (fz-kdt.145).
    fn sub_predicates(&self) -> impl Iterator<Item = &Self> {
        RuntimeTestAxis::ALL
            .into_iter()
            .flat_map(|axis| self.sub_predicates_on(axis))
    }

    fn sub_predicates_on(&self, axis: RuntimeTestAxis) -> Vec<&Self> {
        match axis {
            RuntimeTestAxis::Tuples => self.tuples.shapes().iter().flatten().collect(),
            RuntimeTestAxis::Lists => self.lists.heads().iter().collect(),
            // A scalar axis decides a value outright, and a struct, map,
            // binary, resource or callable test reads a schema id, a kind or a
            // code word -- never anything the value CONTAINS.
            RuntimeTestAxis::Ints
            | RuntimeTestAxis::Floats
            | RuntimeTestAxis::Atoms
            | RuntimeTestAxis::NamedStructs
            | RuntimeTestAxis::OtherStructs
            | RuntimeTestAxis::Maps
            | RuntimeTestAxis::Binaries
            | RuntimeTestAxis::Callables
            | RuntimeTestAxis::Resources => Vec::new(),
        }
    }

    /// Whether this test says nothing at all on `axis`.
    fn is_none_on(&self, axis: RuntimeTestAxis) -> bool {
        match axis {
            RuntimeTestAxis::Ints => self.ints.is_none(),
            RuntimeTestAxis::Floats => self.floats.is_none(),
            RuntimeTestAxis::Atoms => self.atoms.is_none(),
            RuntimeTestAxis::Lists => self.lists.shapes().is_none(),
            RuntimeTestAxis::Tuples => self.tuples.arities().is_none(),
            RuntimeTestAxis::NamedStructs => self.named_structs.is_none(),
            RuntimeTestAxis::OtherStructs => !self.allow_other_structs,
            RuntimeTestAxis::Maps => !self.maps,
            RuntimeTestAxis::Binaries => !self.binaries,
            RuntimeTestAxis::Callables => self.callables.is_none(),
            RuntimeTestAxis::Resources => !self.resources,
        }
    }

    /// The axes this test says anything at all on, in table order.
    ///
    /// The native emitters walk this: an axis a predicate is silent on emits
    /// no code, which is what keeps a one-axis test one comparison.
    pub(crate) fn axes(&self) -> impl Iterator<Item = RuntimeTestAxis> + '_ {
        RuntimeTestAxis::ALL.into_iter().filter(|axis| !self.is_none_on(*axis))
    }

    /// Whether every value this predicate's test admits on `axis`, `other`'s
    /// admits too.
    fn axis_contained_in(&self, other: &Self, axis: RuntimeTestAxis) -> bool {
        match axis {
            RuntimeTestAxis::Ints => other.ints.contains_all(&self.ints),
            RuntimeTestAxis::Floats => other.floats.contains_all(&self.floats),
            RuntimeTestAxis::Atoms => other.atoms.contains_all(&self.atoms),
            RuntimeTestAxis::Lists => other.lists.contains_all(&self.lists),
            RuntimeTestAxis::Tuples => other.tuples.contains_all(&self.tuples),
            RuntimeTestAxis::NamedStructs => other.named_structs.contains_all(&self.named_structs),
            RuntimeTestAxis::OtherStructs => other.allow_other_structs || !self.allow_other_structs,
            RuntimeTestAxis::Maps => other.maps || !self.maps,
            RuntimeTestAxis::Binaries => other.binaries || !self.binaries,
            RuntimeTestAxis::Callables => other.callables.contains_all(&self.callables),
            RuntimeTestAxis::Resources => other.resources || !self.resources,
        }
    }

    /// Whether one value could pass both tests on `axis`.
    fn axis_overlaps(&self, other: &Self, axis: RuntimeTestAxis) -> bool {
        match axis {
            RuntimeTestAxis::Ints => self.ints.overlaps(&other.ints),
            RuntimeTestAxis::Floats => self.floats.overlaps(&other.floats),
            RuntimeTestAxis::Atoms => self.atoms.overlaps(&other.atoms),
            RuntimeTestAxis::Lists => self.lists.overlaps(&other.lists),
            RuntimeTestAxis::Tuples => self.tuples.overlaps(&other.tuples),
            RuntimeTestAxis::NamedStructs => self.named_structs.overlaps(&other.named_structs),
            RuntimeTestAxis::OtherStructs => self.allow_other_structs && other.allow_other_structs,
            RuntimeTestAxis::Maps => self.maps && other.maps,
            RuntimeTestAxis::Binaries => self.binaries && other.binaries,
            RuntimeTestAxis::Callables => self.callables.overlaps(&other.callables),
            RuntimeTestAxis::Resources => self.resources && other.resources,
        }
    }

    /// Whether one value could pass both tests on `axis` WITHOUT either test
    /// having looked at what the bodies behind them read.
    fn axis_erases(&self, other: &Self, axis: RuntimeTestAxis) -> bool {
        match axis.precision() {
            AxisPrecision::Separating => false,
            AxisPrecision::Erasing => self.axis_overlaps(other, axis),
            AxisPrecision::PerPosition => match axis {
                RuntimeTestAxis::Tuples => self.tuples.erasing_overlap(&other.tuples),
                RuntimeTestAxis::Lists => self.lists.erasing_overlap(&other.lists),
                // A further per-position axis must name its own store here --
                // answering about tuples for it would silently break the seat.
                _ => unreachable!("per-position precision with no per-position store: {axis:?}"),
            },
        }
    }

    /// Whether every value this predicate's test admits, `other`'s admits too.
    ///
    /// Axis by axis, because the axes are independent: a value reaches exactly
    /// the axes its kind names, so a test that admits more on every axis
    /// admits more, full stop. This is CONTAINMENT OF TESTS, not of the
    /// semantic types the tests were projected from -- `{:halt, :false}` and
    /// `{:cont, :true} | {:halt, :false}` are two types and (on the atom
    /// position) two tests, while `{:halt, [int]}` and `{:halt, [int | :ok]}`
    /// are two types and one test.
    ///
    /// It is what the runtime ASKS, and that is exactly why it does not settle
    /// a dispatch's arm order on its own. A test is a projection and it drops
    /// what the body reads: a list head says nothing about the tail, and a
    /// tuple position erases whatever its own sub-test erases. So a value can
    /// satisfy every question an arm asks and still lie outside the surface
    /// that arm's body was compiled for, and seating on this relation alone
    /// hands it to a body that never named it (fz-kdt.131).
    /// `callsite_dispatch::covers` is the conjunct that makes a seat sound;
    /// this is one half of it.
    pub(crate) fn contained_in(&self, other: &Self) -> bool {
        RuntimeTestAxis::ALL
            .into_iter()
            .all(|axis| self.axis_contained_in(other, axis))
    }

    /// Whether the two tests can both admit a value on an axis whose
    /// projection ERASES something a body reads.
    ///
    /// On such an axis "the tests differ" is not separation -- tuple arities
    /// {2} and {2,3} both admit a 2-tuple, and `[int]` and `[int | :ok]` both
    /// admit a cons cell whose head is an int -- so a dispatch seat may not
    /// skip the surface-coverage check there. [`RuntimeTestAxis::precision`]
    /// is the table that says which axes those are, and it is the same table
    /// the three lowerings are written against: an axis may only be called
    /// separating here because all three actually decide it.
    ///
    /// NEITHER STRUCTURAL AXIS is wholly one or the other; each is as
    /// separating as the questions it puts to what the value contains.
    ///
    /// The tuple axis carries one sub-predicate per position per shape, so two
    /// shapes that overlap are erasing only where some position they overlap
    /// at is itself erasing: `{:cont, int}` and `{:halt, int}` separate on an
    /// atom, while `{:ok, [int]}` and `{:ok, [int | :ok]}` are one and the
    /// same question.
    ///
    /// The list axis carries one head question per cons-admitting clause, and
    /// its law is one-sided: rejection is exact and acceptance is not, so
    /// DISJOINT heads separate and any overlap at all erases. See
    /// [`ListShapes::erasing_overlap`], which states it in full.
    pub(crate) fn overlaps_on_an_erasing_axis(&self, other: &Self) -> bool {
        RuntimeTestAxis::ALL
            .into_iter()
            .any(|axis| self.axis_erases(other, axis))
    }

    pub(crate) fn overlaps(&self, other: &Self) -> bool {
        RuntimeTestAxis::ALL
            .into_iter()
            .any(|axis| self.axis_overlaps(other, axis))
    }
}

/// The list shapes a test admits, plus the question a cons cell's HEAD is put.
///
/// This is the list axis' answer to [`TupleShapes`], and its shape follows what
/// the type lattice actually says about a list: `ListSig` carries ONE element
/// type for the whole list, so a list type is HOMOGENEOUS by construction. That
/// is what makes a single head load worth reading.
///
/// `heads` holds one entry per list CLAUSE that admits a cons cell, which is
/// what keeps the clauses correlated -- the same reason [`TupleShapes`] keeps
/// one shape per clause. `exact` records whether every such clause could be
/// projected; an inexact axis is the shape-only reading this layer had before
/// fz-kdt.107 step 3, and is a sound over-approximation of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ListShapes {
    shapes: FiniteSet<ListShape>,
    heads: Vec<RuntimeTypePredicate>,
    exact: bool,
}

impl ListShapes {
    pub(crate) fn none() -> Self {
        Self {
            shapes: FiniteSet::none(),
            heads: Vec::new(),
            exact: true,
        }
    }

    /// The coarse reading: these shapes, and nothing about the elements.
    pub(crate) fn shape_only(shapes: FiniteSet<ListShape>) -> Self {
        Self {
            shapes,
            heads: Vec::new(),
            exact: false,
        }
    }

    /// These shapes, with one head question per cons-admitting clause.
    ///
    /// INVARIANT: an axis that admits `NonEmpty` carries at least one head.
    /// A cons-admitting axis with nothing to ask is the shape-only reading and
    /// must be built as one, or it would claim to CONTAIN sharper axes while
    /// asking strictly less than they do.
    pub(crate) fn exact(shapes: FiniteSet<ListShape>, heads: Vec<RuntimeTypePredicate>) -> Self {
        debug_assert!(
            !shapes.contains(&ListShape::NonEmpty) || !heads.is_empty(),
            "an exact list axis that admits a cons cell must ask its head something",
        );
        Self {
            shapes,
            heads,
            exact: true,
        }
    }

    /// Every list, of every element type.
    pub(crate) fn any() -> Self {
        Self::shape_only(FiniteSet::any())
    }

    /// Which shapes the test admits. Always answerable, and the only thing this
    /// axis said before fz-kdt.107 step 3 -- the coarse callers
    /// (`jobs::transport`, `lowering_tests_position`) still read it alone.
    pub(crate) fn shapes(&self) -> &FiniteSet<ListShape> {
        &self.shapes
    }

    pub(crate) fn heads(&self) -> &[RuntimeTypePredicate] {
        &self.heads
    }

    #[cfg(test)]
    pub(crate) fn is_exact(&self) -> bool {
        self.exact
    }

    /// Whether the test asks a cons cell's head anything at all.
    ///
    /// The three lowerings read this, so a head-blind axis emits and answers
    /// exactly what it did before this axis learned to look. By [`Self::exact`]'s
    /// invariant this is `exact && admits a cons cell`; the head check is
    /// stated anyway because the answer must not depend on the invariant
    /// holding.
    pub(crate) fn asks_the_head(&self) -> bool {
        self.exact && !self.heads.is_empty() && self.shapes.contains(&ListShape::NonEmpty)
    }

    /// Whether one cons cell could pass both head questions.
    ///
    /// An axis that asks the head nothing admits every head, so it overlaps
    /// with anything: what a test declines to ask is never a separation.
    fn heads_overlap(&self, other: &Self) -> bool {
        if !self.asks_the_head() || !other.asks_the_head() {
            return true;
        }
        self.heads
            .iter()
            .any(|left| other.heads.iter().any(|right| left.overlaps(right)))
    }

    /// Whether every list `other` admits, this axis admits too.
    ///
    /// An inexact axis is the shape-only reading, which admits every element,
    /// so it contains anything; and nothing exact contains it.
    fn contains_all(&self, other: &Self) -> bool {
        if !self.shapes.contains_all(&other.shapes) {
            return false;
        }
        if !self.exact {
            return true;
        }
        if !other.exact {
            return false;
        }
        other
            .heads
            .iter()
            .all(|theirs| self.heads.iter().any(|ours| theirs.contained_in(ours)))
    }

    /// Whether one list could pass both tests.
    ///
    /// `[]` is a shape, not a head: two tests that both admit the empty list
    /// overlap there whatever their heads say.
    fn overlaps(&self, other: &Self) -> bool {
        if !self.shapes.overlaps(&other.shapes) {
            return false;
        }
        if self.shapes.contains(&ListShape::Empty) && other.shapes.contains(&ListShape::Empty) {
            return true;
        }
        self.heads_overlap(other)
    }

    /// Whether one list could pass both tests through what NEITHER test reads.
    ///
    /// THE ONE-SIDED-FILTER LAW (fz-kdt.107 step 3; the rule this replaced was
    /// refuted by measurement, so read this one as written). A head load is
    ///
    /// - EXACT ON REJECTION: a list type is homogeneous, so a head outside the
    ///   element question proves the whole value lies outside the surface;
    /// - ERASING ON ACCEPTANCE: a head inside it proves nothing about the tail,
    ///   which no test reads.
    ///
    /// So DISJOINT heads are the only claimable separation. Two `NonEmpty`
    /// tests whose heads overlap AT ALL erase -- `[int]` and `[int | :ok]`
    /// disagree only about a tail, and seating the narrow one first hands
    /// `[1, :ok]` to a body that reads every element as an int. Claiming
    /// otherwise is precisely what re-created the abort this axis exists to
    /// kill.
    ///
    /// THE `[]` EXCEPTION: two tests meeting only at the empty list do not
    /// erase. `[]` is a single value carrying nothing, so no body admitted
    /// through it can misread what arrives -- the same reason the atom axis
    /// separates.
    ///
    /// An inexact axis, or one that asks no head, erases wherever it admits a
    /// cons cell: what the projection could not name, the seat may not claim.
    fn erasing_overlap(&self, other: &Self) -> bool {
        if !self.shapes.contains(&ListShape::NonEmpty) || !other.shapes.contains(&ListShape::NonEmpty) {
            return false;
        }
        self.heads_overlap(other)
    }
}

/// The fixed-arity tuple shapes a test admits, one sub-predicate per position.
///
/// `shapes` holds one entry per tuple CLAUSE of the descriptor it was
/// projected from, which is what keeps cross-position correlation: `{:cont,
/// int} | {:halt, atom}` is two shapes, and re-joining them into "position 0 is
/// `:cont | :halt`, position 1 is `int | atom`" would admit `{:cont, atom}`,
/// which neither clause names (fz-kdt.126 -- never re-join what the lattice
/// kept apart).
///
/// `exact` records whether EVERY clause could be shaped. A clause with several
/// positive signatures is an intersection and one with negations is a
/// difference; neither is a list of positions, so an inexact axis falls back to
/// the arity-only reading, which is what this layer asked before fz-kdt.119 and
/// is a sound over-approximation of it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TupleShapes {
    /// Which arities the test admits. Always answerable, and the only thing
    /// this axis said before fz-kdt.119 -- four callers still read it alone
    /// (`jobs::transport`, `jobs::runtime_demand`, the interpreter's schema
    /// registration and the native driver's).
    arities: FiniteSet<usize>,
    /// One entry per tuple clause, when every clause could be shaped; empty
    /// otherwise, and then `exact` is false.
    shapes: Vec<Vec<RuntimeTypePredicate>>,
    exact: bool,
}

/// Which positions of a tuple shape a reading looks at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PositionScope {
    /// The positions all three lowerings decide.
    Lowered,
    /// Every position, including the ones the lowerings are blind to. This is
    /// what the surface-membership tripwire compares against: the gap between
    /// the two readings IS the population of values a test admits into a body
    /// that never named them.
    Full,
}

/// Whether the lowerings emit a test for a position whose question is `sub`.
///
/// SCOPE A CARVE-OUT (fz-kdt.119; Scope B is fz-kdt.138): a position that can
/// hold a LIST is not tested at all. Testing only the position's non-list axes
/// would make the test STRICTER than the type -- the position's question is a
/// disjunction, and dropping a disjunct rejects values the arm's surface names
/// -- so the choice is to decide the list axis there or to be blind, and
/// deciding it separates `{[], int}` from `{[int], int}`, which wakes the
/// dead-and-broken accumulator specialization fz-kdt.132 owns. Blind is the
/// over-approximation, and it is the one this layer already made everywhere
/// before per-position shapes existed.
///
/// The lattice reads this too, so a blind position counts as overlapping and
/// as erasing: what the lowering declines to ask, the seat may not claim as
/// separation.
pub(crate) fn lowering_tests_position(sub: &RuntimeTypePredicate) -> bool {
    sub.lists.shapes().is_none()
}

fn position_overlaps(left: &RuntimeTypePredicate, right: &RuntimeTypePredicate) -> bool {
    !lowering_tests_position(left) || !lowering_tests_position(right) || left.overlaps(right)
}

fn position_erases(left: &RuntimeTypePredicate, right: &RuntimeTypePredicate) -> bool {
    !lowering_tests_position(left) || !lowering_tests_position(right) || left.overlaps_on_an_erasing_axis(right)
}

fn position_contains(outer: &RuntimeTypePredicate, inner: &RuntimeTypePredicate) -> bool {
    if !lowering_tests_position(outer) {
        return true;
    }
    lowering_tests_position(inner) && inner.contained_in(outer)
}

fn shapes_overlap(left: &[RuntimeTypePredicate], right: &[RuntimeTypePredicate]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(l, r)| position_overlaps(l, r))
}

impl TupleShapes {
    /// One shape per clause, and the arities they name.
    ///
    /// The arity set is DERIVED, never stated twice: an exact axis' arities
    /// are its shapes' lengths, so the two readings cannot drift apart.
    pub(crate) fn exact(shapes: Vec<Vec<RuntimeTypePredicate>>) -> Self {
        Self {
            arities: FiniteSet::finite(shapes.iter().map(Vec::len)),
            shapes,
            exact: true,
        }
    }

    /// The coarse reading: these arities, and nothing about the payloads.
    pub(crate) fn arity_only(arities: FiniteSet<usize>) -> Self {
        Self {
            arities,
            shapes: Vec::new(),
            exact: false,
        }
    }

    /// Every tuple, of every arity.
    pub(crate) fn any() -> Self {
        Self::arity_only(FiniteSet::any())
    }

    pub(crate) fn arities(&self) -> &FiniteSet<usize> {
        &self.arities
    }

    pub(crate) fn shapes(&self) -> &[Vec<RuntimeTypePredicate>] {
        &self.shapes
    }

    pub(crate) fn is_exact(&self) -> bool {
        self.exact
    }

    /// The shapes of one arity -- the ones a value of that arity could match.
    fn of_arity(&self, arity: usize) -> impl Iterator<Item = &[RuntimeTypePredicate]> {
        self.shapes
            .iter()
            .map(Vec::as_slice)
            .filter(move |shape| shape.len() == arity)
    }

    /// Whether every shape `other` admits, some shape of this axis admits too.
    ///
    /// An inexact axis is the arity-only reading, which admits every payload,
    /// so it contains anything; and nothing exact contains it.
    fn contains_all(&self, other: &Self) -> bool {
        if !self.arities.contains_all(&other.arities) {
            return false;
        }
        if !self.exact {
            return true;
        }
        if !other.exact {
            return false;
        }
        other.shapes.iter().all(|theirs| {
            self.shapes.iter().any(|ours| {
                ours.len() == theirs.len()
                    && ours
                        .iter()
                        .zip(theirs)
                        .all(|(ours, theirs)| position_contains(ours, theirs))
            })
        })
    }

    /// Whether one tuple could pass both tests.
    fn overlaps(&self, other: &Self) -> bool {
        if !self.arities.overlaps(&other.arities) {
            return false;
        }
        if !self.exact || !other.exact {
            return true;
        }
        self.shapes
            .iter()
            .any(|left| other.shapes.iter().any(|right| shapes_overlap(left, right)))
    }

    /// Whether one tuple could pass both tests through a position NEITHER test
    /// can see past. A shape pair that overlaps only through positions whose
    /// own questions separate is a real separation, and a seat may skip the
    /// surface check for it.
    fn erasing_overlap(&self, other: &Self) -> bool {
        if !self.arities.overlaps(&other.arities) {
            return false;
        }
        if !self.exact || !other.exact {
            return true;
        }
        self.shapes.iter().any(|left| {
            other
                .shapes
                .iter()
                .any(|right| shapes_overlap(left, right) && left.iter().zip(right).any(|(l, r)| position_erases(l, r)))
        })
    }
}

impl Default for RuntimeTypePredicate {
    fn default() -> Self {
        Self::none()
    }
}

impl fmt::Display for RuntimeTypePredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Which callable a runtime code word denotes.
///
/// The word a closure carries at `+8` is the backend's, not the type lattice's:
/// one callable can be minted through several code paths, and a backend is free
/// to name them however it likes. The backend that minted them is therefore the
/// authority on reading them back, and it answers here. `None` is a code word
/// the program never described, which no finite callable set can name.
pub(crate) type CallableIdentities<'a> = dyn Fn(u64) -> Option<ClosureTarget> + 'a;

/// Read field `index` out of a tuple value.
///
/// Mirrors [`CallableIdentities`]: the side that owns the representation
/// answers. `None` is a field the reader could not produce, which no
/// sub-predicate can be asked about.
pub(crate) type TupleFieldReader<'a> = dyn Fn(RuntimeAnyValue, usize) -> Option<RuntimeAnyValue> + 'a;

/// Read the first element out of a cons cell.
///
/// Mirrors [`TupleFieldReader`]: the side that owns the representation
/// answers. `None` is a head the reader could not produce, which no head
/// question can be asked about.
pub(crate) type ListHeadReader<'a> = dyn Fn(RuntimeAnyValue) -> Option<RuntimeAnyValue> + 'a;

/// Everything the interpreter's matcher needs to read a value back.
///
/// The schema maps are the runtime's own numbering, so they are handed in
/// rather than derived here; the two function slots are the representation's
/// owners answering questions only they can.
pub(crate) struct RuntimeValueReader<'a> {
    pub(crate) module: &'a Module,
    pub(crate) tuple_schema_ids: &'a HashMap<usize, u32>,
    pub(crate) named_schema_ids: &'a HashMap<String, u32>,
    pub(crate) callables: &'a CallableIdentities<'a>,
    pub(crate) fields: &'a TupleFieldReader<'a>,
    pub(crate) list_head: &'a ListHeadReader<'a>,
}

impl RuntimeValueReader<'_> {
    /// The schema ids of every named struct the module declares.
    fn known_named_schemas(&self) -> BTreeSet<u32> {
        self.module
            .struct_schemas
            .keys()
            .filter_map(|name| self.named_schema_ids.get(name).copied())
            .collect()
    }

    fn tuple_arity_of(&self, schema: u32) -> Option<usize> {
        self.tuple_schema_ids
            .iter()
            .find(|(_, id)| **id == schema)
            .map(|(arity, _)| *arity)
    }
}

pub(crate) fn matches_runtime_type_predicate(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
) -> bool {
    RuntimeTestAxis::of_value(value)
        .iter()
        .any(|axis| axis_admits(predicate, reader, value, *axis, PositionScope::Lowered))
}

/// Whether `axis` admits `value`.
///
/// Only ever asked of the axes [`RuntimeTestAxis::of_value`] names, so the kind
/// is already known to fit; each arm still states the kind it reads, because a
/// test that answers about the wrong kind is worse than one that costs a
/// comparison.
fn axis_admits(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
    axis: RuntimeTestAxis,
    scope: PositionScope,
) -> bool {
    match axis {
        RuntimeTestAxis::Ints => matches!(value, RuntimeAnyValue::Int(int) if predicate.ints.contains(&int)),
        RuntimeTestAxis::Floats => matches!(value, RuntimeAnyValue::Float(bits) if predicate.floats.contains(&bits)),
        RuntimeTestAxis::Atoms => match value {
            RuntimeAnyValue::Atom(atom_id) => mapped_membership(&predicate.atoms, atom_id, |name| {
                reader
                    .module
                    .atom_names
                    .iter()
                    .position(|candidate| candidate == name)
                    .map(|idx| idx as u32)
            }),
            _ => false,
        },
        RuntimeTestAxis::Lists => match value {
            RuntimeAnyValue::EmptyList => predicate.lists.shapes().contains(&ListShape::Empty),
            RuntimeAnyValue::HeapRef(value_ref) if value_ref.tag() == ValueKind::LIST => {
                predicate.lists.shapes().contains(&ListShape::NonEmpty)
                    && matches_list_head(&predicate.lists, reader, value, scope)
            }
            _ => false,
        },
        RuntimeTestAxis::Maps => predicate.maps && has_kind(value, ValueKind::MAP),
        RuntimeTestAxis::Binaries => predicate.binaries && has_kind(value, ValueKind::BITSTRING),
        RuntimeTestAxis::Resources => predicate.resources && has_kind(value, ValueKind::RESOURCE),
        RuntimeTestAxis::Callables => {
            has_kind(value, ValueKind::CLOSURE) && matches_runtime_callable(predicate, value, reader.callables)
        }
        RuntimeTestAxis::Tuples => matches_tuple_axis(predicate, reader, value, scope),
        RuntimeTestAxis::NamedStructs => matches_named_struct_axis(predicate, reader, value),
        RuntimeTestAxis::OtherStructs => matches_other_struct_axis(predicate, reader, value),
    }
}

fn has_kind(value: RuntimeAnyValue, kind: ValueKind) -> bool {
    matches!(value, RuntimeAnyValue::HeapRef(value_ref) if value_ref.tag() == kind)
}

fn struct_schema_of(value: RuntimeAnyValue) -> Option<u32> {
    if !has_kind(value, ValueKind::STRUCT) {
        return None;
    }
    let ptr = value.heap_addr()?;
    Some(unsafe { struct_schema_id(ptr.cast_const()) })
}

/// Read a closure value's identity and ask the predicate about it.
///
/// A cofinite callable set names every callable but the ones it lists, so a
/// code word the backend cannot place is in it: the value is a callable, and
/// none of the excluded ones.
fn matches_runtime_callable(
    predicate: &RuntimeTypePredicate,
    value: RuntimeAnyValue,
    callables: &CallableIdentities<'_>,
) -> bool {
    if predicate.callables.is_none() {
        return false;
    }
    if predicate.callables.is_any() {
        return true;
    }
    let Some(addr) = value.heap_addr() else {
        return false;
    };
    match callables(unsafe { closure_fn_ptr(addr.cast_const()) }) {
        Some(target) => predicate.callables.contains(&target),
        None => predicate.callables.cofinite,
    }
}

fn mapped_membership<T, U>(set: &FiniteSet<T>, actual: U, mut map: impl FnMut(&T) -> Option<U>) -> bool
where
    T: Ord,
    U: Ord,
{
    set.values
        .iter()
        .filter_map(&mut map)
        .collect::<BTreeSet<_>>()
        .contains(&actual)
        != set.cofinite
}

/// "Is this an admitted tuple, of an admitted shape?"
///
/// The arity half is a schema-id membership question; the shape half asks each
/// position its own question, and is skipped where the axis is inexact, which
/// is the arity-only reading this layer had before fz-kdt.119.
fn matches_tuple_axis(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
    scope: PositionScope,
) -> bool {
    let arities = predicate.tuples.arities();
    if arities.is_none() {
        return false;
    }
    let Some(actual) = struct_schema_of(value) else {
        return false;
    };
    let known_named = reader.known_named_schemas();
    let named_arities = || {
        arities
            .values
            .iter()
            .filter_map(|arity| reader.tuple_schema_ids.get(arity).copied())
            .collect::<BTreeSet<_>>()
    };
    let arity_match = if arities.is_any() {
        !known_named.contains(&actual)
    } else if arities.cofinite {
        !known_named.contains(&actual) && !named_arities().contains(&actual)
    } else {
        named_arities().contains(&actual)
    };
    arity_match && matches_tuple_shape(predicate, reader, value, actual, scope)
}

/// Whether some shape the test names matches the tuple's fields.
///
/// The tuple's own arity chooses the candidate shapes; a shape matches when
/// every position the `scope` looks at answers yes. Under
/// [`PositionScope::Lowered`] that is the positions all three lowerings
/// decide, so this function and the emitted code answer alike by construction.
fn matches_tuple_shape(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
    schema: u32,
    scope: PositionScope,
) -> bool {
    if !predicate.tuples.is_exact() {
        return true;
    }
    let Some(arity) = reader.tuple_arity_of(schema) else {
        // A tuple whose arity this test never named: the arity half above
        // already decided it, and there is no shape to ask.
        return true;
    };
    predicate.tuples.of_arity(arity).any(|shape| {
        shape.iter().enumerate().all(|(index, position)| {
            if scope == PositionScope::Lowered && !lowering_tests_position(position) {
                return true;
            }
            (reader.fields)(value, index).is_some_and(|field| {
                RuntimeTestAxis::of_value(field)
                    .iter()
                    .any(|axis| axis_admits(position, reader, field, *axis, scope))
            })
        })
    })
}

/// Whether some clause's head question admits this cons cell's first element.
///
/// The shape half above has already decided that a cons cell is admitted at
/// all; this is the element half, and it is skipped where the axis asks the
/// head nothing, which is the shape-only reading this layer had before
/// fz-kdt.107 step 3. The emitted native test is the same disjunction under
/// the same cons guard, so this function and the compiled code answer alike.
fn matches_list_head(
    lists: &ListShapes,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
    scope: PositionScope,
) -> bool {
    if !lists.asks_the_head() {
        return true;
    }
    let Some(head) = (reader.list_head)(value) else {
        // A head the representation's owner could not produce is a head no
        // question can be asked about, so the shape half stands alone.
        return true;
    };
    lists.heads().iter().any(|question| {
        RuntimeTestAxis::of_value(head)
            .iter()
            .any(|axis| axis_admits(question, reader, head, *axis, scope))
    })
}

fn matches_named_struct_axis(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
) -> bool {
    if predicate.named_structs.is_none() {
        return false;
    }
    let Some(actual) = struct_schema_of(value) else {
        return false;
    };
    let known_named = reader.known_named_schemas();
    if predicate.named_structs.is_any() {
        return known_named.contains(&actual);
    }
    let relevant = predicate
        .named_structs
        .values
        .iter()
        .filter_map(|name| reader.named_schema_ids.get(name).copied())
        .collect::<BTreeSet<_>>();
    if predicate.named_structs.cofinite {
        known_named.contains(&actual) && !relevant.contains(&actual)
    } else {
        relevant.contains(&actual)
    }
}

fn matches_other_struct_axis(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
) -> bool {
    if !predicate.allow_other_structs {
        return false;
    }
    let Some(actual) = struct_schema_of(value) else {
        return false;
    };
    let known_tuple = predicate
        .tuples
        .arities()
        .values
        .iter()
        .filter_map(|arity| reader.tuple_schema_ids.get(arity).copied())
        .collect::<BTreeSet<_>>();
    !reader.known_named_schemas().contains(&actual) && !known_tuple.contains(&actual)
}

/// The dynamic surface-membership tripwire (fz-kdt.135).
///
/// A test is a projection, so a value can pass every question an arm asks and
/// still lie outside the surface that arm's body was compiled for. The static
/// gates reason about that hazard on hand-picked pairs; this measures it, on
/// the production path, over whatever the corpus actually runs.
///
/// What it can see cheaply is the tuple axis: the test is answered under
/// [`PositionScope::Lowered`], and the tripwire re-asks it under
/// [`PositionScope::Full`], which looks at the positions the lowerings are
/// blind to as well. A value admitted by the first reading and refused by the
/// second passed a test no shape of the arm's surface names -- exactly the
/// blind routing this class of defect is made of.
///
/// The LIST axis is not re-asked, and it is the natural next reading now that
/// a cons cell's head carries a predicate of its own: the head is exact on
/// rejection and erasing on acceptance, so a full re-ask would walk the tail
/// the emitted test never reads. That is fz-kdt.144, deliberately not folded
/// in here -- the 268-escape baseline this reports is the tuple population,
/// and mixing a second population into it would lose the comparand.
///
/// It is off unless `FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP` is set; `abort`
/// makes each finding fatal, anything else counts them and reports each on
/// stderr, which is what a corpus census reads.
pub(crate) mod surface_membership {
    use super::{PositionScope, RuntimeTestAxis, RuntimeTypePredicate, RuntimeValueReader, axis_admits};
    use fz_runtime::any_value::AnyValue as RuntimeAnyValue;
    use std::sync::OnceLock;

    pub(crate) const ASSERT_SURFACE_MEMBERSHIP_ENV: &str = "FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP";

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum Mode {
        /// Not installed: nothing is checked and nothing is paid.
        Off,
        /// Report every finding on stderr and carry on. A corpus census is
        /// `FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP=1 fz2 interp <fixture> 2>&1 |
        /// grep -c 'surface-membership escape'`.
        Report,
        /// Make every finding fatal, for bisecting one fixture down to the
        /// dispatch that routes blind.
        Abort,
    }

    pub(crate) fn mode() -> Mode {
        static MODE: OnceLock<Mode> = OnceLock::new();
        *MODE.get_or_init(|| match std::env::var(ASSERT_SURFACE_MEMBERSHIP_ENV) {
            Err(_) => Mode::Off,
            Ok(value) if value == "abort" => Mode::Abort,
            Ok(_) => Mode::Report,
        })
    }

    /// Check one admitted value against the surface the test was projected
    /// from, and report it where it is not in there.
    pub(crate) fn observe(predicate: &RuntimeTypePredicate, reader: &RuntimeValueReader<'_>, value: RuntimeAnyValue) {
        let mode = mode();
        if mode == Mode::Off || !escaped(predicate, reader, value) {
            return;
        }
        let report = format!(
            "surface-membership escape: a value the test admits lies outside every shape it names \
             (value kind {:?}, test {predicate})",
            value.kind(),
        );
        match mode {
            Mode::Abort => panic!("{report}"),
            _ => eprintln!("{report}"),
        }
    }

    fn escaped(predicate: &RuntimeTypePredicate, reader: &RuntimeValueReader<'_>, value: RuntimeAnyValue) -> bool {
        if !predicate.tuples.is_exact() || !RuntimeTestAxis::of_value(value).contains(&RuntimeTestAxis::Tuples) {
            return false;
        }
        axis_admits(
            predicate,
            reader,
            value,
            RuntimeTestAxis::Tuples,
            PositionScope::Lowered,
        ) && !axis_admits(predicate, reader, value, RuntimeTestAxis::Tuples, PositionScope::Full)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Widen this test to admit everything on `axis` and nothing more.
    ///
    /// This is the table read the other way: a field no axis names would be
    /// left at `none()` by the fold below, and `any()` would not come out.
    fn widen_to_top_on(predicate: &mut RuntimeTypePredicate, axis: RuntimeTestAxis) {
        match axis {
            RuntimeTestAxis::Ints => predicate.ints = FiniteSet::any(),
            RuntimeTestAxis::Floats => predicate.floats = FiniteSet::any(),
            RuntimeTestAxis::Atoms => predicate.atoms = FiniteSet::any(),
            RuntimeTestAxis::Lists => predicate.lists = ListShapes::any(),
            RuntimeTestAxis::Tuples => predicate.tuples = TupleShapes::any(),
            RuntimeTestAxis::NamedStructs => predicate.named_structs = FiniteSet::any(),
            RuntimeTestAxis::OtherStructs => predicate.allow_other_structs = true,
            RuntimeTestAxis::Maps => predicate.maps = true,
            RuntimeTestAxis::Binaries => predicate.binaries = true,
            RuntimeTestAxis::Callables => predicate.callables = FiniteSet::any(),
            RuntimeTestAxis::Resources => predicate.resources = true,
        }
    }

    /// The invariant behind fz-kdt.119 item 6: the axis table is the whole
    /// lattice, so nothing a predicate carries can escape the classification
    /// `overlaps_on_an_erasing_axis` and the three lowerings are written
    /// against.
    #[test]
    fn the_axis_table_names_every_axis_a_predicate_carries() {
        let mut built = RuntimeTypePredicate::none();
        for axis in RuntimeTestAxis::ALL {
            widen_to_top_on(&mut built, axis);
        }
        assert_eq!(
            built,
            RuntimeTypePredicate::any(),
            "an axis the table does not name would leave its field at none() here; \
             add it to RuntimeTestAxis::ALL and to every lowering's match",
        );
    }

    /// Every axis is reachable by some runtime value: a test the runtime can
    /// never be asked is not a test, and a value that reaches no axis is one
    /// no arm can claim.
    #[test]
    fn every_axis_is_reached_by_some_runtime_value_kind() {
        let mut reached = BTreeSet::new();
        for kind in [
            ValueKind::LIST,
            ValueKind::MAP,
            ValueKind::BITSTRING,
            ValueKind::CLOSURE,
            ValueKind::RESOURCE,
            ValueKind::STRUCT,
        ] {
            // A heap value's axes are a function of its tag alone, which is
            // what `of_value` reads; the address is never dereferenced here.
            let axes = axes_for_tag(kind);
            reached.extend(axes.iter().copied());
        }
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::Int(0)).iter().copied());
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::Float(0)).iter().copied());
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::Atom(0)).iter().copied());
        reached.extend(RuntimeTestAxis::of_value(RuntimeAnyValue::EmptyList).iter().copied());
        assert_eq!(
            reached,
            RuntimeTestAxis::ALL.into_iter().collect::<BTreeSet<_>>(),
            "an axis no value kind reaches is a question the runtime is never asked",
        );
    }

    fn axes_for_tag(kind: ValueKind) -> &'static [RuntimeTestAxis] {
        match kind {
            ValueKind::LIST => &[RuntimeTestAxis::Lists],
            ValueKind::MAP => &[RuntimeTestAxis::Maps],
            ValueKind::BITSTRING => &[RuntimeTestAxis::Binaries],
            ValueKind::CLOSURE => &[RuntimeTestAxis::Callables],
            ValueKind::RESOURCE => &[RuntimeTestAxis::Resources],
            ValueKind::STRUCT => &[
                RuntimeTestAxis::Tuples,
                RuntimeTestAxis::NamedStructs,
                RuntimeTestAxis::OtherStructs,
            ],
            _ => &[],
        }
    }

    /// The classification and the relation it feeds must agree: an axis is
    /// erasing exactly when two tests saturating it overlap erasingly.
    #[test]
    fn the_precision_table_is_what_overlaps_on_an_erasing_axis_reports() {
        for axis in RuntimeTestAxis::ALL {
            let mut saturated = RuntimeTypePredicate::none();
            widen_to_top_on(&mut saturated, axis);
            let erases = saturated.overlaps_on_an_erasing_axis(&saturated);
            match axis.precision() {
                AxisPrecision::Separating => assert!(!erases, "{axis:?} is classified separating but reports erasing"),
                // A saturated per-position axis is its own coarse reading --
                // every arity, every element -- so it erases. The per-position
                // shapes and the head questions are what make it separate, and
                // those are the neighbouring tests' business.
                AxisPrecision::Erasing | AxisPrecision::PerPosition => {
                    assert!(erases, "{axis:?} is classified erasing but reports separating")
                }
            }
        }
    }

    fn tuple(shapes: Vec<Vec<RuntimeTypePredicate>>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(shapes);
        predicate
    }

    fn atom(name: &str) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.atoms = FiniteSet::lit(name.to_string());
        predicate
    }

    fn ints() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.ints = FiniteSet::any();
        predicate
    }

    fn list_of_anything() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.lists = ListShapes::any();
        predicate
    }

    /// A cons-only test whose head asks `heads`.
    fn cons_of(heads: Vec<RuntimeTypePredicate>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.lists = ListShapes::exact(FiniteSet::lit(ListShape::NonEmpty), heads);
        predicate
    }

    /// THE ONE-SIDED-FILTER LAW, stated as a property (fz-kdt.107 step 3).
    ///
    /// A head load rejects exactly and accepts erasingly, so DISJOINT heads
    /// are the only claimable separation and any overlap at all erases. The
    /// second half is the one that was refuted by measurement: reading
    /// "the heads differ" as separation seats `[int]` ahead of `[int | :ok]`,
    /// and `[1, :ok]` then reaches a body that reads every element as an int.
    #[test]
    fn list_heads_separate_only_where_they_are_disjoint() {
        let ints_list = cons_of(vec![ints()]);
        let atoms_list = cons_of(vec![atom("ok")]);
        let mixed_list = cons_of(vec![{
            let mut mixed = ints();
            mixed.atoms = FiniteSet::lit("ok".to_string());
            mixed
        }]);

        assert!(
            !ints_list.overlaps(&atoms_list),
            "disjoint heads are disjoint tests: no list has a first element that is both",
        );
        assert!(
            !ints_list.overlaps_on_an_erasing_axis(&atoms_list),
            "disjoint heads are the one separation a head load can claim",
        );

        assert!(
            ints_list.overlaps(&mixed_list),
            "[1, ..] passes both a [int] head test and a [int | :ok] one",
        );
        assert!(
            ints_list.overlaps_on_an_erasing_axis(&mixed_list),
            "heads that overlap at all erase: the head says nothing about the tail, so a seat \
             must fall back to surface coverage",
        );
        assert!(
            ints_list.contained_in(&mixed_list) && !mixed_list.contained_in(&ints_list),
            "and the narrower head is still the narrower test",
        );
    }

    /// THE `[]` EXCEPTION: two tests meeting only at the empty list do not
    /// erase, because `[]` is one value carrying nothing for a body to
    /// misread -- the same reason the atom axis separates.
    #[test]
    fn two_tests_meeting_only_at_the_empty_list_do_not_erase() {
        let mut empty_or_ints = RuntimeTypePredicate::none();
        empty_or_ints.lists =
            ListShapes::exact(FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty]), vec![ints()]);
        let mut empty_or_atoms = RuntimeTypePredicate::none();
        empty_or_atoms.lists = ListShapes::exact(
            FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty]),
            vec![atom("ok")],
        );
        assert!(
            empty_or_ints.overlaps(&empty_or_atoms),
            "both admit [], so one value passes both tests",
        );
        assert!(
            !empty_or_ints.overlaps_on_an_erasing_axis(&empty_or_atoms),
            "meeting at [] is not a blind meeting: the value carries nothing either body reads",
        );
    }

    /// A head the projection could not name is a head the seat may not read as
    /// separation: the shape-only reading erases against everything that
    /// admits a cons cell.
    #[test]
    fn a_head_blind_list_axis_erases_against_every_cons_test() {
        let blind = list_of_anything();
        let ints_list = cons_of(vec![ints()]);
        assert!(
            blind.overlaps_on_an_erasing_axis(&ints_list),
            "what the projection declines to ask, a seat may not claim as separation",
        );
        assert!(
            ints_list.contained_in(&blind) && !blind.contained_in(&ints_list),
            "the shape-only reading is the over-approximation, so it contains the exact one",
        );
    }

    /// fz-kdt.145, the constructive invariant: every arity ANY sub-predicate
    /// can reach is reported, so every lowering registers a schema for it.
    ///
    /// The prototype of the list axis reported tuple arities through tuple
    /// positions only. An arity reachable solely through a list HEAD went
    /// unregistered, the interpreter's head test rejected the tuple it could
    /// not name, and the JIT -- which registers from the same walk but reads
    /// schema ids the native driver had already minted -- said yes: three
    /// interpreter-only parity breaks from one missing recursion. The walk is
    /// now one exhaustive match over the axis table
    /// (`RuntimeTypePredicate::sub_predicates_on`), so the next nested axis
    /// cannot repeat it without failing to compile.
    #[test]
    fn every_arity_a_sub_predicate_can_reach_is_reported_for_registration() {
        let triple = tuple(vec![vec![ints(), ints(), ints()]]);
        let through_a_head = cons_of(vec![triple]);
        assert_eq!(
            through_a_head.tuple_arities_at_every_depth(),
            BTreeSet::from([3]),
            "an arity reachable only through a list head is still an arity the test asks about",
        );

        let pair_over_a_list = tuple(vec![vec![atom("ok"), through_a_head]]);
        assert_eq!(
            pair_over_a_list.tuple_arities_at_every_depth(),
            BTreeSet::from([2, 3]),
            "and the walk composes: a head inside a position inside a tuple reports every rung",
        );
    }

    /// The P1 claim in lattice terms: two annotated tagged tuples are two
    /// questions, and the seat may treat the difference as separation.
    #[test]
    fn tagged_tuples_that_differ_at_an_atom_position_are_two_questions() {
        let cont = tuple(vec![vec![atom("cont"), ints()]]);
        let halt = tuple(vec![vec![atom("halt"), ints()]]);
        assert_ne!(cont, halt, "the two tests must not be one question");
        assert!(!cont.overlaps(&halt), "no value passes both tests");
        assert!(
            !cont.overlaps_on_an_erasing_axis(&halt),
            "an atom position separates, so a seat needs no surface check here",
        );
    }

    /// The Scope-A carve-out, stated as a property: a LIST position is blind,
    /// so two shapes that differ only there stay one question however
    /// different their types (fz-kdt.138 is what changes this).
    #[test]
    fn a_nested_list_position_stays_erasing() {
        let mut empty_list = RuntimeTypePredicate::none();
        empty_list.lists = ListShapes::exact(FiniteSet::lit(ListShape::Empty), Vec::new());
        let mut cons = RuntimeTypePredicate::none();
        cons.lists = ListShapes::exact(FiniteSet::lit(ListShape::NonEmpty), vec![ints()]);
        let initial = tuple(vec![vec![empty_list, ints()]]);
        let grown = tuple(vec![vec![cons, ints()]]);
        assert!(
            initial.overlaps(&grown),
            "the lowerings do not test a list position, so both tests admit the same tuples",
        );
        assert!(
            initial.overlaps_on_an_erasing_axis(&grown),
            "a position no lowering decides may never be claimed as separation",
        );
    }

    /// Correlation survives the projection: a two-clause union is two shapes,
    /// and the cross terms neither clause names are not admitted.
    #[test]
    fn two_tuple_clauses_stay_two_shapes() {
        let mixed = tuple(vec![vec![atom("cont"), ints()], vec![atom("halt"), atom("ok")]]);
        let blind_cross = tuple(vec![vec![atom("cont"), list_of_anything()]]);
        assert!(
            mixed.overlaps(&blind_cross),
            "a blind list position makes {{:cont, [..]}} indistinguishable from {{:cont, int}}",
        );
        let cross_of_exact_positions = tuple(vec![vec![atom("cont"), atom("ok")]]);
        assert!(
            !mixed.overlaps(&cross_of_exact_positions),
            "{{:cont, :ok}} is a cross term neither clause names, and the shapes keep it out: \
             joining the clauses position-wise would have admitted it",
        );
    }

    /// Containment is per position, and a wider position is what widens a
    /// shape.
    #[test]
    fn a_shape_contains_another_when_every_position_does() {
        let mut cont_or_halt = RuntimeTypePredicate::none();
        cont_or_halt.atoms = FiniteSet::finite(["cont".to_string(), "halt".to_string()]);
        let wide = tuple(vec![vec![cont_or_halt, ints()]]);
        let narrow = tuple(vec![vec![atom("cont"), ints()]]);
        assert!(
            narrow.contained_in(&wide),
            "a narrower atom position is a narrower shape"
        );
        assert!(!wide.contained_in(&narrow), "and containment is not mutual");
        assert!(
            wide.overlaps(&narrow),
            "a {{:cont, 3}} passes both, so the pair is a seating question at all",
        );
        assert!(
            !wide.overlaps_on_an_erasing_axis(&narrow),
            "and every position they overlap at separates, so precision may settle the seat \
             without a surface-coverage check",
        );
    }

    /// An inexact clause degrades to the arity-only reading rather than
    /// claiming a precision the projection could not produce.
    #[test]
    fn an_inexact_tuple_axis_is_the_arity_only_reading() {
        let exact = tuple(vec![vec![atom("cont"), ints()]]);
        let arity_only = RuntimeTypePredicate::tuple_arity(2);
        assert!(exact.contained_in(&arity_only), "every shape is inside its own arity");
        assert!(
            !arity_only.contained_in(&exact),
            "and the arity admits more than the shape"
        );
        assert!(exact.overlaps(&arity_only));
        assert!(
            exact.overlaps_on_an_erasing_axis(&arity_only),
            "an arity-only test sees nothing of the payload, so it separates nothing",
        );
    }

    /// The arity reading is derived from the shapes, so the coarse callers and
    /// the precise ones can never disagree about which tuples are admitted.
    #[test]
    fn the_arity_reading_is_derived_from_the_shapes() {
        let predicate = tuple(vec![vec![atom("cont"), ints()], vec![ints(), ints(), ints()]]);
        assert_eq!(*predicate.tuples.arities(), FiniteSet::finite([2, 3]));
        assert_eq!(*RuntimeTypePredicate::none().tuples.arities(), FiniteSet::none());
        assert_eq!(*RuntimeTypePredicate::any().tuples.arities(), FiniteSet::any());
        assert_eq!(
            *RuntimeTypePredicate::tuple_arity(3).tuples.arities(),
            FiniteSet::lit(3)
        );
    }

    /// Nested arities are reported, because a nested position can only be
    /// tested where the runtime has a schema to name.
    #[test]
    fn every_nested_tuple_arity_is_reported_for_schema_registration() {
        let inner = tuple(vec![vec![ints(), ints(), ints()]]);
        let outer = tuple(vec![vec![atom("ok"), inner]]);
        assert_eq!(
            outer.tuple_arities_at_every_depth(),
            BTreeSet::from([2, 3]),
            "the inner 3-tuple's schema is what makes the nested position askable",
        );
    }
}
