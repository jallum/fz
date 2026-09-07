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
            // Callable membership is CONSTRUCTION membership: the heap word
            // at `+8` names the construction a closure was minted from, and a
            // construction is a function together with the capture types it
            // closed over (fz-kdt.127). A test admits a value when the
            // value's construction shape lies INSIDE a shape the test names,
            // position by position, so the axis separates exactly as far as
            // the capture sub-questions do -- `#66 over int` and `#66 over
            // float` are two tests, `#66 over [int]` and `#66 over
            // [int | :ok]` erase the tail exactly as the list axis does.
            Self::Callables => AxisPrecision::PerPosition,
            // Numbers are PRESENCE BITS here, never value sets: the projection
            // records "INT is present" and drops literals and brands alike
            // (`Types::runtime_type_predicate`, which never reads the brand
            // slot -- a refinement narrows WHICH ints a type admits, and this
            // axis only asks whether an int arrives). So the reason this axis is
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
    /// The whole callable axis: WHICH construction, not merely "a callable".
    /// A closure value's heap word at `+8` names the construction it was
    /// minted from -- the code AND the capture types that construction closed
    /// over -- so the callable a value is is runtime-observable at the same
    /// grain the lattice's closure literal names it. See [`CallableShapes`].
    pub(crate) callables: CallableShapes,
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
            callables: CallableShapes::none(),
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
            callables: CallableShapes::any(),
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
            // A callable test reads a code word, and the word names a
            // construction whose capture shapes are then compared to the
            // test's STATICALLY -- the value's captures are never loaded --
            // so a tuple nested in a capture is a question about the shape,
            // not about the value, and needs no schema of its own.
            //
            // A scalar axis decides a value outright, and a struct, map,
            // binary or resource test reads a schema id or a kind -- never
            // anything the value CONTAINS.
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
                RuntimeTestAxis::Callables => self.callables.erasing_overlap(&other.callables),
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
    /// `callsite_dispatch::seating` is the relation that makes a seat sound;
    /// this is one half of its coverage answer.
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

    /// Whether ONE value could pass both tests.
    ///
    /// Axis by axis, because a value reaches exactly the axes its kind names:
    /// two tests can both admit a value only where some axis admits one to
    /// both. It is the SEPARATION question `callsite_dispatch::seating` asks
    /// first of a pair of arms, one subject at a time -- a plan row is a
    /// conjunction over its subjects, so one subject that admits nothing to
    /// both keeps the two arms apart outright, whatever the others say
    /// (fz-kdt.186).
    ///
    /// It OVER-ESTIMATES, axis by axis, and that is the direction a seat needs:
    /// every axis answers yes wherever it cannot rule a shared value out -- two
    /// cofinite sets, a head neither side asks, an inexact tuple or callable
    /// store -- so a `false` here is a claim no value passes both tests, and
    /// never merely that this layer could not tell.
    ///
    /// The bridge from SURFACES to tests is the other half, and it holds
    /// wherever the projection is a coarsening of the surface it came from:
    /// two surfaces that share a value then project to two tests that overlap.
    /// `callsite_dispatch::tests::a_separated_pair_of_tests_is_a_disjoint_pair_of_surfaces`
    /// holds every axis of a wide battery to it. It is not universal, and the
    /// gap is a projection defect rather than a fact about this relation: a
    /// tuple clause with a SUBTRACTED signature loses that whole arity in
    /// `runtime_type_predicate_tuple_arities`, so `{any, any} & not({int,
    /// int})` -- a surface holding every pair that is not two ints -- projects
    /// to a test that admits nothing and does not overlap ITSELF. No seat and
    /// no drop may turn on that: `callsite_dispatch::seating` treats a position
    /// where the two arms ask the IDENTICAL question as no separation at all,
    /// so an unrealizable test can only ever describe an arm the plan's own
    /// emitted test already refuses.
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
    /// axis said before fz-kdt.107 step 3 -- `jobs::transport` still reads it
    /// alone.
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

/// How much of a value a reading looks at.
///
/// The gap between the two readings is the LIST SPINE, and nothing else. Every
/// tuple position a shape carries is one all three lowerings decide
/// (fz-kdt.138), so the two scopes agree there; a cons cell's head is one load
/// the lowerings can afford and its tail is not, so they part company on the
/// list axis alone. That is what makes the difference measurable: subtracting
/// one reading from the other is exactly the one-sided filter's acceptance
/// residue, which is what the [`surface_membership`] tripwire counts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PositionScope {
    /// What the three lowerings decide: every tuple position, and one head per
    /// cons-admitting list clause.
    Lowered,
    /// What the surface names: every tuple position, and every ELEMENT of a
    /// list, under one clause's element question. The gap between this and
    /// `Lowered` IS the population of values a test admits into a body that
    /// never named them.
    Full,
}

/// Whether one shape's positions could all be satisfied by one tuple.
///
/// A position is a full predicate, so this is the ordinary overlap question
/// asked position-wise. Every position is asked: a tuple position that holds
/// a LIST used to be excluded here and from all three lowerings alike, which
/// made it count as overlapping whatever it met (fz-kdt.119's Scope-A
/// carve-out, retired by fz-kdt.138).
fn shapes_overlap(left: &[RuntimeTypePredicate], right: &[RuntimeTypePredicate]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(l, r)| l.overlaps(r))
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
                ours.len() == theirs.len() && ours.iter().zip(theirs).all(|(ours, theirs)| theirs.contained_in(ours))
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
            other.shapes.iter().any(|right| {
                shapes_overlap(left, right) && left.iter().zip(right).any(|(l, r)| l.overlaps_on_an_erasing_axis(r))
            })
        })
    }
}

/// One callable CONSTRUCTION as a runtime test sees it: the code a value was
/// minted from and, per capture position, the question that capture answers.
///
/// This is the lattice's closure literal `closure[L](captures)` projected the
/// way a tuple clause is projected into a [`TupleShapes`] shape -- the
/// identity stays, and every capture becomes its own [`RuntimeTypePredicate`].
/// Both doors stamp exactly this onto a value at mint time, because a
/// construction wrapper is one function at one capture layout, so it is the
/// grain the runtime can answer at (fz-kdt.127).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallableShape {
    pub(crate) target: ClosureTarget,
    pub(crate) captures: Vec<RuntimeTypePredicate>,
}

impl CallableShape {
    /// Whether every value minted through this construction is one `other`
    /// names: the same code, and every capture's question inside `other`'s.
    ///
    /// A construction's capture types are the ANNOTATION the mint stamped, so
    /// this is the containment of one annotation in another -- capture by
    /// capture, [`RuntimeTypePredicate::contained_in`], which is containment of
    /// the projected TESTS and not of the semantic types they came from -- and
    /// not the overlap of two tests. A
    /// construction over `int | float` is not one a body compiled for `int`
    /// captures may receive, whatever the value in that capture happens to be,
    /// because the layout the capture was STORED in is the construction's and
    /// not the value's (fz-kdt.167).
    fn inside(&self, other: &Self) -> bool {
        self.target == other.target
            && self.captures.len() == other.captures.len()
            && self
                .captures
                .iter()
                .zip(&other.captures)
                .all(|(ours, theirs)| ours.contained_in(theirs))
    }

    /// Whether one construction could satisfy both shapes' capture questions.
    fn overlaps(&self, other: &Self) -> bool {
        self.target == other.target
            && self.captures.len() == other.captures.len()
            && self.captures.iter().zip(&other.captures).all(|(l, r)| l.overlaps(r))
    }

    /// Whether the two shapes meet at a capture position NEITHER can see past.
    fn erasing_overlap(&self, other: &Self) -> bool {
        self.overlaps(other)
            && self
                .captures
                .iter()
                .zip(&other.captures)
                .any(|(l, r)| l.overlaps_on_an_erasing_axis(r))
    }
}

/// The callable constructions a test admits, one shape per closure literal.
///
/// This is the callable axis' answer to [`TupleShapes`] and it follows the
/// same discipline: `shapes` holds one entry per positive closure-literal
/// CLAUSE of the descriptor it was projected from, and `exact` records whether
/// every clause could be shaped. A clause that pins several literals at once
/// is an intersection and is not one shape, so it degrades the whole axis to
/// the target-only reading -- which is what this layer asked before fz-kdt.127
/// and is a sound over-approximation of it. The target set is DERIVED from the
/// shapes when the axis is exact, never stated twice, so the two readings
/// cannot drift apart.
///
/// ADMISSION of a value is [`Self::admits`]: CONTAINMENT of the value's
/// construction shape in a shape named here, never overlap. The two-test
/// relations a dispatch SEAT reads -- [`Self::contains_all`],
/// [`Self::overlaps`], [`Self::erasing_overlap`] -- are the ordinary ones,
/// exactly as for tuples.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallableShapes {
    targets: FiniteSet<ClosureTarget>,
    shapes: Vec<CallableShape>,
    exact: bool,
}

impl CallableShapes {
    /// No callable at all: the exact reading of no clauses, which is what
    /// projecting a callable-free type produces.
    pub(crate) fn none() -> Self {
        Self::exact(Vec::new())
    }

    /// Every callable, of every construction.
    pub(crate) fn any() -> Self {
        Self::target_only(FiniteSet::any())
    }

    /// One shape per clause, and the targets they name.
    pub(crate) fn exact(shapes: Vec<CallableShape>) -> Self {
        Self {
            targets: FiniteSet::finite(shapes.iter().map(|shape| shape.target)),
            shapes,
            exact: true,
        }
    }

    /// The coarse reading: these targets, and nothing about their captures.
    pub(crate) fn target_only(targets: FiniteSet<ClosureTarget>) -> Self {
        Self {
            targets,
            shapes: Vec::new(),
            exact: false,
        }
    }

    /// Which functions the test admits values minted from. Always answerable,
    /// and what the native emitter reads to apply the cofinite complement.
    pub(crate) fn targets(&self) -> &FiniteSet<ClosureTarget> {
        &self.targets
    }

    pub(crate) fn is_none(&self) -> bool {
        self.targets.is_none()
    }

    pub(crate) fn is_any(&self) -> bool {
        self.targets.is_any()
    }

    #[cfg(test)]
    pub(crate) fn is_exact(&self) -> bool {
        self.exact
    }

    /// Whether this test ENUMERATES `shape`: membership in the listed side,
    /// before the cofinite complement is applied. The emitters read this to
    /// pick the addresses they compare against and apply the complement
    /// themselves.
    pub(crate) fn enumerates(&self, shape: &CallableShape) -> bool {
        if self.exact {
            self.shapes.iter().any(|ours| shape.inside(ours))
        } else {
            self.targets.values.contains(&shape.target)
        }
    }

    /// Whether this test admits a value minted through the construction
    /// `shape`.
    pub(crate) fn admits(&self, shape: &CallableShape) -> bool {
        self.enumerates(shape) != self.targets.cofinite
    }

    /// Whether every construction `other` admits, this axis admits too.
    ///
    /// An inexact axis is the target-only reading, which admits every capture
    /// layout of its targets, so it contains anything of them; and nothing
    /// exact contains it.
    fn contains_all(&self, other: &Self) -> bool {
        if !self.targets.contains_all(&other.targets) {
            return false;
        }
        if !self.exact {
            return true;
        }
        if !other.exact {
            return false;
        }
        other
            .shapes
            .iter()
            .all(|theirs| self.shapes.iter().any(|ours| theirs.inside(ours)))
    }

    /// Whether one construction could pass both tests.
    fn overlaps(&self, other: &Self) -> bool {
        if !self.targets.overlaps(&other.targets) {
            return false;
        }
        if !self.exact || !other.exact {
            return true;
        }
        self.shapes
            .iter()
            .any(|left| other.shapes.iter().any(|right| left.overlaps(right)))
    }

    /// Whether one construction could pass both tests through a capture
    /// position NEITHER test can see past. Two shapes that meet only through
    /// captures whose own questions separate are a real separation, and a seat
    /// may skip the surface check for them.
    fn erasing_overlap(&self, other: &Self) -> bool {
        if !self.targets.overlaps(&other.targets) {
            return false;
        }
        if !self.exact || !other.exact {
            return true;
        }
        self.shapes
            .iter()
            .any(|left| other.shapes.iter().any(|right| left.erasing_overlap(right)))
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

/// Which CONSTRUCTION a runtime code word denotes.
///
/// The word a closure carries at `+8` is the backend's, not the type lattice's:
/// one callable can be minted through several code paths, and a backend is free
/// to name them however it likes. The backend that minted them is therefore the
/// authority on reading them back, and it answers here with the construction's
/// shape -- the function, and the projected capture types it closed over.
/// `None` is a code word the program never described, which no finite callable
/// set can name.
pub(crate) type CallableIdentities<'a> = dyn Fn(u64) -> Option<CallableShape> + 'a;

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

/// Read the rest of a cons cell.
///
/// Mirrors [`ListHeadReader`]: the side that owns the representation answers.
/// `None` is a tail the reader could not produce, which ends a spine walk --
/// what the representation declines to show, this layer does not judge.
pub(crate) type ListTailReader<'a> = dyn Fn(RuntimeAnyValue) -> Option<RuntimeAnyValue> + 'a;

/// Everything the interpreter's matcher needs to read a value back.
///
/// The schema maps are the runtime's own numbering, so they are handed in
/// rather than derived here; the function slots are the representation's
/// owners answering questions only they can.
pub(crate) struct RuntimeValueReader<'a> {
    pub(crate) module: &'a Module,
    pub(crate) tuple_schema_ids: &'a HashMap<usize, u32>,
    pub(crate) named_schema_ids: &'a HashMap<String, u32>,
    pub(crate) callables: &'a CallableIdentities<'a>,
    pub(crate) fields: &'a TupleFieldReader<'a>,
    pub(crate) list_head: &'a ListHeadReader<'a>,
    pub(crate) list_tail: &'a ListTailReader<'a>,
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
        RuntimeTestAxis::Lists => match list_shape_of(value) {
            Some(ListShape::Empty) => predicate.lists.shapes().contains(&ListShape::Empty),
            Some(ListShape::NonEmpty) => {
                predicate.lists.shapes().contains(&ListShape::NonEmpty)
                    && matches_list_elements(&predicate.lists, reader, value, scope)
            }
            None => false,
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

/// Read a closure value's CONSTRUCTION and ask the predicate about it.
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
        Some(shape) => predicate.callables.admits(&shape),
        None => predicate.callables.targets().cofinite,
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
/// every position answers yes. Both scopes ask every position -- fz-kdt.138
/// retired the last position any lowering declined -- so this function and the
/// emitted code answer alike by construction. The `scope` is threaded through
/// because a position's own value can be a LIST, and there the two readings do
/// differ: see [`matches_list_elements`].
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
            (reader.fields)(value, index).is_some_and(|field| {
                RuntimeTestAxis::of_value(field)
                    .iter()
                    .any(|axis| axis_admits(position, reader, field, *axis, scope))
            })
        })
    })
}

/// Which list shape a runtime value is, or `None` where it is not a list.
///
/// The ONE cons-cell reading in this layer: the list axis answers with it and
/// the element walk stops where it says anything but `NonEmpty`. `[]` reaches
/// here as its own variant -- `AnyValue::from_ref` normalizes an empty-list ref
/// before it ever tags one -- so the `is_empty_list` arm states that invariant
/// rather than adding a second reading of it.
fn list_shape_of(value: RuntimeAnyValue) -> Option<ListShape> {
    match value {
        RuntimeAnyValue::EmptyList => Some(ListShape::Empty),
        RuntimeAnyValue::HeapRef(value_ref) if value_ref.tag() == ValueKind::LIST => {
            Some(if value_ref.is_empty_list() {
                ListShape::Empty
            } else {
                ListShape::NonEmpty
            })
        }
        _ => None,
    }
}

/// Whether some clause's element question admits this cons cell, and how far
/// the `scope` looks to decide it.
///
/// The shape half above has already decided that a cons cell is admitted at
/// all; this is the ELEMENT half, and it is skipped where the axis asks the
/// head nothing -- the shape-only reading this layer had before fz-kdt.107
/// step 3, and the one fz-kdt.146's degrade rule still falls back to. Such an
/// axis has no `Full` content to give, so it is honestly inert under both
/// scopes rather than dishonestly silent under one.
///
/// - Under [`PositionScope::Lowered`] exactly ONE head is loaded and put to the
///   disjunction of the clauses' head questions. The emitted native test is the
///   same disjunction under the same cons guard, so this function and the
///   compiled code answer alike.
/// - Under [`PositionScope::Full`] the reading is what the TYPE says rather
///   than what a test can afford: a list clause is homogeneous by construction
///   (`ListSig` carries one element type for the whole list), so lying inside
///   the surface means SOME ONE clause's element question admits EVERY element.
///   Each element is asked under `Full` in turn, so a list inside a list, or a
///   list inside a tuple position, walks too.
///
/// The gap between the two readings is the one-sided filter's acceptance
/// residue -- the head is exact on rejection and erasing on acceptance, and the
/// tail is what no emitted test reads. That gap is what the
/// [`surface_membership`] tripwire measures.
///
/// COST. The `Lowered` reading is one load and one disjunction. The `Full`
/// reading is O(clauses x length) element questions on a flat list, and
/// O(clauses x outer x inner) one level of nesting down, which is why it is
/// asked only behind the tripwire's env gate and never on the production
/// answer.
fn matches_list_elements(
    lists: &ListShapes,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
    scope: PositionScope,
) -> bool {
    if !lists.asks_the_head() {
        return true;
    }
    match scope {
        PositionScope::Lowered => {
            let Some(head) = (reader.list_head)(value) else {
                // A head the representation's owner could not produce is a head
                // no question can be asked about, so the shape half stands
                // alone.
                return true;
            };
            lists
                .heads()
                .iter()
                .any(|question| admits_element(question, reader, head, scope))
        }
        PositionScope::Full => lists
            .heads()
            .iter()
            .any(|question| first_refused_element(question, reader, value).is_none()),
    }
}

/// Whether `question` admits `element` on any axis the element's kind reaches.
fn admits_element(
    question: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    element: RuntimeAnyValue,
    scope: PositionScope,
) -> bool {
    RuntimeTestAxis::of_value(element)
        .iter()
        .any(|axis| axis_admits(question, reader, element, *axis, scope))
}

/// The first element of this list `question` refuses, and where it sits.
///
/// `None` is NO refusal this walk can name, which is always read as admitted:
/// the question answered every element, or the spine ended, or the reader
/// declined to open a cell, or the walk hit its limit. What the representation
/// will not show, this layer does not judge.
///
/// The walk stops at anything that is not a cons cell -- the empty list and an
/// improper tail alike -- because neither is an element. It terminates on two
/// counts: a cons cell's tail is built before the cell is, so a spine the
/// runtime builds cannot be cyclic, and [`ELEMENT_WALK_LIMIT`] bounds it
/// anyway, because termination inside a dispatch test should be a fact of the
/// code rather than a property of the heap it reads.
fn first_refused_element(
    question: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    list: RuntimeAnyValue,
) -> Option<(usize, RuntimeAnyValue)> {
    let mut cursor = list;
    let mut index = 0;
    while list_shape_of(cursor) == Some(ListShape::NonEmpty) {
        if index == ELEMENT_WALK_LIMIT {
            eprintln!(
                "surface-membership walk limit: a spine longer than {ELEMENT_WALK_LIMIT} elements is not \
                 judged, so this list counts as inside the question it was asked"
            );
            return None;
        }
        let head = (reader.list_head)(cursor)?;
        if !admits_element(question, reader, head, PositionScope::Full) {
            return Some((index, head));
        }
        cursor = (reader.list_tail)(cursor)?;
        index += 1;
    }
    None
}

/// The longest spine the `Full` reading walks. A list past it is not judged and
/// says so on stderr, which only the tripwire's env gate can reach.
const ELEMENT_WALK_LIMIT: usize = 1 << 16;

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

/// The dynamic surface-membership tripwire (fz-kdt.135, fz-kdt.144).
///
/// A test is a projection, so a value can pass every question an arm asks and
/// still lie outside the surface that arm's body was compiled for. The static
/// gates reason about that hazard on hand-picked pairs; this measures it, on
/// the production path, over whatever the corpus actually runs.
///
/// The production answer is [`PositionScope::Lowered`], which is what the three
/// lowerings can afford. The tripwire re-asks the same value's own axes under
/// [`PositionScope::Full`], which is what the surface names. A value admitted
/// by the first reading and refused by the second passed a test no shape of the
/// arm's surface names -- exactly the blind routing this class of defect is made
/// of.
///
/// What the two readings disagree about is the LIST SPINE: a head load is exact
/// on rejection and erasing on acceptance, so the tail is the one thing no
/// emitted test reads. Tuple positions are asked identically by both scopes
/// (fz-kdt.138) and scalar and content-blind axes coincide, so a finding here is
/// always a list whose later elements leave the clause its head answered.
///
/// It is off unless `FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP` is set; `abort` makes
/// each finding fatal, anything else counts them and reports each on stderr,
/// which is what a corpus census reads. The report carries the offending
/// element and its index, because a list escape is untriageable from the value's
/// kind and the test text alone.
///
/// INTERPRETER ONLY, and that is the whole instrument rather than half of one:
/// every door answers the same `Lowered` question over the same dispatch plans,
/// so the escaping POPULATION is door-independent by construction. What differs
/// between the doors is the HARM -- interp survives on dynamic tags where the
/// native doors read the element through a grounded accessor -- and harm is what
/// the three-door behaviour sweep measures.
///
/// The measured population is
/// `compiler2_no_value_reaches_a_construction_member_that_never_named_it`'s
/// table, and the corpus recipe is in `.agent/docs/dispatch-matrix.md`.
pub(crate) mod surface_membership {
    use super::{
        ListShape, PositionScope, RuntimeTestAxis, RuntimeTypePredicate, RuntimeValueReader, axis_admits,
        first_refused_element, list_shape_of,
    };
    use fz_runtime::any_value::AnyValue as RuntimeAnyValue;
    use std::cell::Cell;

    pub(crate) const ASSERT_SURFACE_MEMBERSHIP_ENV: &str = "FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP";

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(crate) enum Mode {
        /// The environment has not been read on this thread yet. Never
        /// observed by `observe`: `mode` resolves it on first ask.
        Unread,
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

    thread_local! {
        static MODE: Cell<Mode> = const { Cell::new(Mode::Unread) };
        static ESCAPES: Cell<usize> = const { Cell::new(0) };
        /// The DENOMINATOR of [`ESCAPES`]: how many admitted values this
        /// tripwire has looked at. A zero escape count says nothing until this
        /// says something was looked at (fz-kdt.187).
        static OBSERVATIONS: Cell<usize> = const { Cell::new(0) };
    }

    /// What this thread does with a finding. A process-wide default comes from
    /// the environment, which is how a fixture is swept through the real `fz2`
    /// binary; an in-process driver installs [`SurfaceMembershipCensus`]
    /// instead. What keeps one census from counting a neighbour's escapes is
    /// NOT thread ownership -- under `--test-threads=1` libtest runs every
    /// case serially on the main thread, so the thread-local persists between
    /// cases -- it is [`SurfaceMembershipCensus`]'s RAII save/restore: install
    /// saves both cells and `Drop` restores them (the `dispatch_stress`
    /// shape, for the same reason).
    pub(crate) fn mode() -> Mode {
        MODE.with(|mode| match mode.get() {
            Mode::Unread => {
                let read = mode_from_env();
                mode.set(read);
                read
            }
            settled => settled,
        })
    }

    fn mode_from_env() -> Mode {
        match std::env::var(ASSERT_SURFACE_MEMBERSHIP_ENV) {
            Err(_) => Mode::Off,
            Ok(value) if value == "abort" => Mode::Abort,
            Ok(_) => Mode::Report,
        }
    }

    /// Check one admitted value against the surface the test was projected
    /// from, and report it where it is not in there.
    pub(crate) fn observe(predicate: &RuntimeTypePredicate, reader: &RuntimeValueReader<'_>, value: RuntimeAnyValue) {
        let mode = mode();
        if mode == Mode::Off {
            return;
        }
        OBSERVATIONS.with(|observations| observations.set(observations.get() + 1));
        let Some(witness) = escaped(predicate, reader, value) else {
            return;
        };
        let report = format!(
            "surface-membership escape: a value the test admits lies outside every shape it names \
             ({witness}, test {predicate})",
        );
        ESCAPES.with(|escapes| escapes.set(escapes.get() + 1));
        match mode {
            Mode::Abort => panic!("{report}"),
            _ => eprintln!("{report}"),
        }
    }

    /// Reports every finding on this thread and counts them, for as long as it
    /// lives, then puts the previous setting and tallies back.
    ///
    /// The census the shell recipe reads off stderr, available to an
    /// in-process driver as two numbers: the findings, and how many values were
    /// looked at to find them.
    #[cfg(test)]
    pub(crate) struct SurfaceMembershipCensus {
        mode: Mode,
        escapes: usize,
        observations: usize,
    }

    #[cfg(test)]
    impl SurfaceMembershipCensus {
        pub(crate) fn install() -> Self {
            Self {
                mode: MODE.with(|mode| mode.replace(Mode::Report)),
                escapes: ESCAPES.with(|escapes| escapes.replace(0)),
                observations: OBSERVATIONS.with(|observations| observations.replace(0)),
            }
        }

        /// How many values have reached a body whose surface never named them
        /// since this census was installed.
        pub(crate) fn escapes(&self) -> usize {
            ESCAPES.with(Cell::get)
        }

        /// How many admitted values the tripwire has looked at since this
        /// census was installed -- the denominator [`Self::escapes`] speaks
        /// for. A census that observes nothing reports no escape for the same
        /// reason an empty room is quiet (fz-kdt.187).
        pub(crate) fn observations(&self) -> usize {
            OBSERVATIONS.with(Cell::get)
        }
    }

    #[cfg(test)]
    impl Drop for SurfaceMembershipCensus {
        fn drop(&mut self) {
            MODE.with(|mode| mode.set(self.mode));
            ESCAPES.with(|escapes| escapes.set(self.escapes));
            OBSERVATIONS.with(|observations| observations.set(self.observations));
        }
    }

    /// Admitted by the reading the lowerings share, refused by the reading the
    /// surface names -- asked on the value's OWN axes, which is the same
    /// disjunction [`super::matches_runtime_type_predicate`] answers, so the
    /// first half of this is literally the production answer.
    ///
    /// `Some` is the witness a triage reads: what the value is, and where the
    /// surface first refuses it.
    fn escaped(
        predicate: &RuntimeTypePredicate,
        reader: &RuntimeValueReader<'_>,
        value: RuntimeAnyValue,
    ) -> Option<String> {
        let axes = RuntimeTestAxis::of_value(value);
        let admits = |scope| {
            axes.iter()
                .any(|axis| axis_admits(predicate, reader, value, *axis, scope))
        };
        if !admits(PositionScope::Lowered) || admits(PositionScope::Full) {
            return None;
        }
        let value_text = format!("value {}", render(reader, value, RENDER_DEPTH));
        Some(match refused_element(predicate, reader, value) {
            Some(refusal) => format!("{value_text}, {refusal}"),
            None => value_text,
        })
    }

    /// Which element broke the clause that got furthest along a list subject.
    ///
    /// A spine escape means EVERY clause refuses some element, so the single
    /// most useful fact is where the most tolerant of them gave up: that is the
    /// element the arm's surface does not name and the body behind it will read
    /// anyway. A value that is not a cons cell has no such element -- its
    /// rendering already shows the nested list that broke it.
    fn refused_element(
        predicate: &RuntimeTypePredicate,
        reader: &RuntimeValueReader<'_>,
        value: RuntimeAnyValue,
    ) -> Option<String> {
        if list_shape_of(value) != Some(ListShape::NonEmpty) {
            return None;
        }
        let (index, element) = predicate
            .lists
            .heads()
            .iter()
            .filter_map(|question| first_refused_element(question, reader, value))
            .max_by_key(|(index, _)| *index)?;
        Some(format!(
            "element {index} = {} is outside every clause the surface names",
            render(reader, element, RENDER_DEPTH),
        ))
    }

    /// How many levels down, and how many items across, a witness is rendered.
    ///
    /// Bounded on both axes because a report able to print an unbounded value is
    /// a report able to hang the program it instruments.
    const RENDER_DEPTH: usize = 3;
    const RENDER_WIDTH: usize = 8;

    /// A value as the reader can show it.
    ///
    /// Only the representation's owner can read a heap value, so this asks the
    /// same closures the matcher does and nothing else; what the reader declines
    /// to produce prints as the kind it is.
    fn render(reader: &RuntimeValueReader<'_>, value: RuntimeAnyValue, depth: usize) -> String {
        match value {
            RuntimeAnyValue::Null => "null".to_string(),
            RuntimeAnyValue::Int(int) => int.to_string(),
            RuntimeAnyValue::Float(bits) => f64::from_bits(bits).to_string(),
            RuntimeAnyValue::Atom(atom_id) => match reader.module.atom_names.get(atom_id as usize) {
                Some(name) => format!(":{name}"),
                None => format!(":<atom {atom_id}>"),
            },
            RuntimeAnyValue::EmptyList => "[]".to_string(),
            RuntimeAnyValue::HeapRef(_) => match list_shape_of(value) {
                Some(_) => render_spine(reader, value, depth),
                None => match super::struct_schema_of(value).and_then(|schema| reader.tuple_arity_of(schema)) {
                    Some(arity) => render_tuple(reader, value, arity, depth),
                    None => format!("<{:?}>", value.kind()),
                },
            },
        }
    }

    fn render_spine(reader: &RuntimeValueReader<'_>, list: RuntimeAnyValue, depth: usize) -> String {
        if depth == 0 {
            return "[...]".to_string();
        }
        let mut elements = Vec::new();
        let mut cursor = list;
        while list_shape_of(cursor) == Some(ListShape::NonEmpty) {
            if elements.len() == RENDER_WIDTH {
                elements.push("...".to_string());
                return format!("[{}]", elements.join(", "));
            }
            let Some(head) = (reader.list_head)(cursor) else {
                elements.push("?".to_string());
                break;
            };
            elements.push(render(reader, head, depth - 1));
            let Some(tail) = (reader.list_tail)(cursor) else {
                elements.push("?".to_string());
                break;
            };
            cursor = tail;
        }
        match list_shape_of(cursor) {
            Some(_) => format!("[{}]", elements.join(", ")),
            // An improper tail is not an element, and saying so is the point.
            None => format!("[{} | {}]", elements.join(", "), render(reader, cursor, depth - 1)),
        }
    }

    fn render_tuple(reader: &RuntimeValueReader<'_>, value: RuntimeAnyValue, arity: usize, depth: usize) -> String {
        if depth == 0 {
            return "{...}".to_string();
        }
        let fields = (0..arity.min(RENDER_WIDTH))
            .map(|index| match (reader.fields)(value, index) {
                Some(field) => render(reader, field, depth - 1),
                None => "?".to_string(),
            })
            .chain((arity > RENDER_WIDTH).then(|| "...".to_string()))
            .collect::<Vec<_>>();
        format!("{{{}}}", fields.join(", "))
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
            RuntimeTestAxis::Callables => predicate.callables = CallableShapes::any(),
            RuntimeTestAxis::Resources => predicate.resources = true,
        }
    }

    /// A test that admits exactly the floats, for use as a capture question.
    fn floats() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.floats = FiniteSet::any();
        predicate
    }

    fn construction(target: u32, captures: Vec<RuntimeTypePredicate>) -> CallableShape {
        CallableShape {
            target: ClosureTarget(target),
            captures,
        }
    }

    /// ADMISSION IS CONTAINMENT, NEVER OVERLAP (fz-kdt.167).
    ///
    /// A construction's capture types are the annotation its mint stamped, and
    /// the LAYOUT the capture was stored in is the construction's, not the
    /// value's. So a wrapper closed over `int | float` stores a boxed word,
    /// and a body compiled for an `int` capture reads a raw int out of that
    /// slot -- which is why the union construction must be refused by the
    /// narrow test even though the two overlap. Only a test naming a capture
    /// question the construction's own is INSIDE may admit it.
    #[test]
    fn a_union_capture_construction_is_admitted_only_by_a_test_that_contains_it() {
        let mut int_or_float = ints();
        int_or_float.floats = FiniteSet::any();
        let minted = construction(66, vec![int_or_float.clone()]);

        let narrow = CallableShapes::exact(vec![construction(66, vec![ints()])]);
        assert!(
            narrow.targets().values.contains(&ClosureTarget(66)),
            "the two do name one function, so nothing but the captures can separate them",
        );
        assert!(
            !narrow.admits(&minted),
            "a construction over `int | float` stored a boxed capture; a body whose capture \
             lane is a raw int must not receive it",
        );

        let equal = CallableShapes::exact(vec![construction(66, vec![int_or_float.clone()])]);
        assert!(equal.admits(&minted), "the construction's own shape admits it");

        let mut wider = int_or_float;
        wider.atoms = FiniteSet::any();
        let wide = CallableShapes::exact(vec![construction(66, vec![wider])]);
        assert!(wide.admits(&minted), "and so does any shape that contains it");

        let other_function = CallableShapes::exact(vec![construction(68, vec![ints()])]);
        assert!(
            !other_function.admits(&minted),
            "a different function is a different word"
        );
    }

    /// The target-only reading is what a clause pinning several literals at
    /// once degrades to, and it admits every capture layout of its targets --
    /// which is what this layer asked before fz-kdt.127.
    #[test]
    fn a_target_only_axis_admits_every_capture_layout_of_its_targets() {
        let coarse = CallableShapes::target_only(FiniteSet::lit(ClosureTarget(66)));
        assert!(!coarse.is_exact(), "several literals at once are not one shape");
        assert!(coarse.admits(&construction(66, vec![ints()])));
        assert!(coarse.admits(&construction(66, vec![floats()])));
        assert!(!coarse.admits(&construction(68, vec![ints()])));
    }

    /// The callable axis is PER POSITION: it separates exactly as far as its
    /// capture questions do, and erases exactly where they erase.
    ///
    /// Two constructions of one function over disjoint capture types are a
    /// real separation -- a seat may put either first. Two over capture types
    /// that meet only through what a capture's own test cannot see past are
    /// not, and the seat owes them the surface-coverage check (fz-kdt.131).
    #[test]
    fn the_callable_axis_erases_exactly_where_its_captures_do() {
        let over_int = CallableShapes::exact(vec![construction(66, vec![ints()])]);
        let over_float = CallableShapes::exact(vec![construction(66, vec![floats()])]);
        let mut both = RuntimeTypePredicate::none();
        both.callables = over_int;
        let mut other = RuntimeTypePredicate::none();
        other.callables = over_float;
        assert!(
            !both.overlaps(&other),
            "int and float captures are disjoint, so no construction passes both tests",
        );
        assert!(
            !both.overlaps_on_an_erasing_axis(&other),
            "and a disjoint capture position is a separation the seat may rely on",
        );

        let int_list = cons_of(vec![ints()]);
        let int_or_atom_list = cons_of(vec![{
            let mut heads = ints();
            heads.atoms = FiniteSet::any();
            heads
        }]);
        let mut over_int_list = RuntimeTypePredicate::none();
        over_int_list.callables = CallableShapes::exact(vec![construction(66, vec![int_list])]);
        let mut over_wider_list = RuntimeTypePredicate::none();
        over_wider_list.callables = CallableShapes::exact(vec![construction(66, vec![int_or_atom_list])]);
        assert!(
            over_int_list.overlaps(&over_wider_list),
            "`[int]` and `[int | :ok]` admit the same cons cells at the head",
        );
        assert!(
            over_int_list.overlaps_on_an_erasing_axis(&over_wider_list),
            "and they disagree only about a tail no test reads, so the callable axis must \
             report the erasure through the capture rather than claim a separation",
        );

        let coarse = {
            let mut predicate = RuntimeTypePredicate::none();
            predicate.callables = CallableShapes::target_only(FiniteSet::lit(ClosureTarget(66)));
            predicate
        };
        assert!(
            coarse.overlaps_on_an_erasing_axis(&both),
            "and an axis that could not be shaped claims nothing at all",
        );
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

    /// fz-kdt.138 in lattice terms: a LIST position is decided like any other,
    /// so it separates exactly as far as the list axis itself does -- by shape,
    /// and by disjoint heads -- and no further.
    ///
    /// This is `dispatch_nested_list_position_separates`' claim one layer down.
    /// Every pair here used to be ONE question, because the position was
    /// excluded from the lattice and from all three lowerings alike.
    #[test]
    fn a_nested_list_position_is_a_question_like_any_other() {
        let mut empty_list = RuntimeTypePredicate::none();
        empty_list.lists = ListShapes::exact(FiniteSet::lit(ListShape::Empty), Vec::new());
        let initial = tuple(vec![vec![empty_list, ints()]]);
        let grown = tuple(vec![vec![cons_of(vec![ints()]), ints()]]);
        assert!(
            !initial.overlaps(&grown),
            "the shapes disagree about the position's SHAPE, so no tuple passes both tests",
        );
        assert!(
            !initial.overlaps_on_an_erasing_axis(&grown),
            "a position the lowerings decide is separation a seat may claim",
        );

        let of_atoms = tuple(vec![vec![cons_of(vec![atom("ok")]), ints()]]);
        assert!(
            !grown.overlaps(&of_atoms),
            "and disjoint HEADS separate the position too, one nesting level in",
        );

        let mut int_or_atom = ints();
        int_or_atom.atoms = FiniteSet::lit("ok".to_string());
        let of_either = tuple(vec![vec![cons_of(vec![int_or_atom]), ints()]]);
        assert!(
            grown.overlaps(&of_either) && grown.overlaps_on_an_erasing_axis(&of_either),
            "the one-sided-filter law holds inside a position: heads that OVERLAP still \
             erase, because the tail behind them is what neither test reads",
        );
    }

    /// Correlation survives the projection: a two-clause union is two shapes,
    /// and the cross terms neither clause names are not admitted.
    #[test]
    fn two_tuple_clauses_stay_two_shapes() {
        let mixed = tuple(vec![vec![atom("cont"), ints()], vec![atom("halt"), atom("ok")]]);
        let list_payload = tuple(vec![vec![atom("cont"), list_of_anything()]]);
        assert!(
            !mixed.overlaps(&list_payload),
            "a list position is a question, so {{:cont, [..]}} and {{:cont, int}} are two of them",
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

/// What one TEST says about one VALUE, over a fake reader, through the
/// production tripwire (fz-kdt.144).
///
/// The lattice tests above ask what two tests say about EACH OTHER. These ask
/// the other half of the one-sided-filter law: a head is exact on rejection and
/// erasing on acceptance, so the tail is what only [`PositionScope::Full`]
/// reads, and the gap between the two readings is what
/// [`surface_membership::observe`] must report -- no more and no less.
///
/// The reader is exactly the shape `select_dispatch_match` builds, and the
/// predicate is asked through `matches_runtime_type_predicate` and `observe`
/// rather than through the walk directly, so a case that passes here is a case
/// the interpreter answers the same way.
#[cfg(test)]
mod value_membership_tests {
    use super::surface_membership::SurfaceMembershipCensus;
    use super::*;
    use fz_runtime::any_value::AnyValueRef;

    /// A fake heap: cons cells and tuples addressed by synthetic words the
    /// reader closures resolve, so no value is ever dereferenced except a
    /// tuple's schema id, which the runtime's own `struct_schema_id` reads off
    /// the pointer.
    struct FakeHeap {
        cells: Vec<(RuntimeAnyValue, RuntimeAnyValue)>,
        tuples: Vec<(Box<u32>, Vec<RuntimeAnyValue>)>,
        module: Module,
    }

    impl FakeHeap {
        fn new(atoms: &[&str]) -> Self {
            let module = Module {
                atom_names: atoms.iter().map(|name| (*name).to_string()).collect(),
                ..Module::default()
            };
            Self {
                cells: Vec::new(),
                tuples: Vec::new(),
                module,
            }
        }

        fn atom(&self, name: &str) -> RuntimeAnyValue {
            let id = self
                .module
                .atom_names
                .iter()
                .position(|candidate| candidate == name)
                .expect("the fake heap must intern every atom a test names");
            RuntimeAnyValue::Atom(id as u32)
        }

        /// Cell `index` lives at the synthetic word `(index + 1) * 8`, which is
        /// never dereferenced and is never null, so it is never the empty list.
        fn cons(&mut self, head: RuntimeAnyValue, tail: RuntimeAnyValue) -> RuntimeAnyValue {
            self.cells.push((head, tail));
            Self::cell_ref(self.cells.len() - 1)
        }

        fn cell_ref(index: usize) -> RuntimeAnyValue {
            let addr = ((index + 1) * 8) as *const u8;
            RuntimeAnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::LIST, addr).expect("a list ref"))
        }

        /// A proper list, built right to left.
        fn list(&mut self, elements: &[RuntimeAnyValue]) -> RuntimeAnyValue {
            let mut list = RuntimeAnyValue::EmptyList;
            for element in elements.iter().rev() {
                list = self.cons(*element, list);
            }
            list
        }

        /// A cons cell whose tail is itself: a spine no heap the runtime builds
        /// can hold, and the only way to ask whether the walk's termination is a
        /// fact of the code.
        fn cycle(&mut self, head: RuntimeAnyValue) -> RuntimeAnyValue {
            let cell = self.cons(head, RuntimeAnyValue::EmptyList);
            let index = self.cells.len() - 1;
            self.cells[index].1 = cell;
            cell
        }

        /// Its schema id is a real `u32` behind a `Box`, because
        /// `struct_schema_id` reads it off the value itself.
        fn tuple(&mut self, schema: u32, fields: Vec<RuntimeAnyValue>) -> RuntimeAnyValue {
            let boxed = Box::new(schema);
            let addr = (&*boxed) as *const u32 as *const u8;
            self.tuples.push((boxed, fields));
            RuntimeAnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::STRUCT, addr).expect("a struct ref"))
        }

        fn cell_of(&self, value: RuntimeAnyValue) -> Option<&(RuntimeAnyValue, RuntimeAnyValue)> {
            let RuntimeAnyValue::HeapRef(value_ref) = value else {
                return None;
            };
            if value_ref.tag() != ValueKind::LIST || value_ref.is_empty_list() {
                return None;
            }
            let index = (value_ref.storage_addr() as usize) / 8;
            self.cells.get(index - 1)
        }

        fn fields_of(&self, value: RuntimeAnyValue) -> Option<&Vec<RuntimeAnyValue>> {
            let addr = value.heap_addr()?;
            self.tuples
                .iter()
                .find(|(schema, _)| (&**schema) as *const u32 as *mut u8 == addr)
                .map(|(_, fields)| fields)
        }
    }

    /// How many escapes the production tripwire reports for one value, asked
    /// the way the interpreter asks it: answer the test, and observe what it
    /// admitted. `arities` registers the schema id of each tuple arity the test
    /// names, which is the runtime's own numbering the interpreter hands in.
    fn escapes(
        heap: &FakeHeap,
        predicate: &RuntimeTypePredicate,
        value: RuntimeAnyValue,
        arities: &[(usize, u32)],
    ) -> usize {
        let tuple_schema_ids = arities.iter().copied().collect::<HashMap<_, _>>();
        let named_schema_ids = HashMap::new();
        let callables = |_: u64| None;
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |value: RuntimeAnyValue| heap.cell_of(value).map(|(head, _)| *head);
        let list_tail = |value: RuntimeAnyValue| heap.cell_of(value).map(|(_, tail)| *tail);
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let census = SurfaceMembershipCensus::install();
        if matches_runtime_type_predicate(predicate, &reader, value) {
            surface_membership::observe(predicate, &reader, value);
        }
        census.escapes()
    }

    fn list_test(shapes: FiniteSet<ListShape>, heads: Vec<RuntimeTypePredicate>) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.lists = ListShapes::exact(shapes, heads);
        predicate
    }

    fn any_shape() -> FiniteSet<ListShape> {
        FiniteSet::finite([ListShape::Empty, ListShape::NonEmpty])
    }

    fn ints() -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.ints = FiniteSet::any();
        predicate
    }

    fn atom_test(name: &str) -> RuntimeTypePredicate {
        let mut predicate = RuntimeTypePredicate::none();
        predicate.atoms = FiniteSet::lit(name.to_string());
        predicate
    }

    /// The two readings agree on a list the clause actually names: every
    /// element answers the one element question, so there is nothing to report.
    #[test]
    fn a_list_whose_every_element_answers_the_head_question_is_inside_the_surface() {
        let mut heap = FakeHeap::new(&["ok"]);
        let value = heap.list(&[RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2)]);
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), value, &[]), 0);
    }

    /// THE ACCEPTANCE RESIDUE, which is the whole point of the instrument: the
    /// head admits, the TAIL does not, and only the `Full` reading can say so.
    #[test]
    fn a_list_whose_tail_leaves_the_head_question_is_outside_the_surface() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), value, &[]), 1);
    }

    /// PER-CLAUSE HOMOGENEITY, not a union of heads. `[int] | [:ok]` names two
    /// list types and `[1, :ok]` is neither, so reading the clauses' heads as
    /// one set would admit it and lose the correlation the clauses keep.
    #[test]
    fn a_mixed_list_belongs_to_no_clause_of_a_union_of_homogeneous_list_clauses() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let two_clauses = list_test(any_shape(), vec![ints(), atom_test("ok")]);
        assert_eq!(escapes(&heap, &two_clauses, value, &[]), 1);
    }

    /// The same list under ONE clause whose ELEMENT type is that union is
    /// inside, because a clause is one homogeneous element type and this one
    /// names both. The false escape the per-clause reading must not produce.
    #[test]
    fn a_mixed_list_belongs_to_one_clause_whose_element_type_is_that_union() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let mut element = ints();
        element.atoms = FiniteSet::lit("ok".to_string());
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![element]), value, &[]), 0);
    }

    /// The walk composes: an element that is itself a list is asked under
    /// `Full` too, so `[[1], [:ok]]` leaves `[[int]]` one level in.
    #[test]
    fn an_element_that_is_itself_a_list_is_asked_the_same_way() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let inner_ints = heap.list(&[RuntimeAnyValue::Int(1)]);
        let inner_atoms = heap.list(&[ok]);
        let value = heap.list(&[inner_ints, inner_atoms]);
        let list_of_int_lists = list_test(any_shape(), vec![list_test(any_shape(), vec![ints()])]);
        assert_eq!(escapes(&heap, &list_of_int_lists, value, &[]), 1);
    }

    /// `[]` carries nothing for a body to misread, which is the `[]` exception
    /// stated on the value side: no reading can refuse it.
    #[test]
    fn the_empty_list_carries_no_element_to_refuse() {
        let heap = FakeHeap::new(&["ok"]);
        assert_eq!(
            escapes(
                &heap,
                &list_test(any_shape(), vec![ints()]),
                RuntimeAnyValue::EmptyList,
                &[]
            ),
            0
        );
    }

    /// An axis that asks no head has no `Full` content, so it reports nothing:
    /// honest inertness for exactly the clauses fz-kdt.146's degrade rule could
    /// not shape, rather than a guess about elements nobody projected.
    #[test]
    fn a_list_axis_that_asks_no_head_reports_nothing_rather_than_guessing() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let mut shape_only = RuntimeTypePredicate::none();
        shape_only.lists = ListShapes::shape_only(any_shape());
        assert_eq!(escapes(&heap, &shape_only, value, &[]), 0);
    }

    /// A list held in a TUPLE position is walked through that position, because
    /// the scope is threaded through `matches_tuple_shape` already.
    #[test]
    fn a_list_held_in_a_tuple_position_is_walked_through_that_position() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let payload = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let tag = heap.atom("ok");
        let value = heap.tuple(7, vec![tag, payload]);
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(vec![vec![atom_test("ok"), list_test(any_shape(), vec![ints()])]]);
        assert_eq!(escapes(&heap, &predicate, value, &[(2, 7)]), 1);
    }

    /// An element question that admits everything refuses nothing, however
    /// heterogeneous the spine: the surface named all of it.
    #[test]
    fn an_element_question_that_admits_everything_refuses_nothing() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let value = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        let element = RuntimeTypePredicate::any();
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![element]), value, &[]), 0);
    }

    /// A COFINITE head set is "every atom but these", and the walk reads it the
    /// way the head load does -- admitting what it does not exclude, refusing
    /// what it does.
    #[test]
    fn a_cofinite_element_question_refuses_exactly_what_it_excludes() {
        let mut heap = FakeHeap::new(&["ok", "err", "other"]);
        let other = heap.atom("other");
        let err = heap.atom("err");
        let mut element = RuntimeTypePredicate::none();
        element.atoms = FiniteSet {
            values: ["ok".to_string()].into_iter().collect(),
            cofinite: true,
        };
        let admitted = heap.list(&[other, err]);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![element.clone()]), admitted, &[]),
            0,
        );
        let ok = heap.atom("ok");
        let excluded = heap.list(&[other, ok]);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![element]), excluded, &[]),
            1,
            "the excluded atom is an element outside the clause, wherever in the spine it sits",
        );
    }

    /// A content-blind element axis (maps, binaries) is decided by kind alone,
    /// so it reads the same under both scopes and a list of them never reports.
    #[test]
    fn a_content_blind_element_axis_reads_the_same_under_both_scopes() {
        let mut heap = FakeHeap::new(&["ok"]);
        let map = RuntimeAnyValue::HeapRef(
            AnyValueRef::from_heap_object(ValueKind::MAP, 0x1000 as *const u8).expect("a map ref"),
        );
        let value = heap.list(&[map, map]);
        let mut element = RuntimeTypePredicate::none();
        element.maps = true;
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![element]), value, &[]), 0);
    }

    /// An IMPROPER list's tail is not an element: the walk stops there rather
    /// than judging a value the list type never described.
    #[test]
    fn an_improper_tail_is_not_an_element_and_ends_the_walk() {
        let mut heap = FakeHeap::new(&["ok"]);
        let improper = heap.cons(RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2));
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), improper, &[]), 0);
        let ok = heap.atom("ok");
        let atom_tailed = heap.cons(RuntimeAnyValue::Int(1), ok);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![ints()]), atom_tailed, &[]),
            0,
            "an atom tail is not an element either",
        );
    }

    /// What the representation declines to show, the instrument does not judge:
    /// a cons cell the reader cannot open ends the walk silently, exactly as an
    /// unreadable head ends the `Lowered` reading.
    #[test]
    fn a_head_the_representation_declines_to_show_is_not_judged() {
        let heap = FakeHeap::new(&["ok"]);
        let orphan = RuntimeAnyValue::HeapRef(
            AnyValueRef::from_heap_object(ValueKind::LIST, 0x9000 as *const u8).expect("a list ref"),
        );
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), orphan, &[]), 0);
    }

    /// A CALLABLE element is decided by the construction word the backend
    /// minted it with, which no scope changes: a closure the question names is
    /// never a false escape, and one it does not name is refused by BOTH
    /// readings, so it is never an escape either.
    #[test]
    fn a_callable_element_is_decided_by_its_construction_under_both_scopes() {
        let mut heap = FakeHeap::new(&["ok"]);
        // A real closure object: word 0 is the header, word 1 the code word.
        let object: Box<[u64; 2]> = Box::new([0, 66]);
        let addr = (&*object) as *const [u64; 2] as *const u8;
        let closure =
            RuntimeAnyValue::HeapRef(AnyValueRef::from_heap_object(ValueKind::CLOSURE, addr).expect("a closure ref"));
        let value = heap.list(&[closure, closure]);

        let shape = CallableShape {
            target: ClosureTarget(66),
            captures: vec![list_test(any_shape(), vec![ints()])],
        };
        let mut element = RuntimeTypePredicate::none();
        element.callables = CallableShapes::exact(vec![shape.clone()]);
        let tuple_schema_ids = HashMap::new();
        let named_schema_ids = HashMap::new();
        let callables = move |code: u64| (code == 66).then(|| shape.clone());
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |value: RuntimeAnyValue| heap.cell_of(value).map(|(head, _)| *head);
        let list_tail = |value: RuntimeAnyValue| heap.cell_of(value).map(|(_, tail)| *tail);
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let predicate = list_test(any_shape(), vec![element]);
        let census = SurfaceMembershipCensus::install();
        assert!(
            matches_runtime_type_predicate(&predicate, &reader, value),
            "the construction these closures carry is the one the element question names",
        );
        surface_membership::observe(&predicate, &reader, value);
        assert_eq!(
            census.escapes(),
            0,
            "a capture question is answered off the construction word, not off the value's contents, \
             so it reads the same under both scopes",
        );
    }

    /// Termination is a fact of the walk, not of the heap it reads: a spine
    /// that never ends is abandoned at [`ELEMENT_WALK_LIMIT`] and reported as
    /// inside, because a report that can hang the program it instruments is
    /// worse than a report that stops.
    #[test]
    fn a_spine_that_never_ends_is_abandoned_at_the_walk_limit() {
        let mut heap = FakeHeap::new(&["ok"]);
        let value = heap.cycle(RuntimeAnyValue::Int(1));
        assert_eq!(escapes(&heap, &list_test(any_shape(), vec![ints()]), value, &[]), 0);
        let ok = heap.atom("ok");
        let atoms_forever = heap.cycle(ok);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![ints()]), atoms_forever, &[]),
            0,
            "and a cycle the question refuses at its first element is refused, not walked",
        );
    }

    /// A `[]`-only clause beside a cons clause puts no head question of its
    /// own, so the cons clause's is the only element question and the empty
    /// list is still inside.
    #[test]
    fn an_empty_list_clause_beside_a_cons_clause_asks_only_the_cons_clauses_question() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let test = list_test(any_shape(), vec![ints()]);
        assert_eq!(escapes(&heap, &test, RuntimeAnyValue::EmptyList, &[]), 0);
        let ints_only = heap.list(&[RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2)]);
        assert_eq!(escapes(&heap, &test, ints_only, &[]), 0);
        let mixed = heap.list(&[RuntimeAnyValue::Int(1), ok]);
        assert_eq!(escapes(&heap, &test, mixed, &[]), 1);
    }

    /// Three levels: a tuple holding a list of tuples whose own position is a
    /// list. The refusal is four loads deep and the walk must still find it.
    #[test]
    fn a_tuple_inside_a_list_inside_a_tuple_is_walked_to_the_bottom() {
        let mut heap = FakeHeap::new(&["ok", "err"]);
        let ok = heap.atom("ok");
        let err = heap.atom("err");
        let good_inner = heap.list(&[RuntimeAnyValue::Int(2)]);
        let bad_inner = heap.list(&[err]);
        let good = heap.tuple(7, vec![RuntimeAnyValue::Int(1), good_inner]);
        let bad = heap.tuple(7, vec![RuntimeAnyValue::Int(1), bad_inner]);
        let spine = heap.list(&[good, bad]);
        let outer = heap.tuple(7, vec![ok, spine]);

        let mut inner_tuple = RuntimeTypePredicate::none();
        inner_tuple.tuples = TupleShapes::exact(vec![vec![ints(), list_test(any_shape(), vec![ints()])]]);
        let mut predicate = RuntimeTypePredicate::none();
        predicate.tuples = TupleShapes::exact(vec![vec![atom_test("ok"), list_test(any_shape(), vec![inner_tuple])]]);
        assert_eq!(escapes(&heap, &predicate, outer, &[(2, 7)]), 1);
    }

    /// A clause that would admit a LATER element does not rescue an earlier
    /// one: per-clause homogeneity is order-blind.
    #[test]
    fn a_clause_that_admits_a_later_element_does_not_rescue_an_earlier_one() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let two_clauses = list_test(any_shape(), vec![ints(), atom_test("ok")]);
        let atom_first = heap.list(&[ok, RuntimeAnyValue::Int(1)]);
        assert_eq!(escapes(&heap, &two_clauses, atom_first, &[]), 1);
        let all_atoms = heap.list(&[ok, ok]);
        assert_eq!(escapes(&heap, &two_clauses, all_atoms, &[]), 0);
    }

    /// A callable element minted from a construction the clause does not name
    /// is outside it, wherever in the spine it sits.
    #[test]
    fn a_callable_element_from_a_construction_the_clause_never_named_is_outside_it() {
        let mut heap = FakeHeap::new(&["ok"]);
        let named: Box<[u64; 2]> = Box::new([0, 66]);
        let other: Box<[u64; 2]> = Box::new([0, 67]);
        let closure = |object: &[u64; 2]| {
            RuntimeAnyValue::HeapRef(
                AnyValueRef::from_heap_object(ValueKind::CLOSURE, object as *const [u64; 2] as *const u8)
                    .expect("a closure ref"),
            )
        };
        let value = heap.list(&[closure(&named), closure(&other)]);

        let shape = CallableShape {
            target: ClosureTarget(66),
            captures: Vec::new(),
        };
        let mut element = RuntimeTypePredicate::none();
        element.callables = CallableShapes::exact(vec![shape.clone()]);
        let predicate = list_test(any_shape(), vec![element]);

        let tuple_schema_ids = HashMap::new();
        let named_schema_ids = HashMap::new();
        let callables = move |code: u64| {
            (code == 66).then(|| shape.clone()).or_else(|| {
                (code == 67).then(|| CallableShape {
                    target: ClosureTarget(67),
                    captures: Vec::new(),
                })
            })
        };
        let fields =
            |value: RuntimeAnyValue, index: usize| heap.fields_of(value).and_then(|fields| fields.get(index)).copied();
        let list_head = |value: RuntimeAnyValue| heap.cell_of(value).map(|(head, _)| *head);
        let list_tail = |value: RuntimeAnyValue| heap.cell_of(value).map(|(_, tail)| *tail);
        let reader = RuntimeValueReader {
            module: &heap.module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let census = SurfaceMembershipCensus::install();
        assert!(matches_runtime_type_predicate(&predicate, &reader, value));
        surface_membership::observe(&predicate, &reader, value);
        assert_eq!(census.escapes(), 1);
    }

    /// An improper tail DEEP in the spine still ends the walk, and a refusal
    /// before it is still found.
    #[test]
    fn an_improper_tail_deeper_in_the_spine_ends_the_walk_where_it_sits() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let test = list_test(any_shape(), vec![ints()]);
        let improper = heap.cons(RuntimeAnyValue::Int(1), RuntimeAnyValue::Int(2));
        let deep = heap.cons(RuntimeAnyValue::Int(0), improper);
        assert_eq!(escapes(&heap, &test, deep, &[]), 0);
        let refused_then_improper = {
            let tail = heap.cons(ok, RuntimeAnyValue::Int(2));
            heap.cons(RuntimeAnyValue::Int(0), tail)
        };
        assert_eq!(escapes(&heap, &test, refused_then_improper, &[]), 1);
    }

    /// A nested clause that admits only NON-EMPTY lists refuses an empty
    /// element, which no head load can see.
    #[test]
    fn an_empty_inner_list_leaves_an_element_clause_that_admits_only_cons_cells() {
        let mut heap = FakeHeap::new(&["ok"]);
        let inner = heap.list(&[RuntimeAnyValue::Int(1)]);
        let value = heap.list(&[inner, RuntimeAnyValue::EmptyList]);
        let non_empty_ints = list_test(FiniteSet::lit(ListShape::NonEmpty), vec![ints()]);
        assert_eq!(
            escapes(&heap, &list_test(any_shape(), vec![non_empty_ints]), value, &[]),
            1
        );
    }

    /// THE WALK LIMIT IS A FALSE NEGATIVE, and this pins where it starts: a
    /// refusal at the last index the walk reaches is reported, and the same
    /// refusal one element further out is not.
    #[test]
    fn the_walk_limit_is_where_a_refusal_stops_being_reported() {
        let mut heap = FakeHeap::new(&["ok"]);
        let ok = heap.atom("ok");
        let test = list_test(any_shape(), vec![ints()]);

        let mut elements = vec![RuntimeAnyValue::Int(1); ELEMENT_WALK_LIMIT - 1];
        elements.push(ok);
        let at_the_last_judged_index = heap.list(&elements);
        assert_eq!(escapes(&heap, &test, at_the_last_judged_index, &[]), 1);

        let mut elements = vec![RuntimeAnyValue::Int(1); ELEMENT_WALK_LIMIT];
        elements.push(ok);
        let one_past_it = heap.list(&elements);
        assert_eq!(
            escapes(&heap, &test, one_past_it, &[]),
            0,
            "past the limit the walk reports nothing, which is a MISSED escape, not a clean list",
        );
    }
}
