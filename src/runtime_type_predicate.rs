//! First-class runtime-observable membership predicates.
//!
//! Semantic types remain richer than what the runtime can inspect directly.
//! Backends and the interpreter therefore answer runtime-membership questions
//! by projecting semantic types into this explicit predicate layer.

use crate::finite_set::FiniteSet;
use crate::fz_ir::Module;
use crate::modules::identity::ModuleName;
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
/// - `ir_interp::dispatch_exec::TypeTest::whole_value_matches` through
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
                kind if kind.is_binary_repr() => &[Self::Binaries],
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
    pub(crate) named_structs: FiniteSet<ModuleName>,
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

    /// The test every value passes. It is what a list clause that admits every
    /// element asks its head.
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

    pub(crate) fn named_struct(name: ModuleName) -> Self {
        let mut predicate = Self::none();
        predicate.named_structs = FiniteSet::lit(name);
        predicate
    }

    pub(crate) fn map_kind() -> Self {
        let mut predicate = Self::none();
        predicate.maps = true;
        predicate
    }

    /// Which arities of UNNAMED struct the other-structs axis admits.
    ///
    /// The axis is the remainder the tuple axis leaves: every unnamed struct
    /// whose arity the tuple axis does not NAME. So the answer is the
    /// complement of the arities the tuple axis lists -- cofinite, because an
    /// arity nobody mentioned is one nobody excluded -- and it is empty for a
    /// test that does not carry the axis at all.
    ///
    /// Naming is not admission: a cofinite tuple axis EXCLUDES the arities it
    /// lists, and those are exactly the ones this axis then declines too, so
    /// such a test refuses them on both axes. That is what the axis has always
    /// meant; stating it once keeps the interpreter's matcher, the whole-value
    /// reading in [`Self::tuple_positions`] and the native emitter from each
    /// deciding for themselves which arities are spoken for.
    pub(crate) fn other_struct_arities(&self) -> FiniteSet<usize> {
        if self.allow_other_structs {
            FiniteSet::cofinite(self.tuples.arities().values.iter().copied())
        } else {
            FiniteSet::none()
        }
    }

    /// What this test asks of a value that is an unnamed tuple of `arity`.
    ///
    /// The whole-value answer, not one axis of it: a struct value is offered to
    /// three axes at once, and the other-structs axis admits every struct whose
    /// arity the tuple axis does not name, so a test carrying it cannot refuse
    /// such a tuple on its shape. What is left is the tuple axis' own reading:
    /// an inexact axis is the arity-only one and asks nothing further, and an
    /// exact one names the shapes of that arity.
    ///
    /// The named-structs axis takes no part: it admits only a schema the module
    /// registered under a name, which an unnamed tuple never carries.
    ///
    /// Every door asks through here -- the boxed matcher, the boxed emitter,
    /// and the two lowerings that hold the fields rather than a value -- so
    /// they cannot decompose a tuple test differently.
    pub(crate) fn tuple_positions(&self, arity: usize) -> TuplePositions<'_> {
        if self.other_struct_arities().contains(&arity) {
            return TuplePositions::Always;
        }
        if !self.tuples.arities().contains(&arity) {
            return TuplePositions::Never;
        }
        if !self.tuples.is_exact() {
            return TuplePositions::Always;
        }
        let shapes = self.tuples.of_arity(arity).collect::<Vec<_>>();
        debug_assert!(
            !shapes.is_empty(),
            "an exact axis derives its arities from its shapes' lengths, so an admitted arity has a shape"
        );
        TuplePositions::AnyOf(shapes)
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

    /// Whether answering this test needs to know which schemas the module
    /// NAMED.
    ///
    /// Three readings consult that table, and a test that asks none of them at
    /// any depth can be answered without building it at all. The named-structs
    /// axis asks it outright. Either struct axis asks it whenever its arity set
    /// is COFINITE, because "every arity but these" means "every UNNAMED struct
    /// but these", and only the module's table says which structs were named --
    /// and the other-structs axis' set is cofinite exactly when the test
    /// carries that axis.
    ///
    /// The same walk as [`Self::tuple_arities_at_every_depth`], for the same
    /// reason: a nested position is answered through the same reader, so a
    /// question asked at depth needs what the whole test needs.
    pub(crate) fn reads_named_schemas(&self) -> bool {
        self.asks_a_named_schema_question() || self.sub_predicates().any(Self::reads_named_schemas)
    }

    fn asks_a_named_schema_question(&self) -> bool {
        !self.named_structs.is_none() || self.tuples.arities().cofinite || self.allow_other_structs
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

/// What a test asks of a value already known to be an unnamed tuple of one
/// arity.
///
/// A door holding a boxed value reads the arity off a schema id and then asks
/// each field its own question. A door holding the fields themselves has no
/// schema to read, so it asks this instead: the arity is a fact it already
/// knows, and what is left is either settled or a set of shapes to try.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TuplePositions<'a> {
    /// No tuple of that arity is admitted.
    Never,
    /// Every tuple of that arity is admitted, whatever its fields hold.
    Always,
    /// Admitted by any one of these shapes, each a question per position.
    AnyOf(Vec<&'a [RuntimeTypePredicate]>),
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
/// clause of the descriptor it was projected from. An interned clause has one
/// literal identity, so every non-top callable axis is exact. The target set
/// is derived from the shapes when the axis is exact, never stated twice, so
/// the two readings cannot drift apart.
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
        Self {
            targets: FiniteSet::any(),
            shapes: Vec::new(),
            exact: false,
        }
    }

    /// One shape per clause, and the targets they name.
    pub(crate) fn exact(shapes: Vec<CallableShape>) -> Self {
        Self {
            targets: FiniteSet::finite(shapes.iter().map(|shape| shape.target)),
            shapes,
            exact: true,
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
    pub(crate) named_schema_ids: &'a HashMap<ModuleName, u32>,
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

    /// Whether `schema` is an UNNAMED struct whose arity `arities` admits.
    ///
    /// The one schema-space reading of an arity set. A tuple is a struct the
    /// module never named, so a cofinite set is "not a named schema, and not
    /// one of the excluded arities' schemas" while a finite one is exactly the
    /// schemas of the arities it lists. An arity the runtime registered no
    /// schema for names no value and drops out of either reading.
    ///
    /// Both struct axes that ask about arities ask through here, so the tuple
    /// axis and the other-structs axis cannot disagree about which schema a
    /// set of arities covers. The native emitter's `emit_arity_set_membership`
    /// renders the same three cases into Cranelift.
    fn unnamed_struct_of_arity(&self, schema: u32, arities: &FiniteSet<usize>) -> bool {
        let of_arities = arities
            .values
            .iter()
            .filter_map(|arity| self.tuple_schema_ids.get(arity).copied())
            .collect::<BTreeSet<_>>();
        if !arities.cofinite {
            return of_arities.contains(&schema);
        }
        !self.known_named_schemas().contains(&schema) && !of_arities.contains(&schema)
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
        RuntimeTestAxis::Binaries => predicate.binaries && is_binary_value(value),
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

/// A binary in either of its representations. See `ValueKind::BINARY_REPRS`.
fn is_binary_value(value: RuntimeAnyValue) -> bool {
    matches!(value, RuntimeAnyValue::HeapRef(value_ref) if value_ref.tag().is_binary_repr())
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
/// The arity half is the schema-id membership question
/// [`RuntimeValueReader::unnamed_struct_of_arity`] answers; the shape half asks
/// each position its own question, and is skipped where the axis is inexact,
/// which is the arity-only reading this layer had before fz-kdt.119.
fn matches_tuple_axis(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
    scope: PositionScope,
) -> bool {
    let Some(actual) = struct_schema_of(value) else {
        return false;
    };
    reader.unnamed_struct_of_arity(actual, predicate.tuples.arities())
        && matches_tuple_shape(predicate, reader, value, actual, scope)
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
    let Some(arity) = reader.tuple_arity_of(schema) else {
        // A tuple whose arity this test never named: the arity half above
        // already decided it, and there is no shape to ask.
        return true;
    };
    let shapes = match predicate.tuple_positions(arity) {
        TuplePositions::Never => return false,
        TuplePositions::Always => return true,
        TuplePositions::AnyOf(shapes) => shapes,
    };
    shapes.into_iter().any(|shape| {
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

/// "Is this an unnamed struct the tuple axis does not speak for?"
///
/// Which arities those are is [`RuntimeTypePredicate::other_struct_arities`]'s
/// to say, and turning arities into schema ids is the same reading the tuple
/// axis uses, so the two axes divide the unnamed structs between them without
/// gap or overlap.
fn matches_other_struct_axis(
    predicate: &RuntimeTypePredicate,
    reader: &RuntimeValueReader<'_>,
    value: RuntimeAnyValue,
) -> bool {
    let Some(actual) = struct_schema_of(value) else {
        return false;
    };
    reader.unnamed_struct_of_arity(actual, &predicate.other_struct_arities())
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

/// What one TEST says about one VALUE, over a fake reader, through the
/// production tripwire (fz-kdt.144).
///
/// The lattice tests above ask what two tests say about EACH OTHER. These ask
/// the other half of the one-sided-filter law: a head is exact on rejection and
/// erasing on acceptance, so the tail is what only [`PositionScope::Full`]
/// reads, and the gap between the two readings is what
/// [`surface_membership::observe`] must report -- no more and no less.
///
/// The reader is exactly the shape `TypeTest::whole_value_matches` builds, and the
/// predicate is asked through `matches_runtime_type_predicate` and `observe`
/// rather than through the walk directly, so a case that passes here is a case
/// the interpreter answers the same way.
#[cfg(test)]
#[path = "runtime_type_predicate_test.rs"]
mod runtime_type_predicate_test;
