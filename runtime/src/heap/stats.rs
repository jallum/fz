//! GC telemetry — facts captured from one Cheney pass.

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct AllocStat {
    pub allocs: u64,
    pub bytes: u64,
}

impl AllocStat {
    pub fn record(&mut self, bytes: u64) {
        self.allocs += 1;
        self.bytes += bytes;
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HeapAllocStats {
    pub total: AllocStat,
    pub list_cons: AllocStat,
    pub struct_: AllocStat,
    pub closure: AllocStat,
    /// Continuation frames the compiler builds to resume a call's caller;
    /// `closure` counts only the closures a program makes.
    pub continuation: AllocStat,
    pub map: AllocStat,
    pub bitstring: AllocStat,
    /// Binary views: the objects binary values above the inline threshold
    /// point at.
    pub binview: AllocStat,
    /// BinRefs: the one object per buffer per heap that holds its reference.
    pub binref: AllocStat,
    pub scalar_box: AllocStat,
    pub resource: AllocStat,
    pub other: AllocStat,
    /// Off-heap binary buffers allocated by this process.
    /// Deliberately NOT part of `total`: these bytes do not live on the
    /// process heap, do not move under Cheney and are not what `bytes`
    /// measures. They are counted because they are otherwise invisible --
    /// a binary view costs the same whether its bytes were freshly copied
    /// or shared with another view, so the stub counters cannot tell
    /// copying from sharing.
    pub shared_bin: AllocStat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapAllocKind {
    ListCons,
    Struct,
    Closure,
    Continuation,
    Map,
    Bitstring,
    BinView,
    BinRef,
    ScalarBox,
    Resource,
    Other,
}

impl HeapAllocStats {
    /// Record an off-heap binary buffer. Separate from `record` because
    /// these bytes are not heap bytes; see the `shared_bin` field.
    pub fn record_shared_bin(&mut self, bytes: u64) {
        self.shared_bin.record(bytes);
    }

    pub fn record(&mut self, kind: HeapAllocKind, bytes: u64) {
        self.total.record(bytes);
        match kind {
            HeapAllocKind::ListCons => self.list_cons.record(bytes),
            HeapAllocKind::Struct => self.struct_.record(bytes),
            HeapAllocKind::Closure => self.closure.record(bytes),
            HeapAllocKind::Continuation => self.continuation.record(bytes),
            HeapAllocKind::Map => self.map.record(bytes),
            HeapAllocKind::Bitstring => self.bitstring.record(bytes),
            HeapAllocKind::BinView => self.binview.record(bytes),
            HeapAllocKind::BinRef => self.binref.record(bytes),
            HeapAllocKind::ScalarBox => self.scalar_box.record(bytes),
            HeapAllocKind::Resource => self.resource.record(bytes),
            HeapAllocKind::Other => self.other.record(bytes),
        }
    }
}

/// Which blocks a collection took as from-space: the young blocks alone
/// (minor), or every block the heap owned (major).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Generation {
    #[default]
    Minor,
    Major,
}

impl Generation {
    pub fn as_str(self) -> &'static str {
        match self {
            Generation::Minor => "minor",
            Generation::Major => "major",
        }
    }
}

/// What made a binary view, and the BinRef it was made with if it entered a new
/// buffer: each place that allocates one names itself, so a collection can say
/// which of them its young views and BinRefs came from and which of the BinRefs
/// survived.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum StubSite {
    /// An append wrote into the spare room of the buffer its left side views,
    /// and the view is a longer window of that same buffer. It makes no BinRef.
    AppendedInPlace,
    /// A window onto part of a buffer larger than the inline threshold: a
    /// field or a tail taken out of a binary, copying nothing. It makes no
    /// BinRef.
    WindowOfBuffer,
    /// An append overflowed its buffer and the result went into a new one with
    /// room to grow.
    GrownBuffer,
    /// A binary above the inline threshold written into a new buffer sized to
    /// it: a built or copied binary, a `:binary.copy`, a literal.
    FilledBuffer,
    /// A message copy gave the receiving heap its own BinRef and view of a
    /// buffer the sender's heap also holds.
    MessageCopy,
    /// A program literal baked into the module, viewed in place.
    StaticLiteral,
}

impl StubSite {
    pub const ALL: [StubSite; 6] = [
        StubSite::AppendedInPlace,
        StubSite::WindowOfBuffer,
        StubSite::GrownBuffer,
        StubSite::FilledBuffer,
        StubSite::MessageCopy,
        StubSite::StaticLiteral,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            StubSite::AppendedInPlace => "appended_in_place",
            StubSite::WindowOfBuffer => "window_of_buffer",
            StubSite::GrownBuffer => "grown_buffer",
            StubSite::FilledBuffer => "filled_buffer",
            StubSite::MessageCopy => "message_copy",
            StubSite::StaticLiteral => "static_literal",
        }
    }

    pub(crate) fn code(self) -> u8 {
        self as u8
    }

    /// The site a stub stored as `code`.
    pub(crate) fn from_code(code: u8) -> StubSite {
        *Self::ALL
            .get(code as usize)
            .unwrap_or_else(|| panic!("stub site code {code} names no site"))
    }
}

/// A count of binary views or BinRefs for each site.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StubCounts([u64; StubSite::ALL.len()]);

impl StubCounts {
    pub fn record(&mut self, site: StubSite) {
        self.0[site as usize] += 1;
    }

    pub fn get(&self, site: StubSite) -> u64 {
        self.0[site as usize]
    }

    /// The counts as a JSON object, every site present, in declaration order.
    pub fn write_json(&self, out: &mut String) {
        use std::fmt::Write;
        out.push('{');
        for (index, site) in StubSite::ALL.into_iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            write!(out, "\"{}\":{}", site.as_str(), self.get(site)).unwrap();
        }
        out.push('}');
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GcStats {
    pub generation: Generation,
    /// Objects the collection copied: the survivors of its from-space.
    pub copied_objects: u64,
    /// Bytes the collection copied.
    pub copied_bytes: u64,
    /// Objects the heap holds once the collection finishes: what earlier
    /// collections kept and what this one copied.
    pub live_objects: u64,
    /// Bytes the heap holds once the collection finishes: what earlier
    /// collections kept and what this one copied.
    pub live_bytes: u64,
    /// Chain links the collection followed: each BinRef or resource stub it
    /// examined in the sweep. A binary view is on no chain and is never visited.
    pub stub_visits: u64,
    /// Binary views made since the heap's previous collection, by the site that
    /// made each: one per binary value above the inline threshold, including the
    /// view made together with a fresh buffer's BinRef.
    pub stubs_made: StubCounts,
    /// BinRefs made since the heap's previous collection, by the site that made
    /// each: one per buffer that entered the heap. Windows and in-place appends
    /// make none.
    pub binrefs_made: StubCounts,
    /// BinRefs this collection kept, by the site that made each: the survivors
    /// of the BinRefs it examined, which are the young ones for a minor
    /// collection and every one for a major collection. A BinRef survives when
    /// any view reached by the collection names it.
    pub stubs_survived: StubCounts,
    /// Bytes the heap allocated since its previous collection, by fill: what
    /// `should_gc` compared with `young_budget` when this collection was due.
    pub young_bytes: u64,
    /// The young bytes at which this collection was due.
    pub young_budget: u64,
    /// Capacity of the from-space blocks.
    pub from_space_capacity_bytes: u64,
    /// Blocks of the from-space the collection released.
    pub blocks_released: u64,
    /// Old blocks the heap holds once the collection finishes: every block
    /// that holds data a collection kept or a gift brought. The fresh tip is
    /// empty and is not counted.
    pub blocks_after: u64,
}
