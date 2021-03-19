/*
 * The following license applies to this file, which has been derived
 * (transliterated) from the files `js/src/jit/BacktrackingAllocator.h` and
 * `js/src/jit/BacktrackingAllocator.cpp` in Mozilla Firefox:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

//! Backtracking register allocator on SSA code ported from IonMonkey's
//! BacktrackingAllocator.

/*
 * TODO:
 * - Compute liveness info (`buildLivenessInfo()`)
 * - mergeAndQueueRegisters
 * - processBundle
 * - splits
 * - eviction
 * - move insertion (`resolveControlFlow()`)
 *   - "movegroup" instruction?
 * - regalloc fuzzer: generate valid SSA
 *   - simple approach: phi for every local in every block?
 *   - two "modes" per local: the above, or def in entry block
 *     and use elsewhere?
 * - hook up checker
 *   - handle phis/movegroups
 *
 * - modify CL to generate SSA VCode
 *   - lower phis to phis directly
 *   - movegroup impl with scratch regs
 *   - use temps properly (`alloc_tmp()` vs `alloc_reg()`)
 *
 * - produce stackmaps
 */

#![allow(dead_code, unused_imports)]

use crate::{
    domtree, BlockIx, Function, InstIx, RealReg, RealRegUniverse, RegAllocError, RegAllocResult,
    RegClass, RegClassInfo, RegSlotConstraint, RegSlotInfo, RegSlotKind, RegSlotLoc, TypedIxVec,
    VirtualReg,
};
use smallvec::{smallvec, SmallVec};
use std::cmp::Ordering;
use std::fmt::Debug;

mod cfg;
mod binheap;
mod postorder;
mod splay;

pub(crate) trait ContainerIndex: Clone + Copy + Debug + PartialEq + Eq {}

pub(crate) trait ContainerComparator {
    type Ix: ContainerIndex;
    fn compare(&self, a: Self::Ix, b: Self::Ix) -> Ordering;
}

#[cfg(not(debug))]
fn validate_ssa<F: Function>(_: &F, _: &cfg::CFGInfo) -> Result<(), RegAllocError> {
    Ok(())
}

#[cfg(debug)]
fn validate_ssa<F: Function>(f: &F, cfginfo: &cfg::CFGInfo) -> Result<(), RegAllocError> {
    // Walk the blocks in RPO. We should see every def before any uses, aside from phi inputs.
    let mut defined = vec![f.num_vregs(); false];
    for block in cfginfo.postorder.iter().rev() {
        for iix in f.block_insns(block) {
            let slots = f.get_reg_slot_info(iix);
            if let Some(phiinfo) = f.is_phi(iix) {
                assert_eq!(phiinfo.inputs.len(), f.block_preds(block).len());
                for (pred, input) in f.block_preds(block).iter().zip(phiinfo.inputs.iter()) {
                    let vreg = input.to_virtual_reg();
                    let def_block = cfginfo.def[vreg.get_index()];
                    if def_block.is_invalid() {
                        return Err(RegAllocError::SSA(vreg, iix));
                    }
                    if !cfginfo.dominates(def_block, pred) {
                        return Err(RegAllocError::SSA(vreg, iix));
                    }
                }
            } else {
                for slot in &slots {
                    match slot.kind {
                        RegSlotKind::Use => {
                            if !defined[slot.vreg.get_index()] {
                                return Err(RegAllocError::SSA(slot.vreg, iix));
                            }
                        }
                        _ => {}
                    }
                }
            }
            for slot in &slots {
                match slot.kind {
                    RegSlotKind::Def => {
                        if !defined[slot.vreg.get_index()] {
                            return Err(RegAllocError::SSA(slot.vreg, iix));
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CodePosition {
    Before(InstIx),
    After(InstIx),
}

/// A range from `from` (inclusive) to `to` (exclusive).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CodeRange {
    from: CodePosition,
    to: CodePosition,
}

impl std::cmp::PartialOrd for CodeRange {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl std::cmp::Ord for CodeRange {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.to <= other.from {
            Ordering::Less
        } else if self.from >= other.to {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

macro_rules! define_index {
    ($ix:ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
        pub(crate) struct $ix(u32);
        impl $ix {
            pub(crate) fn index(self) -> usize {
                self.0 as usize
            }
            pub(crate) fn invalid() -> Self {
                Self(u32::MAX)
            }
            pub(crate) fn is_invalid(self) -> bool {
                self == Self::invalid()
            }
            pub(crate) fn is_valid(self) -> bool {
                self != Self::invalid()
            }
        }

        impl ContainerIndex for $ix {}
    };
}
define_index!(LiveBundleIndex);
define_index!(LiveRangeIndex);
define_index!(SpillSetIndex);
define_index!(UseIndex);
define_index!(DefIndex);
define_index!(VRegIndex);
define_index!(PrioQueueIndex);

#[derive(Clone, Debug)]
struct LiveRange {
    range: CodeRange,
    vreg: VirtualReg,
    bundle: LiveBundleIndex,
    uses_spill_weight: u32,
    num_uses: u32,

    first_use: UseIndex,
    def: DefIndex,

    next_in_bundle: LiveRangeIndex,
    next_in_reg: LiveRangeIndex,
}

#[derive(Clone, Debug)]
struct Use {
    vreg: VRegIndex,
    pos: CodePosition,
    policy: RegSlotConstraint,
}

#[derive(Clone, Debug)]
struct Def {
    vreg: VRegIndex,
    pos: CodePosition,
    policy: RegSlotConstraint,
}

#[derive(Clone, Debug)]
struct LiveBundle {
    first_range: LiveRangeIndex,
    spillset: SpillSetIndex,
    spill_parent: LiveBundleIndex,
    allocation: RegSlotLoc,
}

#[derive(Clone, Debug)]
struct SpillSet {
    parent: SpillSetIndex,
    bundles: SmallVec<[LiveBundleIndex; 4]>,
}

#[derive(Clone, Debug)]
struct VReg {
    reg: VirtualReg,
    def: DefIndex,
    first_range: LiveRangeIndex,
    is_temp: bool,
    used_by_phi: bool,
    must_copy_input: bool,
}

#[derive(Clone, Debug)]
struct PReg {
    reg: RealReg,
    ranges: LiveRangeSet,
}

/*
 * Environment setup:
 *
 * We have seven fundamental objects: LiveRange, LiveBundle, SpillSet, Use, Def, VReg, PReg.
 *
 * The relationship is as follows:
 *
 * LiveRange --(vreg)--> shared(VReg)
 * LiveRange --(bundle)--> shared(LiveBundle)
 * LiveRange --(def)--> owns(Def)
 * LiveRange --(use) --> list(Use)
 *
 * Use --(vreg)--> shared(VReg)
 *
 * Def --(vreg) --> owns(VReg)
 *
 * LiveBundle --(range)--> list(LiveRange)
 * LiveBundle --(spillset)--> shared(SpillSet)
 * LiveBundle --(parent)--> parent(LiveBundle)
 *
 * SpillSet --(parent)--> parent(SpillSet)
 * SpillSet --(bundles)--> list(LiveBundle)
 *
 * VReg --(range)--> list(LiveRange)
 *
 * PReg --(ranges)--> set(LiveRange)
 */

#[derive(Clone, Debug)]
struct Env<'a, F: Function> {
    func: &'a F,
    cfginfo: cfg::CFGInfo,
    rru: &'a RealRegUniverse,

    ranges: Vec<LiveRange>,
    bundles: Vec<LiveBundle>,
    spillsets: Vec<SpillSet>,
    uses: Vec<Use>,
    defs: Vec<Def>,
    regs: Vec<VReg>,
    allocation_queue: PrioQueue,
    stackslot_allocator: StackSlotAllocator,
    hot_code: LiveRangeSet,
    calls: Vec<CodePosition>,  // sorted list
    slots_single: Vec<usize>,
    slots_double: Vec<usize>,
    slots_quad: Vec<usize>,
    spilled_bundles: Vec<LiveBundleIndex>,
}

#[derive(Clone, Debug)]
struct PrioQueue {
    items: Vec<PrioQueueItem>,
    heap: binheap::BinHeap<PrioQueueIndex>,
}

#[derive(Clone, Debug)]
struct PrioQueueItem {
    bundle: LiveBundleIndex,
    prio: usize,
}

#[derive(Clone, Debug)]
struct StackSlotAllocator {
    height: usize,
    normal_slots: Vec<usize>,
    double_slots: Vec<usize>,
}

#[derive(Clone, Debug)]
struct LiveRangeSet {
    splay_tree: splay::SplayTree<LiveRangeIndex>,
}

#[derive(Clone, Debug)]
struct LiveRangeCmp<'a> {
    ranges: &'a [LiveRange],
}

impl<'a> ContainerComparator for LiveRangeCmp<'a> {
    type Ix = LiveRangeIndex;
    fn compare(&self, a: Self::Ix, b: Self::Ix) -> std::cmp::Ordering {
        self.ranges[a.index()]
            .range
            .cmp(&self.ranges[b.index()].range)
    }
}

impl PrioQueue {
    fn new() -> Self {
        PrioQueue {
            items: vec![],
            heap: binheap::BinHeap::new(),
        }
    }
}

impl StackSlotAllocator {
    pub(crate) fn new() -> Self {
        StackSlotAllocator {
            height: 0,
            normal_slots: vec![],
            double_slots: vec![],
        }
    }
}

impl LiveRangeSet {
    pub(crate) fn new() -> Self {
        Self {
            splay_tree: splay::SplayTree::new(),
        }
    }
}

impl<'a, F: Function> Env<'a, F> {
    pub(crate) fn new(func: &'a F, rru: &'a RealRegUniverse, cfginfo: cfg::CFGInfo) -> Self {
        Self {
            func,
            rru,
            cfginfo,

            bundles: vec![],
            ranges: vec![],
            spillsets: vec![],
            uses: vec![],
            defs: vec![],
            regs: vec![],
            allocation_queue: PrioQueue::new(),
            stackslot_allocator: StackSlotAllocator::new(),
            calls: vec![],
            hot_code: LiveRangeSet::new(),
            slots_single: vec![],
            slots_double: vec![],
            slots_quad: vec![],
            spilled_bundles: vec![],
        }
    }

    fn lr_cmp<'b>(&'b self) -> LiveRangeCmp<'b> {
        LiveRangeCmp {
            ranges: &self.ranges[..],
        }
    }

    pub(crate) fn init(&mut self) -> Result<(), RegAllocError> {
        // Initialize uses, defs, and regs.


        // Initialize hot_code to contain inner loops only.

        Ok(())
    }
}

pub(crate) fn run<F: Function>(
    func: &F,
    rru: &RealRegUniverse,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let cfginfo = cfg::CFGInfo::new(func);
    validate_ssa(func, &cfginfo)?;

    let mut env = Env::new(func, rru, cfginfo);
    env.init()?;

    Err(RegAllocError::Other("unimplemented".into()))
}
