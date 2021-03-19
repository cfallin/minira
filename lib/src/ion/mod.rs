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

#![allow(dead_code, unused_imports)]

use crate::{
    domtree, BlockIx, Function, InstIx, RealReg, RealRegUniverse, RegAllocError, RegAllocResult,
    RegClass, RegClassInfo, RegSlotConstraint, RegSlotInfo, RegSlotKind, RegSlotLoc, TypedIxVec,
    VirtualReg,
};
use smallvec::{smallvec, SmallVec};
use std::cmp::Ordering;
use std::fmt::Debug;

mod binheap;
mod postorder;
mod splay;

pub(crate) trait ContainerIndex: Clone + Copy + Debug + PartialEq + Eq {}

pub(crate) trait ContainerComparator {
    type Ix: ContainerIndex;
    fn compare(&self, a: Self::Ix, b: Self::Ix) -> Ordering;
}

struct CFGInfo {
    postorder: Vec<BlockIx>,
    domtree: TypedIxVec<BlockIx, BlockIx>,
    insn_block: TypedIxVec<InstIx, BlockIx>,
    def: Vec</* VirtualReg index, */ InstIx>,
}

impl CFGInfo {
    fn new<F: Function>(f: &F) -> CFGInfo {
        assert!(f.is_ssa());

        let postorder = postorder::calculate(f);
        let domtree = domtree::calculate(
            f.blocks().len() as u32,
            |block| f.block_preds(block),
            &postorder[..],
            f.entry_block(),
        );
        let mut insn_block = TypedIxVec::new();
        insn_block.resize(f.insns().len() as u32, BlockIx::invalid_value());
        let mut def = vec![InstIx::invalid_value(); f.get_num_vregs()];

        for bix in f.blocks() {
            for iix in f.block_insns(bix) {
                insn_block[iix] = bix;
                for slot in f.get_reg_slot_info(iix).iter() {
                    if slot.kind == RegSlotKind::Def {
                        def[slot.vreg.get_index()] = iix;
                    }
                }
            }
        }

        CFGInfo {
            postorder,
            domtree,
            insn_block,
            def,
        }
    }

    fn dominates(&self, a: BlockIx, mut b: BlockIx) -> bool {
        loop {
            if a == b {
                return true;
            }
            if b.is_invalid() {
                return false;
            }
            b = self.domtree[b];
        }
    }
}

#[cfg(not(debug))]
fn validate_ssa<F: Function>(_: &F, _: &CFGInfo) -> Result<(), RegAllocError> {
    Ok(())
}

#[cfg(debug)]
fn validate_ssa<F: Function>(f: &F, cfginfo: &CFGInfo) -> Result<(), RegAllocError> {
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CodeRange {
    from: CodePosition,
    to: CodePosition,
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
struct Env {
    ranges: Vec<LiveRange>,
    bundles: Vec<LiveBundle>,
    spillsets: Vec<SpillSet>,
    uses: Vec<Use>,
    defs: Vec<Def>,
    regs: Vec<VReg>,
    queue: binheap::BinHeap<LiveBundleIndex>,
    // TODO: rest of fields of BacktrackingAllocator
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

impl Env {
    fn lr_cmp<'a>(&'a self) -> LiveRangeCmp<'a> {
        LiveRangeCmp {
            ranges: &self.ranges[..],
        }
    }
}

pub(crate) fn run<F: Function>(
    func: &F,
    rru: &RealRegUniverse,
) -> Result<RegAllocResult<F>, RegAllocError> {
    let cfginfo = CFGInfo::new(func);
    validate_ssa(func, &cfginfo)?;

    Err(RegAllocError::Other("unimplemented".into()))
}
