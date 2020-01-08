//! Implementation of the linear scan allocator algorithm.

use crate::analysis::run_analysis;
use crate::data_structures::{
    i_reload, i_spill, mkBlockIx, mkFrag, mkFragIx, mkInsnIx, mkInsnPoint, mkRLRIx,
    mkRReg, mkSlot, mkVLRIx, Block, BlockIx, Frag, FragIx, FragKind, Func, Insn, InsnIx, InsnPoint,
    InsnPoint_D, InsnPoint_R, InsnPoint_S, InsnPoint_U, Map, Point, RLRIx, RReg, Reg, Reg_V, Set,
    Show, Slot, SortedFragIxs, TVec, VLRIx, VReg, Vec_Block, Vec_Frag, Vec_Insn, Vec_RLR, Vec_VLR,
    RLR, VLR, PlusOne
};

fn expire_old_intervals() {
    unimplemented!("expire_old_intervals");
}

fn try_allocate() {
    unimplemented!("try_allocate");
}

fn spill_at_interval() {
    unimplemented!("spill_at_interval");
}

struct IntervalIterator<'a> {
    cur_rlr: RLRIx,
    cur_vlr: VLRIx,
    cur_rlr_frag: FragIx,
    cur_vlr_frag: FragIx,
    rlrs: &'a Vec_RLR,
    vlrs: &'a Vec_VLR,
    frags: &'a Vec_Frag,
}

impl<'a> IntervalIterator<'a> {
    fn new(rlrs: &'a Vec_RLR, vlrs: &'a Vec_VLR, frags: &'a Vec_Frag) -> Self {
        Self {
            cur_rlr: mkRLRIx(0),
            cur_vlr: mkVLRIx(0),
            cur_rlr_frag: mkFragIx(0),
            cur_vlr_frag: mkFragIx(0),
            rlrs,
            vlrs,
            frags,
        }
    }
}

impl<'a> Iterator for IntervalIterator<'a> {
    type Item = &'a Frag;

    fn next(&mut self) -> Option<Self::Item> {
        // Skip to the next RLR if needed.
        if self.cur_rlr.get() < self.rlrs.len() {
            if self.cur_rlr_frag >= self.rlrs[self.cur_rlr].sfrags.len() {
                self.cur_rlr = self.cur_rlr.plus_one();
                self.cur_rlr_frag = 0;
            }
        }

        // Skip to the next VLR if needed.
        if self.cur_vlr.get() < self.vlrs.len() {
            if self.cur_vlr_frag >= self.vlrs[self.cur_vlr].sfrags.len() {
                self.cur_vlr = self.cur_vlr.plus_one();
                self.cur_vlr_frag = 0;
            }
        }

        // No VLR => only look at RLR.
        if self.cur_vlr.get() == self.vlrs.len() {
            if self.cur_rlr.get() >= self.rlrs.len() || self.cur_rlr_frag.get() >= self.rlrs[self.cur_rlr].sfrags.len() {
                return None;
            }

            let ret = &self.rlrs[self.cur_rlr].sfrags[self.cur_rlr_frag];
            self.cur_rlr_frag += 1;
            return Some(ret);
        }

        unreachable!();

        //let rlr = &self.rlr[self.cur_rlr];
        //let vlr = &self.vlrs[self.cur_vlr];
        //let rlr_frag = &rlr.sfrags[self.cur_rlr_frag];
        //let vlr_frag = &vlrs.sfrags[self.cur_vlr_frag];
        //if rlr_frag.first < vlr_frag.first {
        //}
    }
}

// Allocator top level.  |func| is modified so that, when this function
// returns, it will contain no VReg uses.  Allocation can fail if there are
// insufficient registers to even generate spill/reload code, or if the
// function appears to have any undefined VReg/RReg uses.
#[inline(never)]
pub fn alloc_main(func: &mut Func, nRRegs: usize) -> Result<(), String> {
    let (rlr_env, mut vlr_env, mut frag_env) = run_analysis(func, nRRegs)?;

    // Live ranges are already sorted by increasing start point.

    // Get the list of available registers.
    let mut available_registers = Vec::new();
    for i in 0..nRRegs {
        available_registers.push(mkRReg(i as u32));
    }

    // For each interval:
    // - expire old intervals
    // - try allocate
    //  - if success, good
    //  - if not, spill at interval
    let mut rlr_index = 0;
    let mut vlr_index = 0;
    let total_lr = rlr_env.len() + vlr_env.len();
    for i in 0..total_lr {
        // Select the first interval among real vs virtual.
        let cur_rlr = rlr_env[rlr_index];
    }

    unimplemented!("linear scan");
}
