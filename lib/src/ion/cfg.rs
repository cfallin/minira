//! Lightweight CFG analyses.

use crate::{TypedIxVec, BlockIx, InstIx, Function, domtree, RegSlotKind};
use super::{postorder, CodePosition};

#[derive(Clone, Debug)]
pub(crate) struct CFGInfo {
    pub(crate) postorder: Vec<BlockIx>,
    pub(crate) domtree: TypedIxVec<BlockIx, BlockIx>,
    pub(crate) insn_block: TypedIxVec<InstIx, BlockIx>,
    pub(crate) def: Vec</* VirtualReg index, */ InstIx>,
    pub(crate) block_entry: TypedIxVec<BlockIx, CodePosition>,
    pub(crate) block_exit: TypedIxVec<BlockIx, CodePosition>,
}

impl CFGInfo {
    pub(crate) fn new<F: Function>(f: &F) -> CFGInfo {
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
        let mut block_entry = TypedIxVec::new();
        let mut block_exit = TypedIxVec::new();
        block_entry.resize(f.blocks().len() as u32, CodePosition::Before(InstIx::invalid_value()));
        block_exit.resize(f.blocks().len() as u32, CodePosition::Before(InstIx::invalid_value()));

        for bix in f.blocks() {
            for iix in f.block_insns(bix) {
                insn_block[iix] = bix;
                for slot in f.get_reg_slot_info(iix).iter() {
                    if slot.kind == RegSlotKind::Def {
                        def[slot.vreg.get_index()] = iix;
                    }
                }
            }
            block_entry[bix] = CodePosition::Before(f.block_insns(bix).first());
            block_exit[bix] = CodePosition::After(f.block_insns(bix).last());
        }

        CFGInfo {
            postorder,
            domtree,
            insn_block,
            def,
            block_entry,
            block_exit,
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
