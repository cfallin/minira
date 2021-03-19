// This is an implementation of the algorithm described in
//
//   A Simple, Fast Dominance Algorithm
//   Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy
//   Department of Computer Science, Rice University, Houston, Texas, USA
//   TR-06-33870
//   https://www.cs.rice.edu/~keith/EMBED/dom.pdf

use crate::{BlockIx, TypedIxVec};
use log::info;
use std::borrow::Cow;

// Helper
fn dt_merge_sets(
    idom: &TypedIxVec<BlockIx, BlockIx>,
    bix2rpostord: &TypedIxVec<BlockIx, Option<u32>>,
    mut node1: BlockIx,
    mut node2: BlockIx,
) -> BlockIx {
    while node1 != node2 {
        if node1.is_invalid() || node2.is_invalid() {
            return BlockIx::invalid_value();
        }
        let rpo1 = bix2rpostord[node1].unwrap();
        let rpo2 = bix2rpostord[node2].unwrap();
        if rpo1 > rpo2 {
            node1 = idom[node1];
        } else if rpo2 > rpo1 {
            node2 = idom[node2];
        }
    }
    assert!(node1 == node2);
    node1
}

pub(crate) fn calculate<'a, PredFn: Fn(BlockIx) -> Cow<'a, [BlockIx]>>(
    num_blocks: u32,
    preds: PredFn,
    post_ord: &[BlockIx],
    start: BlockIx,
) -> TypedIxVec<BlockIx, BlockIx> {
    info!("        calc_dom_tree: begin");

    // We have post_ord, which is the postorder sequence.

    // Compute bix2rpostord, which maps a BlockIx to its reverse postorder
    // number.  And rpostord2bix, which maps a reverse postorder number to its
    // BlockIx.
    let mut bix2rpostord = TypedIxVec::<BlockIx, Option<u32>>::new();
    let mut rpostord2bix = vec![];
    bix2rpostord.resize(num_blocks, None);
    rpostord2bix.resize(num_blocks as usize, BlockIx::invalid_value());
    for n in 0..num_blocks {
        // bix visits the blocks in reverse postorder
        let bix = post_ord[(num_blocks - 1 - n) as usize];
        // Hence:
        bix2rpostord[bix] = Some(n);
        // and
        rpostord2bix[n as usize] = bix;
    }

    let mut idom = TypedIxVec::<BlockIx, BlockIx>::new();
    idom.resize(num_blocks, BlockIx::invalid_value());

    // The start node must have itself as a parent.
    idom[start] = start;

    for i in 0..num_blocks {
        let block_ix = BlockIx::new(i);
        // All nodes must be reachable from the root.  That means that all nodes
        // that aren't `start` must have at least one predecessor.  However, we
        // can't assert the inverse case -- that the start node has no
        // predecessors -- because the start node might be a self-loop, in which
        // case it will have itself as a pred.  See tests/domtree_fuzz1.rat.
        if block_ix != start {
            assert!(!preds(block_ix).is_empty());
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for n in 0..num_blocks {
            // Consider blocks in reverse postorder.
            let node = rpostord2bix[n as usize];
            assert!(node.is_valid());
            let rponum = bix2rpostord[node].unwrap();

            let mut parent = BlockIx::invalid_value();
            for &pred in preds(node).iter() {
                let pred_rpo = bix2rpostord[pred].unwrap();
                if pred_rpo < rponum {
                    parent = pred;
                    break;
                }
            }

            if parent.is_valid() {
                for &pred in preds(node).iter() {
                    if pred == parent {
                        continue;
                    }
                    if idom[pred].is_invalid() {
                        continue;
                    }
                    parent = dt_merge_sets(&idom, &bix2rpostord, parent, pred);
                }
            }

            if parent.is_valid() && parent != idom[node] {
                idom[node] = parent;
                changed = true;
            }
        }
    }

    // Check what we can.  The start node should be its own parent.  All other
    // nodes should not be their own parent, since we are assured that there are
    // no dead blocks in the graph, and hence that there is only one dominator
    // tree, that covers the whole graph.
    assert!(idom[start] == start);
    for i in 0..num_blocks {
        let block_ix = BlockIx::new(i);
        // All "parent pointers" are valid.
        assert!(idom[block_ix].is_valid());
        // The only node whose parent pointer points to itself is the start node.
        assert!((idom[block_ix] == block_ix) == (block_ix == start));
    }

    info!("        calc_dom_tree: end");
    idom
}
