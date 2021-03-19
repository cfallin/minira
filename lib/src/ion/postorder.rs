//! Fast postorder computation with no allocations (aside from result).

use crate::{BlockIx, Function};
use smallvec::{smallvec, SmallVec};
use std::borrow::Cow;

pub(crate) fn calculate<F: Function>(func: &F) -> Vec<BlockIx> {
    let num_blocks = func.blocks().len();
    let mut ret = vec![];

    // State: visited-block map, and explicit DFS stack.
    let mut visited = vec![];
    visited.resize(num_blocks, false);

    struct State<'a> {
        block: BlockIx,
        succs: Cow<'a, [BlockIx]>,
        next_succ: usize,
    }
    let mut stack: SmallVec<[State; 64]> = smallvec![];

    let entry = func.entry_block();
    visited[entry.get() as usize] = true;
    stack.push(State {
        block: entry,
        succs: func.block_succs(entry),
        next_succ: 0,
    });

    while let Some(ref mut state) = stack.last_mut() {
        // Perform one action: push to new succ, skip an already-visited succ, or pop.
        if state.next_succ < state.succs.len() {
            let succ = state.succs[state.next_succ];
            state.next_succ += 1;
            if !visited[succ.get() as usize] {
                visited[succ.get() as usize] = true;
                stack.push(State {
                    block: succ,
                    succs: func.block_succs(succ),
                    next_succ: 0,
                });
            }
        } else {
            ret.push(state.block);
            stack.pop();
        }
    }

    ret
}
