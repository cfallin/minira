/*
 * The following license applies to this file, which has been derived
 * (transliterated) from the files `js/src/ds/PriorityQueue.h` in Mozilla
 * Firefox:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

//! Binary heap.

use super::{ContainerComparator, ContainerIndex};
use smallvec::{smallvec, SmallVec};
use std::cmp::Ordering;
use std::fmt::Debug;

#[derive(Clone, Debug)]
pub(crate) struct BinHeap<Ix: ContainerIndex> {
    nodes: SmallVec<[Ix; 64]>,
}

impl<Ix: ContainerIndex> BinHeap<Ix> {
    pub(crate) fn new() -> Self {
        Self { nodes: smallvec![] }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    pub(crate) fn pop_highest<C: ContainerComparator<Ix = Ix>>(&mut self, cmp: &C) -> Option<Ix> {
        if self.is_empty() {
            return None;
        }
        let ret = self.nodes[0];
        let last = self.nodes.pop().unwrap();
        if !self.nodes.is_empty() {
            self.nodes[0] = last;
            self.bubble_down(0, cmp);
        }
        Some(ret)
    }

    pub(crate) fn insert<C: ContainerComparator<Ix = Ix>>(&mut self, ix: Ix, cmp: &C) {
        self.nodes.push(ix);
        let idx = self.nodes.len() - 1;
        self.bubble_up(idx, cmp);
    }

    fn bubble_down<C: ContainerComparator<Ix = Ix>>(&mut self, mut idx: usize, cmp: &C) {
        loop {
            let left = 2 * idx + 1;
            let right = 2 * idx + 2;
            if left < self.nodes.len() {
                if right < self.nodes.len() {
                    if cmp.compare(self.nodes[idx], self.nodes[right]) == Ordering::Less
                        && cmp.compare(self.nodes[left], self.nodes[right]) == Ordering::Less
                    {
                        self.swap(idx, right);
                        idx = right;
                        continue;
                    }
                }
                if cmp.compare(self.nodes[idx], self.nodes[left]) == Ordering::Less {
                    self.swap(idx, left);
                    idx = left;
                    continue;
                }
            }
            break;
        }
    }

    fn bubble_up<C: ContainerComparator<Ix = Ix>>(&mut self, mut idx: usize, cmp: &C) {
        while idx > 0 {
            let parent = (idx - 1) / 2;
            if cmp.compare(self.nodes[parent], self.nodes[idx]) == Ordering::Greater {
                break;
            }
            self.swap(idx, parent);
            idx = parent;
        }
    }

    fn swap(&mut self, a: usize, b: usize) {
        let t = self.nodes[a];
        self.nodes[a] = self.nodes[b];
        self.nodes[b] = t;
    }
}
