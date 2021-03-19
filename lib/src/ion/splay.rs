/*
 * The following license applies to this file, which has been derived
 * (transliterated) from the files `js/src/ds/SplayTree.h` in Mozilla
 * Firefox:
 *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

//! A splay-tree implementation.
//!
//! A special property of this data structure is that it is designed to work
//! with *indices* and an *external comparator*. This allows it to be very
//! memory-efficient.

use super::{ContainerComparator, ContainerIndex};
use smallvec::{smallvec, SmallVec};
use std::cmp::Ordering;
use std::fmt::Debug;

#[derive(Clone, Debug)]
pub(crate) struct SplayTree<Ix: ContainerIndex> {
    nodes: SmallVec<[SplayNode<Ix>; 8]>,
    root: u32,
    free: u32,
}

#[derive(Clone, Debug)]
struct SplayNode<Ix: ContainerIndex> {
    parent: u32,
    left: u32,
    right: u32,
    value: Ix,
}

const INVALID: u32 = u32::MAX;

impl<Ix: ContainerIndex> SplayTree<Ix> {
    pub(crate) fn new() -> SplayTree<Ix> {
        SplayTree {
            nodes: smallvec![],
            root: INVALID,
            free: INVALID,
        }
    }

    pub(crate) fn empty(&self) -> bool {
        self.root != INVALID
    }

    pub(crate) fn contains<C: ContainerComparator<Ix = Ix>>(
        &mut self,
        cmp: &C,
        ix: Ix,
    ) -> Option<Ix> {
        let (node_ix, cmp_result) = self.lookup_node(cmp, ix);
        if node_ix == INVALID {
            return None;
        }
        self.splay(node_ix);
        if cmp_result == Ordering::Equal {
            Some(self.node(node_ix).value)
        } else {
            None
        }
    }

    pub(crate) fn for_each<F: Fn(Ix)>(&self, f: F) {
        self.for_each_inner(&f, self.root);
    }

    fn for_each_inner<F: Fn(Ix)>(&self, f: &F, at: u32) {
        if at == INVALID {
            return;
        }
        let node = self.node(at);
        self.for_each_inner(f, node.left);
        f(node.value);
        self.for_each_inner(f, node.right);
    }

    pub(crate) fn insert<C: ContainerComparator<Ix = Ix>>(&mut self, cmp: &C, value: Ix) {
        let node = self.allocate_node(value);
        if self.root == INVALID {
            self.root = node;
            return;
        }
        let (parent, ordering) = self.lookup_node(cmp, value);
        assert!(parent != INVALID);
        match ordering {
            Ordering::Equal => panic!("Inserting a duplicate"),
            Ordering::Less => {
                assert_eq!(self.node(parent).left, INVALID);
                self.node_mut(parent).left = node;
                self.node_mut(node).parent = parent;
            }
            Ordering::Greater => {
                assert_eq!(self.node(parent).right, INVALID);
                self.node_mut(parent).right = node;
                self.node_mut(node).parent = parent;
            }
        }
        self.splay(node);
    }

    pub(crate) fn remove<C: ContainerComparator<Ix = Ix>>(&mut self, cmp: &C, value: Ix) -> bool {
        let (node, ordering) = self.lookup_node(cmp, value);
        if node == INVALID || ordering != Ordering::Equal {
            return false;
        }
        self.splay(node);
        assert_eq!(node, self.root);

        let (swap, swap_child) = if self.node(node).left != INVALID {
            let mut swap = self.node(node).left;
            while self.node(swap).right != INVALID {
                swap = self.node(swap).right;
            }
            (swap, self.node(swap).left)
        } else if self.node(node).right != INVALID {
            let mut swap = self.node(node).right;
            while self.node(swap).left != INVALID {
                swap = self.node(swap).left;
            }
            (swap, self.node(swap).right)
        } else {
            self.free_node(self.root);
            self.root = INVALID;
            return true;
        };

        let parent = self.node(swap).parent;
        if self.node(parent).left == swap {
            self.node_mut(parent).left = swap_child;
        } else {
            self.node_mut(parent).right = swap_child;
        }
        if swap_child != INVALID {
            self.node_mut(swap_child).parent = parent;
        }

        let value = self.node(swap).value;
        self.node_mut(self.root).value = value;
        self.free_node(swap);
        true
    }

    fn allocate_node(&mut self, value: Ix) -> u32 {
        if self.free != INVALID {
            let n = self.free;
            self.free = self.node(n).left;
            let node = self.node_mut(n);
            node.value = value;
            node.parent = INVALID;
            node.left = INVALID;
            node.right = INVALID;
            n
        } else {
            let n = self.nodes.len() as u32;
            self.nodes.push(SplayNode {
                parent: INVALID,
                left: INVALID,
                right: INVALID,
                value,
            });
            n
        }
    }

    fn free_node(&mut self, node: u32) {
        assert!(node != INVALID);
        self.node_mut(node).left = self.free;
        self.free = node;
    }

    fn node(&self, n: u32) -> &SplayNode<Ix> {
        &self.nodes[n as usize]
    }
    fn node_mut(&mut self, n: u32) -> &mut SplayNode<Ix> {
        &mut self.nodes[n as usize]
    }

    fn lookup_node<C: ContainerComparator<Ix = Ix>>(&self, cmp: &C, ix: Ix) -> (u32, Ordering) {
        if self.root == INVALID {
            return (INVALID, Ordering::Less);
        }
        let mut node = self.root;
        let mut parent;
        let mut ordering;
        loop {
            parent = node;
            match cmp.compare(ix, self.node(node).value) {
                Ordering::Equal => {
                    return (node, Ordering::Equal);
                }
                Ordering::Less => {
                    node = self.node(node).left;
                    ordering = Ordering::Less;
                }
                Ordering::Greater => {
                    node = self.node(node).right;
                    ordering = Ordering::Greater;
                }
            }
            if node == INVALID {
                break;
            }
        }
        (parent, ordering)
    }

    fn splay(&mut self, node: u32) {
        assert!(node != INVALID);
        while node != self.root {
            let parent = self.node(node).parent;
            if parent == self.root {
                self.rotate(node);
                assert_eq!(node, self.root);
                return;
            }
            let grandparent = self.node(parent).parent;
            if (self.node(parent).left == node) == (self.node(grandparent).left == parent) {
                self.rotate(parent);
                self.rotate(node);
            } else {
                self.rotate(node);
                self.rotate(node);
            }
        }
    }

    fn rotate(&mut self, node: u32) {
        assert!(node != INVALID);
        let parent = self.node(node).parent;
        if self.node(parent).left == node {
            let right = self.node(node).right;
            self.node_mut(parent).left = right;
            if right != INVALID {
                self.node_mut(right).parent = parent;
            }
            self.node_mut(node).right = parent;
        } else {
            let left = self.node(node).left;
            self.node_mut(parent).right = left;
            if left != INVALID {
                self.node_mut(left).parent = parent;
            }
            self.node_mut(node).left = parent;
        }
        self.node_mut(node).parent = self.node(parent).parent;
        self.node_mut(parent).parent = node;
        let grandparent = self.node(node).parent;
        if grandparent != INVALID {
            if self.node(grandparent).left == parent {
                self.node_mut(grandparent).left = node;
            } else {
                self.node_mut(grandparent).right = node;
            }
        } else {
            self.root = node;
        }
    }
}
