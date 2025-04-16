// MIT License
//
// Copyright (c) 2022 Jonathan Guillotte-Blouin
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//
// Historical note
// ===============
//
// This was vendored in from the <https://github.com/jonathanGB/Unbounded-Interval-Tree>
// repository, commit 51082c68e0d4fe6fe4cdf09809cad106fc85abf2.
//
// SPDX-License-Identifier: MIT

//! An interval tree implemented with a binary search tree.
//!
//! Implementation of an interval tree ([`IntervalTree`]) that works with
//! inclusive/exclusive bounds, as well as unbounded intervals. It is based on
//! the data structure described in Cormen et al.
//! (2009, Section 14.3: Interval trees, pp. 348–354). It provides methods
//! for "stabbing queries" (as in "is point `p` or an interval `i` contained in
//! any intervals in the tree of intervals?"), as well as helpers to get the
//! difference between a queried interval and the database (in order to find
//! subsegments not covered), and the list of intervals in the database
//! overlapping a queried interval.
//!
//! Note that any type satisfying the [`Ord`] trait can be stored in this tree.
//!
//! ## Historical note
//!
//! This was vendored in from the <https://github.com/jonathanGB/Unbounded-Interval-Tree>
//! repository, commit
//! [`51082c68e0d4fe6fe4cdf09809cad106fc85abf2`](https://github.com/jonathanGB/Unbounded-Interval-Tree/commit/51082c68e0d4fe6fe4cdf09809cad106fc85abf2).

mod node;
#[cfg(test)]
mod tests;

use std::{
    borrow::Borrow,
    cmp::{Ordering, Ordering::*},
    fmt,
    ops::{Bound, Bound::*, RangeBounds},
};

use node::{Node, Range};
use serde_derive::{Deserialize, Serialize};

/// The interval tree storing all the underlying intervals.
///
/// There are three ways to create an interval tree.
/// ```
/// use simulans::interval_tree::IntervalTree;
///
/// // 1. Create an empty default interval tree.
/// let mut interval_tree = IntervalTree::default();
/// assert!(interval_tree.is_empty());
/// interval_tree.insert(0..9);
/// interval_tree.insert(27..);
/// assert_eq!(interval_tree.len(), 2);
///
/// // 2. Create an interval tree from an iterator.
/// let ranges = vec!["hello"..="hi", "Allo"..="Bonjour"];
/// let interval_tree = ranges.into_iter().collect::<IntervalTree<_>>();
/// assert_eq!(interval_tree.len(), 2);
///
/// // 3. Create an interval tree from an array.
/// let ranges = [(1, 5)..(1, 9), (2, 3)..(3, 7)];
/// let interval_tree = IntervalTree::from(ranges);
/// assert_eq!(interval_tree.len(), 2);
/// ```
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct IntervalTree<K> {
    root: Option<Box<Node<K>>>,
    size: usize,
}

impl<K> fmt::Display for IntervalTree<K>
where
    K: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.root {
            Some(ref root) => write!(f, "{}", root),
            None => write!(f, "Empty tree"),
        }
    }
}

impl<K> Default for IntervalTree<K> {
    fn default() -> Self {
        Self {
            root: None,
            size: 0,
        }
    }
}

/// Creates an [`IntervalTree`] from an iterator of elements
/// satisfying the [`RangeBounds`] trait.
impl<K, R> FromIterator<R> for IntervalTree<K>
where
    K: Ord + Clone,
    R: RangeBounds<K>,
{
    fn from_iter<T: IntoIterator<Item = R>>(iter: T) -> Self {
        let mut interval_tree = Self::default();

        for interval in iter {
            interval_tree.insert(interval);
        }

        interval_tree
    }
}

impl<K, R, const N: usize> From<[R; N]> for IntervalTree<K>
where
    K: Ord + Clone,
    R: RangeBounds<K>,
{
    fn from(intervals: [R; N]) -> Self {
        let mut interval_tree = Self::default();

        for interval in intervals {
            interval_tree.insert(interval);
        }

        interval_tree
    }
}

impl<K> IntervalTree<K> {
    /// Produces an in-order iterator for the interval tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::Included;
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// tree.insert((Included(0), Included(10)));
    /// tree.insert((Included(-5), Included(-1)));
    /// tree.insert((Included(20), Included(30)));
    ///
    /// let mut iter = tree.iter();
    /// assert_eq!(iter.next(), Some(&(Included(-5), Included(-1))));
    /// assert_eq!(iter.next(), Some(&(Included(0), Included(10))));
    /// assert_eq!(iter.next(), Some(&(Included(20), Included(30))));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub const fn iter(&self) -> IntervalTreeIter<'_, K> {
        IntervalTreeIter {
            to_visit: vec![],
            curr: &self.root,
        }
    }

    /// Inserts an interval `range` into the interval tree. Insertions respect
    /// the binary search properties of this tree.
    /// It is ok to insert a `range` that overlaps with an existing interval in
    /// the tree.
    ///
    /// An improvement to come is to rebalance the tree (following an AVL or a
    /// red-black scheme).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut int_tree = IntervalTree::default();
    ///
    /// int_tree.insert((Included(5), Excluded(9)));
    /// int_tree.insert(..=10);
    ///
    /// let mut str_tree: IntervalTree<&str> = IntervalTree::default();
    ///
    /// str_tree.insert("Noria"..);
    /// ```
    pub fn insert<R>(&mut self, range: R)
    where
        K: Ord + Clone,
        R: RangeBounds<K>,
    {
        let range = (range.start_bound().cloned(), range.end_bound().cloned());
        self.size += 1;

        // If the tree is empty, put new node at the root.
        if self.root.is_none() {
            self.root = Some(Box::new(Node::new(range)));
            return;
        }

        // Otherwise, walk down the tree and insert when we reach leaves.
        // TODO(jonathangb): Rotate tree?
        let mut curr = self.root.as_mut().unwrap();
        loop {
            curr.maybe_update_value(&range.1);

            match Self::cmp(&curr.key, &range) {
                Equal => return, // Don't insert a redundant key.
                Less => {
                    match curr.right {
                        None => {
                            curr.right = Some(Box::new(Node::new(range)));
                            return;
                        }
                        Some(ref mut node) => curr = node,
                    };
                }
                Greater => {
                    match curr.left {
                        None => {
                            curr.left = Some(Box::new(Node::new(range)));
                            return;
                        }
                        Some(ref mut node) => curr = node,
                    };
                }
            };
        }
    }

    /// A "stabbing query" in the jargon: returns whether or not a point `p`
    /// is contained in any of the intervals stored in the tree.
    ///
    /// The given point may be of a borrowed form of the stored type `K`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut int_tree = IntervalTree::default();
    ///
    /// int_tree.insert((Excluded(5), Unbounded));
    ///
    /// assert!(int_tree.contains_point(&100));
    /// assert!(!int_tree.contains_point(&5));
    /// ```
    ///
    /// Note that we can work with any type that implements the [`Ord`] trait,
    /// so we are not limited to just integers.
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut str_tree = IntervalTree::default();
    ///
    /// str_tree.insert((Excluded(String::from("Noria")), Unbounded));
    ///
    /// // Borrowed form (`str`) of `String`.
    /// assert!(!str_tree.contains_point("Noria"));
    /// // Also works with non-borrowed form.
    /// assert!(str_tree.contains_point(&String::from("Zebra")));
    /// ```
    pub fn contains_point<Q>(&self, p: &Q) -> bool
    where
        K: Ord + Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.contains_interval(&(Included(p), Included(p)))
    }

    /// An alternative "stabbing query": returns whether or not an interval
    /// `range` is fully covered by the intervals stored in the tree.
    ///
    /// The given `range` may have bounds that are of a borrowed form of the
    /// stored type `K`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// tree.insert((Included(20), Included(30)));
    /// tree.insert((Excluded(30), Excluded(50)));
    ///
    /// assert!(tree.contains_interval(&(20..=40)));
    /// // Borrowed form of the key works as well.
    /// assert!(!tree.contains_interval(&(&30..=&50)));
    /// ```
    ///
    /// Again, the given `range` can be any type implementing [`Ord`].
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree: IntervalTree<&str> = IntervalTree::default();
    ///
    /// let key1 = (Included("a"), Excluded("h"));
    /// let key2 = (Excluded("M"), Excluded("O"));
    ///
    /// tree.insert(key1.clone());
    /// tree.insert(key2);
    ///
    /// assert!(tree.contains_interval(&("a".."h")));
    /// assert!(!tree.contains_interval(&("N"..="O")));
    /// // Sometimes, we have to disambiguate the key type.
    /// assert!(tree.contains_interval::<&str, _>(&key1));
    /// ```
    pub fn contains_interval<Q, R>(&self, range: &R) -> bool
    where
        K: Ord + Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        self.get_interval_difference(range).is_empty()
    }

    /// Returns the in-order list of all references to intervals stored in the
    /// tree that overlaps with the given `range` (partially or completely).
    ///
    /// The given `range` may have bounds that are of a borrowed form of the
    /// stored type `K`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// tree.insert((Included(0), Included(5)));
    /// tree.insert((Included(7), Excluded(10)));
    ///
    /// assert_eq!(
    ///     tree.get_interval_overlaps(&(-5..7)),
    ///     vec![&(Included(0), Included(5))]
    /// );
    /// // Borrowed form of the key works as well.
    /// assert!(tree.get_interval_overlaps(&(&10..)).is_empty());
    /// ```
    pub fn get_interval_overlaps<Q, R>(&self, range: &R) -> Vec<&Range<K>>
    where
        K: Ord + Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let curr = &self.root;
        let mut acc = Vec::new();

        Self::get_interval_overlaps_rec(curr, range, &mut acc);
        acc
    }

    /// Returns the ordered list of subintervals in `range` that are not covered
    /// by the tree. This is useful to compute what subsegments of `range`
    /// that are not covered by the intervals stored in the tree.
    ///
    /// If `range` is not covered at all, this simply returns a one element
    /// vector containing the bounds of `range`.
    ///
    /// The given `range` may have bounds that are of a borrowed form of the
    /// stored type `K`. Because all the bounds returned are either from the
    /// interval tree of from the `range`, we return references to these
    /// bounds rather than clone them.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// tree.insert((Included(0), Excluded(10)));
    /// tree.insert((Excluded(10), Included(30)));
    /// tree.insert((Excluded(50), Unbounded));
    ///
    /// assert_eq!(
    ///     tree.get_interval_difference(&(-5..=30)),
    ///     vec![
    ///         (Included(&-5), Excluded(&0)),
    ///         (Included(&10), Included(&10))
    ///     ]
    /// );
    /// assert_eq!(
    ///     tree.get_interval_difference(&(..10)),
    ///     vec![(Unbounded, Excluded(&0))]
    /// );
    /// assert!(tree.get_interval_difference(&(100..)).is_empty());
    /// ```
    pub fn get_interval_difference<'a, Q, R>(&'a self, range: &'a R) -> Vec<Range<&'a Q>>
    where
        K: Ord + Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        let overlaps = self.get_interval_overlaps(range);

        // If there is no overlap, then the difference is the query `q` itself.
        if overlaps.is_empty() {
            let min = range.start_bound();
            let max = range.end_bound();
            return vec![(min, max)];
        }

        let mut acc = Vec::new();
        let first = overlaps.first().unwrap();

        // If q.min < first.min, we have a difference to append.
        match (range.start_bound(), first.start_bound()) {
            (Unbounded, Included(first_min)) => acc.push((Unbounded, Excluded(first_min.borrow()))),
            (Unbounded, Excluded(first_min)) => acc.push((Unbounded, Included(first_min.borrow()))),
            (Included(q_min), Included(first_min)) if q_min < first_min.borrow() => {
                acc.push((Included(q_min), Excluded(first_min.borrow())))
            }
            (Excluded(q_min), Included(first_min)) if q_min < first_min.borrow() => {
                acc.push((Excluded(q_min), Excluded(first_min.borrow())))
            }
            (Excluded(q_min), Excluded(first_min)) if q_min < first_min.borrow() => {
                acc.push((Excluded(q_min), Included(first_min.borrow())))
            }
            (Included(q_min), Excluded(first_min)) if q_min <= first_min.borrow() => {
                acc.push((Included(q_min), Included(first_min.borrow())))
            }
            _ => {}
        };

        // If the max is unbounded, there can't be any difference going forward.
        if first.1 == Unbounded {
            return acc;
        }

        let mut contiguous = &first.1; // keeps track of the maximum of a contiguous interval.
        for overlap in overlaps.iter().skip(1) {
            // If contiguous < overlap.min:
            //   1. We have a difference between contiguous -> overlap.min to fill.
            //     1.1: Note: the endpoints of the difference appended are the opposite,
            //          that is if contiguous was Included, then the difference must
            //          be Excluded, and vice versa.
            //   2. We need to update contiguous to be the new contiguous max.
            // Note: an Included+Excluded at the same point still is contiguous!
            match (&contiguous, &overlap.0) {
                (Included(contiguous_max), Included(overlap_min))
                    if contiguous_max < overlap_min =>
                {
                    acc.push((
                        Excluded(contiguous_max.borrow()),
                        Excluded(overlap_min.borrow()),
                    ));
                    contiguous = &overlap.1;
                }
                (Included(contiguous_max), Excluded(overlap_min))
                    if contiguous_max < overlap_min =>
                {
                    acc.push((
                        Excluded(contiguous_max.borrow()),
                        Included(overlap_min.borrow()),
                    ));
                    contiguous = &overlap.1;
                }
                (Excluded(contiguous_max), Included(overlap_min))
                    if contiguous_max < overlap_min =>
                {
                    acc.push((
                        Included(contiguous_max.borrow()),
                        Excluded(overlap_min.borrow()),
                    ));
                    contiguous = &overlap.1;
                }
                (Excluded(contiguous_max), Excluded(overlap_min))
                    if contiguous_max <= overlap_min =>
                {
                    acc.push((
                        Included(contiguous_max.borrow()),
                        Included(overlap_min.borrow()),
                    ));
                    contiguous = &overlap.1;
                }
                _ => {}
            }

            // If contiguous.max < overlap.max, we set contiguous to the new max.
            match (&contiguous, &overlap.1) {
                (_, Unbounded) => return acc,
                (Included(contiguous_max), Included(overlap_max))
                | (Excluded(contiguous_max), Excluded(overlap_max))
                | (Included(contiguous_max), Excluded(overlap_max))
                    if contiguous_max < overlap_max =>
                {
                    contiguous = &overlap.1
                }
                (Excluded(contiguous_max), Included(overlap_max))
                    if contiguous_max <= overlap_max =>
                {
                    contiguous = &overlap.1
                }
                _ => {}
            };
        }

        // If contiguous.max < q.max, we have a difference to append.
        match (&contiguous, range.end_bound()) {
            (Included(contiguous_max), Included(q_max)) if contiguous_max.borrow() < q_max => {
                acc.push((Excluded(contiguous_max.borrow()), Included(q_max)))
            }
            (Included(contiguous_max), Excluded(q_max)) if contiguous_max.borrow() < q_max => {
                acc.push((Excluded(contiguous_max.borrow()), Excluded(q_max)))
            }
            (Excluded(contiguous_max), Excluded(q_max)) if contiguous_max.borrow() < q_max => {
                acc.push((Included(contiguous_max.borrow()), Excluded(q_max)))
            }
            (Excluded(contiguous_max), Included(q_max)) if contiguous_max.borrow() <= q_max => {
                acc.push((Included(contiguous_max.borrow()), Included(q_max)))
            }
            _ => {}
        };

        acc
    }

    fn get_interval_overlaps_rec<'a, Q, R>(
        curr: &'a Option<Box<Node<K>>>,
        range: &R,
        acc: &mut Vec<&'a Range<K>>,
    ) where
        K: Ord + Borrow<Q>,
        R: RangeBounds<Q>,
        Q: Ord + ?Sized,
    {
        // If we reach None, stop recursing along this subtree.
        let node = match curr {
            None => return,
            Some(node) => node,
        };

        // See if subtree.max < q.min. If that is the case, there is no point
        // in visiting the rest of the subtree (we know that the rest of the intervals
        // will necessarily be smaller than `q`).
        // ~ Recall the ordering rules (as defined in `fn cmp` below). ~
        // -> If subtree.max is Unbounded, subtree.max < q.min is impossible.
        // -> If q.min is Unbounded, subtree.max < q.min is impossible.
        // -> If they are equal, we have 4 cases:
        //  * subtree.max: Included(x) / q.min: Included(x) -> =, we keep visiting the
        //    subtree
        //  * subtree.max: Included(x) / q.min: Excluded(x) -> <, condition satisfied
        //  * subtree.max: Excluded(x) / q.min: Included(x) -> <, condition satisfied
        //  * subtree.max: Excluded(x) / q.min: Excluded(x) -> <, condition satisfied
        let max_subtree = match &node.value {
            Included(x) => Some((x.borrow(), 2)),
            Excluded(x) => Some((x.borrow(), 1)),
            Unbounded => None,
        };
        let min_q = match range.start_bound() {
            Included(x) => Some((x, 2)),
            Excluded(x) => Some((x, 3)),
            Unbounded => None,
        };
        match (max_subtree, min_q) {
            (Some(max_subtree), Some(min_q)) if max_subtree < min_q => return,
            _ => {}
        };

        // Search left subtree.
        Self::get_interval_overlaps_rec(&node.left, range, acc);

        // Visit this node.
        // If node.min <= q.max AND node.max >= q.min, we have an intersection.
        // Let's start with the first inequality, node.min <= q.max.
        // -> If node.min is Unbounded, node.min <= q.max is a tautology.
        // -> If q.max is Unbounded, node.min <= q.max is a tautology.
        // -> If they are equal, we have 4 cases:
        //  * node.min: Included(x) / q.max: Included(x) -> =, we go to 2nd inequality
        //  * node.min: Included(x) / q.max: Excluded(x) -> >, 1st inequality not
        //    satisfied
        //  * node.min: Excluded(x) / q.max: Included(x) -> >, 1st inequality not
        //    satisfied
        //  * node.min: Excluded(x) / q.max: Excluded(x) -> >, 1st inequality not
        //    satisfied
        //
        // Notice that after we visit the node, we should visit the right subtree.
        // However, if node.min > q.max, we can skip right visiting the right
        // subtree. -> If node.min is Unbounded, node.min > q.max is impossible.
        // -> If q.max is Unbounded, node.min > q.max is impossible.
        //
        // It just so happens that we already do this check in the match to satisfy
        // the previous first condition. Hence, we decided to add an early return
        // in there, rather than repeat the logic afterwards.
        let min_node = match &node.key.0 {
            Included(x) => Some((x.borrow(), 2)),
            Excluded(x) => Some((x.borrow(), 3)),
            Unbounded => None,
        };
        let max_q = match range.end_bound() {
            Included(x) => Some((x, 2)),
            Excluded(x) => Some((x, 1)),
            Unbounded => None,
        };
        match (min_node, max_q) {
            // If the following condition is met, we do not have an intersection.
            // On top of that, we know that we can skip visiting the right subtree,
            // so we can return eagerly.
            (Some(min_node), Some(max_q)) if min_node > max_q => return,
            _ => {
                // Now we are at the second inequality, node.max >= q.min.
                // -> If node.max is Unbounded, node.max >= q.min is a tautology.
                // -> If q.min is Unbounded, node.max >= q.min is a tautology.
                // -> If they are equal, we have 4 cases:
                //  * node.max: Included(x) / q.min: Included(x) -> =, 2nd inequality satisfied
                //  * node.max: Included(x) / q.min: Excluded(x) -> <, 2nd inequality not
                //    satisfied
                //  * node.max: Excluded(x) / q.min: Included(x) -> <, 2nd inequality not
                //    satisfied
                //  * node.max: Excluded(x) / q.min: Excluded(x) -> <, 2nd inequality not
                //    satisfied
                let max_node = match &node.key.1 {
                    Included(x) => Some((x.borrow(), 2)),
                    Excluded(x) => Some((x.borrow(), 1)),
                    Unbounded => None,
                };

                match (max_node, min_q) {
                    (Some(max_node), Some(min_q)) if max_node < min_q => {}
                    _ => acc.push(&node.key),
                };
            }
        };

        // Search right subtree.
        Self::get_interval_overlaps_rec(&node.right, range, acc);
    }

    /// Returns the number of ranges stored in the interval tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// assert_eq!(tree.len(), 0);
    ///
    /// tree.insert((Included(5), Excluded(9)));
    /// tree.insert((Unbounded, Included(10)));
    ///
    /// assert_eq!(tree.len(), 2);
    /// ```
    pub const fn len(&self) -> usize {
        self.size
    }

    /// Returns `true` if the map contains no element.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// assert!(tree.is_empty());
    ///
    /// tree.insert((Included(5), Excluded(9)));
    ///
    /// assert!(!tree.is_empty());
    /// ```
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clear the interval tree, removing all values stored.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::ops::Bound::{Excluded, Included, Unbounded};
    ///
    /// use simulans::interval_tree::IntervalTree;
    ///
    /// let mut tree = IntervalTree::default();
    ///
    /// tree.insert((Included(5), Unbounded));
    /// tree.clear();
    ///
    /// assert!(tree.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.root = None;
        self.size = 0;
    }

    fn cmp(r1: &Range<K>, r2: &Range<K>) -> Ordering
    where
        K: Ord,
    {
        // Sorting by lower bound, then by upper bound.
        //   -> Unbounded is the smallest lower bound.
        //   -> Unbounded is the biggest upper bound.
        //   -> Included(x) < Excluded(x) for a lower bound.
        //   -> Included(x) > Excluded(x) for an upper bound.

        // Unpacking from a Bound is annoying, so let's map it to an Option<K>.
        // Let's use this transformation to encode the Included/Excluded rules at the
        // same time. Note that topological order is used during comparison, so
        // if r1 and r2 have the same `x`, only then will the 2nd element of the
        // tuple serve as a tie-breaker.
        let r1_min = match &r1.0 {
            Included(x) => Some((x, 1)),
            Excluded(x) => Some((x, 2)),
            Unbounded => None,
        };
        let r2_min = match &r2.0 {
            Included(x) => Some((x, 1)),
            Excluded(x) => Some((x, 2)),
            Unbounded => None,
        };

        match (r1_min, r2_min) {
            (None, None) => {} // Left-bounds are equal, we can't return yet.
            (None, Some(_)) => return Less,
            (Some(_), None) => return Greater,
            (Some(r1), Some(ref r2)) => {
                match r1.cmp(r2) {
                    Less => return Less,
                    Greater => return Greater,
                    Equal => {} // Left-bounds are equal, we can't return yet.
                };
            }
        };

        // Both left-bounds are equal, we have to
        // compare the right-bounds as a tie-breaker.
        Self::cmp_endbound(&r1.1, &r2.1)
    }

    fn cmp_endbound(e1: &Bound<K>, e2: &Bound<K>) -> Ordering
    where
        K: Ord,
    {
        // Based on the encoding idea used in `cmp`.
        // Note that we have inversed the 2nd value in the tuple,
        // as the Included/Excluded rules are flipped for the upper bound.
        let e1 = match e1 {
            Included(x) => Some((x, 2)),
            Excluded(x) => Some((x, 1)),
            Unbounded => None,
        };
        let e2 = match e2 {
            Included(x) => Some((x, 2)),
            Excluded(x) => Some((x, 1)),
            Unbounded => None,
        };

        match (e1, e2) {
            (None, None) => Equal,
            (None, Some(_)) => Greater,
            (Some(_), None) => Less,
            (Some(r1), Some(ref r2)) => r1.cmp(r2),
        }
    }
}

/// An in-order iterator through the interval tree.
pub struct IntervalTreeIter<'a, K> {
    to_visit: Vec<&'a Node<K>>,
    curr: &'a Option<Box<Node<K>>>,
}

impl<'a, K> Iterator for IntervalTreeIter<'a, K> {
    type Item = &'a Range<K>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_none() && self.to_visit.is_empty() {
            return None;
        }

        while self.curr.is_some() {
            self.to_visit.push(self.curr.as_ref().unwrap());
            self.curr = &self.curr.as_ref().unwrap().left;
        }

        let visited = self.to_visit.pop();
        self.curr = &visited.as_ref().unwrap().right;
        Some(&visited.unwrap().key)
    }
}
