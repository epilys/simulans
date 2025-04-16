# Interval Tree module

## Historical note

This was vendored in from the <https://github.com/jonathanGB/Unbounded-Interval-Tree>
repository, commit
[`51082c68e0d4fe6fe4cdf09809cad106fc85abf2`](https://github.com/jonathanGB/Unbounded-Interval-Tree/commit/51082c68e0d4fe6fe4cdf09809cad106fc85abf2).

The original crate metadata including author credits and license were:

```toml
name = "unbounded-interval-tree"
version = "1.1.2"
authors = ["Jonathan Guillotte-Blouin <jonathan.guillotte.blouin@gmail.com>"]
edition = "2021"
license = "MIT"
description = "An interval tree working with inclusive/exclusive bounds, as well as unbounded intervals. Provides helpers to fetch overlapping intervals, and difference of intervals."
readme = "README.md"

repository = "https://github.com/jonathanGB/unbounded-interval-tree"
keywords = ["interval", "tree", "bound", "exclusive", "difference"]
categories = ["algorithms", "data-structures"]
```

The original `README.md` follows but note its instructions reflect the original crate, and not this vendored module.

### Original `README.md` contents

#### Unbounded Interval Tree

A Rust implementation of an interval tree, based on the one described by Cormen et al., (2009), Introduction to Algorithms (3rd ed., Section 14.3: Interval trees, pp. 348–354). An interval tree is useful to query efficiently a database of intervals. This implementation is generic in that it works with intervals of values implementing `Ord+Clone` traits. The bounds can be inclusive, exclusive, or unbounded. Here are some examples of valid intervals:

* [5, 9] <- inclusive/inclusive integers
* [-2.3, 18.81) <- inclusive/exclusive floats
* ("abc", "hi"] <- exclusive/inclusive strings
* (-inf, November 7 2019] <- unbounded/inclusive dates
* [(1, 5), (2, 9)] <- inclusive/inclusive tuples of integers

#### How To Use

I would suggest to look at the examples part of the documentation (as they are tested by the Rust ecosystem), but here's a current example.

```rust
use unbounded_interval_tree::IntervalTree;
use std::ops::Bound::{Included, Excluded, Unbounded};

// Default interval tree.
let mut tree = IntervalTree::default();

// Ranges are defined as a 2-ple of Bounds.
let interval1 = (Included(5), Excluded(9));
let interval2 = (Unbounded, Included(-2));
let interval3 = (Included(30), Included(30));

// Add intervals to the tree.
tree.insert(interval1);
tree.insert(interval2);
tree.insert(interval3);

// Iterate through the intervals inorder.
for (start, end) in tree.iter() {
  println!("Start: {:?}\tEnd: {:?}", start, end);
}

// Get overlapping intervals.
let overlaps = tree.get_interval_overlaps(&(0..30));

// Get the difference between the database
// of intervals and the query interval.
let diff = tree.get_interval_difference(&(0..=30));
```

##### Roadmap

*What's next...*

* Allow to remove intervals from the tree (started in the `delete` branch).
  * I have added a `remove_random_leaf` method to the API. Removing leaves is significantly simpler with this data structure, hence I started by tackling this problem.
* Keep the tree balanced, by rotating during insertions/deletions
* Assert that the start bound of an interval is smaller or equal to the end bound of the same interval.
