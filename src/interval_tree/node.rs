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

//! Implementation of interval tree nodes, see [`Node`].

use std::{
    fmt,
    ops::{Bound, Bound::*},
};

use serde_derive::{Deserialize, Serialize};

pub type Range<K> = (Bound<K>, Bound<K>);

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq)]
pub struct Node<K> {
    pub key: Range<K>,
    pub value: Bound<K>, // Max end-point.
    pub left: Option<Box<Node<K>>>,
    pub right: Option<Box<Node<K>>>,
}

impl<K> fmt::Display for Node<K>
where
    K: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let start = match self.key.0 {
            Included(ref x) => format!("[{}", x),
            Excluded(ref x) => format!("]{}", x),
            Unbounded => String::from("]-∞"),
        };
        let end = match self.key.1 {
            Included(ref x) => format!("{}]", x),
            Excluded(ref x) => format!("{}[", x),
            Unbounded => "∞[".to_string(),
        };
        let value = match self.value {
            Included(ref x) => format!("{}]", x),
            Excluded(ref x) => format!("{}[", x),
            Unbounded => String::from("∞"),
        };

        if self.left.is_none() && self.right.is_none() {
            write!(f, " {{ {},{} ({}) }} ", start, end, value)
        } else if self.left.is_none() {
            write!(
                f,
                " {{ {},{} ({}) right:{}}} ",
                start,
                end,
                value,
                self.right.as_ref().unwrap()
            )
        } else if self.right.is_none() {
            write!(
                f,
                " {{ {},{} ({}) left:{}}} ",
                start,
                end,
                value,
                self.left.as_ref().unwrap()
            )
        } else {
            write!(
                f,
                " {{ {},{} ({}) left:{}right:{}}} ",
                start,
                end,
                value,
                self.left.as_ref().unwrap(),
                self.right.as_ref().unwrap()
            )
        }
    }
}

impl<K> Node<K> {
    pub fn new(range: Range<K>) -> Self
    where
        K: Clone,
    {
        let max = range.1.clone();

        Self {
            key: range,
            value: max,
            left: None,
            right: None,
        }
    }

    // pub fn is_leaf(&self) -> bool {
    //     self.left.is_none() && self.right.is_none()
    // }

    pub fn maybe_update_value(&mut self, inserted_max: &Bound<K>)
    where
        K: PartialOrd + Clone,
    {
        let self_max_q = match &self.value {
            Included(x) => Some((x, 2)),
            Excluded(x) => Some((x, 1)),
            Unbounded => None,
        };
        let inserted_max_q = match inserted_max {
            Included(x) => Some((x, 2)),
            Excluded(x) => Some((x, 1)),
            Unbounded => None,
        };
        match (self_max_q, inserted_max_q) {
            (None, _) => {}
            (_, None) => self.value = Unbounded,
            (Some(self_max_q), Some(inserted_max_q)) => {
                if self_max_q < inserted_max_q {
                    self.value = inserted_max.clone();
                }
            }
        };
    }
}

#[cfg(test)]
mod tests {
    use serde_json::{from_str, json, to_string, Value};

    use super::*;

    #[test]
    fn serialize_deserialize_identity() {
        let leaf = Node::new((Included(1), Excluded(3)));
        let serialized_leaf = to_string(&leaf).unwrap();
        let deserialized_leaf = from_str(&serialized_leaf).unwrap();
        assert_eq!(leaf, deserialized_leaf);

        let mut node = Node::new((Included(2), Included(4)));
        node.left = Some(Box::new(leaf));
        let serialized_node = to_string(&node).unwrap();
        let deserialized_node = from_str(&serialized_node).unwrap();
        assert_eq!(node, deserialized_node);
    }

    #[test]
    fn serialize() {
        let leaf = Node::new((Included(1), Excluded(3)));
        let serialized_leaf = to_string(&leaf).unwrap();
        let deserialized_value: Value = from_str(&serialized_leaf).unwrap();
        let expected_value = json!({
            "key": [
            {"Included": 1},
            {"Excluded": 3},
            ],
            "left": null,
            "right": null,
            "value": {"Excluded": 3}
        });
        assert_eq!(expected_value, deserialized_value);

        let mut node = Node::new((Included(2), Included(4)));
        node.left = Some(Box::new(leaf));
        let serialized_node = to_string(&node).unwrap();
        let deserialized_value: Value = from_str(&serialized_node).unwrap();
        let expected_value = json!({
            "key": [
            {"Included": 2},
            {"Included": 4},
            ],
            "left": {
            "key": [
                {"Included": 1},
                {"Excluded": 3},
            ],
            "left": null,
            "right": null,
            "value": {"Excluded": 3},
            },
            "right": null,
            "value": {"Included": 4},
        });
        assert_eq!(expected_value, deserialized_value);
    }

    #[test]
    fn deserialize() {
        let expected_leaf = Node::new((Included(1), Excluded(3)));
        let value = json!({
            "key": [
            {"Included": 1},
            {"Excluded": 3},
            ],
            "left": null,
            "right": null,
            "value": {"Excluded": 3},
        });
        let serialized_value = value.to_string();
        let deserialized_leaf = from_str(&serialized_value).unwrap();
        assert_eq!(expected_leaf, deserialized_leaf);

        let mut expected_node = Node::new((Included(2), Included(4)));
        expected_node.left = Some(Box::new(expected_leaf));
        let value = json!({
            "key": [
            {"Included": 2},
            {"Included": 4},
            ],
            "left": {
            "key": [
                {"Included": 1},
                {"Excluded": 3},
            ],
            "left": null,
            "right": null,
            "value": {"Excluded": 3},
            },
            "right": null,
            "value": {"Included": 4},
        });
        let serialized_value = value.to_string();
        let deserialized_node = from_str(&serialized_value).unwrap();
        assert_eq!(expected_node, deserialized_node);
    }
}
