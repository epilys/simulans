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

use serde_json::{from_str, json, to_string, Value};

use super::*;

#[test]
fn serialize_deserialize_identity() {
    let mut tree = IntervalTree::default();
    let serialized_empty_tree = to_string(&tree).unwrap();
    let deserialized_empty_tree = from_str(&serialized_empty_tree).unwrap();
    assert_eq!(tree, deserialized_empty_tree);

    tree.insert((Included(1), Excluded(3)));
    let serialized_tree = to_string(&tree).unwrap();
    let deserialized_tree = from_str(&serialized_tree).unwrap();
    assert_eq!(tree, deserialized_tree);
}

#[test]
fn serialize() {
    let mut tree = IntervalTree::default();
    let serialized_empty_tree = to_string(&tree).unwrap();
    let deserialized_empty_value: Value = from_str(&serialized_empty_tree).unwrap();
    let expected_empty_value = json!({
        "root": null,
        "size": 0,
    });
    assert_eq!(expected_empty_value, deserialized_empty_value);

    tree.insert((Included(2), Included(4)));
    tree.insert((Included(1), Excluded(3)));

    let serialized_tree = to_string(&tree).unwrap();
    let deserialized_tree: Value = from_str(&serialized_tree).unwrap();
    let expected_value = json!({
        "root": {
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
        },
        "size": 2,
    });
    assert_eq!(expected_value, deserialized_tree);
}

#[test]
fn deserialize() {
    let mut expected_tree = IntervalTree::default();
    let empty_value = json!({
        "root": null,
        "size": 0,
    });
    let serialized_empty_value = empty_value.to_string();
    let deserialized_empty_tree = from_str(&serialized_empty_value).unwrap();
    assert_eq!(expected_tree, deserialized_empty_tree);

    expected_tree.insert((Included(2), Included(4)));
    expected_tree.insert((Included(1), Excluded(3)));
    let value = json!({
        "root": {
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
        },
        "size": 2,
    });
    let serialized_value = value.to_string();
    let deserialized_tree = from_str(&serialized_value).unwrap();
    assert_eq!(expected_tree, deserialized_tree);
}

#[test]
fn it_inserts_root() {
    let mut tree = IntervalTree::default();
    assert!(tree.root.is_none());

    let key = (Included(1), Included(3));

    tree.insert(key);
    assert!(tree.root.is_some());
    assert_eq!(tree.root.as_ref().unwrap().key, key);
    assert_eq!(tree.root.as_ref().unwrap().value, key.1);
    assert!(tree.root.as_ref().unwrap().left.is_none());
    assert!(tree.root.as_ref().unwrap().right.is_none());
}

#[test]
fn creates_from_iterator() {
    let ranges = vec![0..5, 6..10, 10..15];
    let interval_tree: IntervalTree<_> = ranges.into_iter().collect();

    assert_eq!(interval_tree.len(), 3);
}

#[test]
fn creates_from_array() {
    let ranges = [0..5, 6..10, 10..15];
    let interval_tree = IntervalTree::from(ranges.clone());
    let other_interval_tree = ranges.into();

    assert_eq!(interval_tree, other_interval_tree);
    assert_eq!(interval_tree.len(), 3);
}

#[test]
fn it_inserts_left_right_node() {
    let mut tree = IntervalTree::default();

    let root_key = (Included(2), Included(3));
    let left_key = (Included(0), Included(1));
    let left_right_key = (Excluded(1), Unbounded);

    tree.insert(root_key);
    assert!(tree.root.is_some());
    assert!(tree.root.as_ref().unwrap().left.is_none());

    tree.insert(left_key);
    assert!(tree.root.as_ref().unwrap().right.is_none());
    assert!(tree.root.as_ref().unwrap().left.is_some());
    assert_eq!(
        tree.root.as_ref().unwrap().left.as_ref().unwrap().value,
        left_key.1
    );

    tree.insert(left_right_key);
    assert!(tree
        .root
        .as_ref()
        .unwrap()
        .left
        .as_ref()
        .unwrap()
        .right
        .is_some());
}

#[test]
fn it_updates_value() {
    let mut tree = IntervalTree::default();

    let root_key = (Included(2), Included(3));
    let left_key = (Included(0), Included(1));
    let left_left_key = (Included(-5), Excluded(10));
    let right_key = (Excluded(3), Unbounded);

    tree.insert(root_key);
    assert_eq!(tree.root.as_ref().unwrap().value, root_key.1);

    tree.insert(left_key);
    assert_eq!(tree.root.as_ref().unwrap().value, root_key.1);
    assert!(tree.root.as_ref().unwrap().left.is_some());
    assert_eq!(
        tree.root.as_ref().unwrap().left.as_ref().unwrap().value,
        left_key.1
    );

    tree.insert(left_left_key);
    assert_eq!(tree.root.as_ref().unwrap().value, left_left_key.1);
    assert_eq!(
        tree.root.as_ref().unwrap().left.as_ref().unwrap().value,
        left_left_key.1
    );
    assert!(tree
        .root
        .as_ref()
        .unwrap()
        .left
        .as_ref()
        .unwrap()
        .left
        .is_some());
    assert_eq!(
        tree.root
            .as_ref()
            .unwrap()
            .left
            .as_ref()
            .unwrap()
            .left
            .as_ref()
            .unwrap()
            .value,
        left_left_key.1
    );

    tree.insert(right_key);
    assert_eq!(tree.root.as_ref().unwrap().value, right_key.1);
    assert!(tree.root.as_ref().unwrap().right.is_some());
    assert_eq!(
        tree.root.as_ref().unwrap().left.as_ref().unwrap().value,
        left_left_key.1
    );
    assert_eq!(
        tree.root.as_ref().unwrap().right.as_ref().unwrap().value,
        right_key.1
    );
}

#[test]
fn cmp_works_as_expected() {
    let key0 = (Unbounded, Excluded(20));
    let key1 = (Included(1), Included(5));
    let key2 = (Included(1), Excluded(7));
    let key3 = (Included(1), Included(7));
    let key4 = (Excluded(5), Excluded(9));
    let key5 = (Included(7), Included(8));
    let key_str1 = (Included("abc"), Excluded("def"));
    let key_str2 = (Included("bbc"), Included("bde"));
    let key_str3: (_, Bound<&str>) = (Included("bbc"), Unbounded);

    assert_eq!(IntervalTree::cmp(&key1, &key1), Equal);
    assert_eq!(IntervalTree::cmp(&key1, &key2), Less);
    assert_eq!(IntervalTree::cmp(&key2, &key3), Less);
    assert_eq!(IntervalTree::cmp(&key0, &key1), Less);
    assert_eq!(IntervalTree::cmp(&key4, &key5), Less);
    assert_eq!(IntervalTree::cmp(&key_str1, &key_str2), Less);
    assert_eq!(IntervalTree::cmp(&key_str2, &key_str3), Less);
}

#[test]
fn overlap_works_as_expected() {
    let mut tree = IntervalTree::default();

    let root_key = (Included(2), Included(3));
    let left_key = (Included(0), Included(1));
    let left_left_key = (Included(-5), Excluded(10));
    let right_key = (Excluded(3), Unbounded);

    tree.insert(root_key);
    tree.insert(left_key);
    assert_eq!(tree.get_interval_overlaps(&root_key), vec![&root_key]);

    tree.insert(left_left_key);
    assert_eq!(
        tree.get_interval_overlaps(&(..)),
        vec![&left_left_key, &left_key, &root_key]
    );
    assert!(tree.get_interval_overlaps(&(100..)).is_empty());

    tree.insert(right_key);
    assert_eq!(
        tree.get_interval_overlaps(&root_key),
        vec![&left_left_key, &root_key]
    );
    assert_eq!(
        tree.get_interval_overlaps(&(..)),
        vec![&left_left_key, &left_key, &root_key, &right_key]
    );
    assert_eq!(tree.get_interval_overlaps(&(100..)), vec![&right_key]);
    assert_eq!(
        tree.get_interval_overlaps(&(3..10)),
        vec![&left_left_key, &root_key, &right_key]
    );
    assert_eq!(
        tree.get_interval_overlaps(&(Excluded(3), Excluded(10))),
        vec![&left_left_key, &right_key]
    );
    assert_eq!(
        tree.get_interval_overlaps(&(..2)),
        vec![&left_left_key, &left_key]
    );
    assert_eq!(
        tree.get_interval_overlaps(&(..=2)),
        vec![&left_left_key, &left_key, &root_key]
    );
    assert_eq!(
        tree.get_interval_overlaps(&(..=3)),
        vec![&left_left_key, &left_key, &root_key]
    );
}

#[test]
fn difference_and_overlaps_with_tuple_works_as_expected() {
    let mut tree = IntervalTree::default();

    let root_key = (Included((1, 2)), Excluded((1, 4)));
    let right_key = (5, 10)..=(5, 20);

    tree.insert(root_key);
    tree.insert(right_key);

    assert!(tree.get_interval_overlaps(&((2, 0)..=(2, 30))).is_empty());
    assert_eq!(
        tree.get_interval_overlaps(&((1, 3)..=(1, 5))),
        vec![&root_key]
    );
    assert_eq!(
        tree.get_interval_difference(&(Excluded((1, 1)), Included((1, 5)))),
        vec![
            (Excluded(&(1, 1)), Excluded(&(1, 2))),
            (Included(&(1, 4)), Included(&(1, 5)))
        ]
    );
}

#[test]
fn difference_works_as_expected() {
    let mut tree = IntervalTree::default();

    let key1 = 2..10;
    let key2 = 4..=6;
    let key3 = (Excluded(10), Excluded(20));
    let key4 = (Excluded(30), Included(35));
    let key5 = 30..=40;
    let key6 = 30..=35;
    let key7 = (Excluded(45), Unbounded);
    let key8 = (Included(60), Included(70));

    tree.insert(key1);
    tree.insert(key2);
    tree.insert(key3);
    tree.insert(key4);
    tree.insert(key5);
    tree.insert(key6);
    tree.insert(key7);
    tree.insert(key8);

    assert_eq!(
        tree.get_interval_difference(&(Excluded(0), Included(100))),
        vec![
            (Excluded(&0), Excluded(&2)),
            (Included(&10), Included(&10)),
            (Included(&20), Excluded(&30)),
            (Excluded(&40), Included(&45))
        ]
    );
    assert_eq!(
        tree.get_interval_difference(&(19..=40)),
        vec![(Included(&20), Excluded(&30))]
    );
    assert_eq!(
        tree.get_interval_difference(&(20..=40)),
        vec![(Included(&20), Excluded(&30))]
    );
    assert_eq!(
        tree.get_interval_difference(&(20..=45)),
        vec![
            (Included(&20), Excluded(&30)),
            (Excluded(&40), Included(&45))
        ]
    );
    assert_eq!(
        tree.get_interval_difference(&(20..45)),
        vec![
            (Included(&20), Excluded(&30)),
            (Excluded(&40), Excluded(&45))
        ]
    );
    assert_eq!(
        tree.get_interval_difference(&(2..=10)),
        vec![(Included(&10), Included(&10))]
    );
}

#[test]
fn consecutive_excluded_non_contiguous_difference_works_as_expected() {
    let mut tree = IntervalTree::default();

    let key1 = (Included(10), Excluded(20));
    let key2 = (Excluded(30), Excluded(40));

    tree.insert(key1);
    tree.insert(key2);

    assert_eq!(
        tree.get_interval_difference(&(0..=40)),
        vec![
            (Included(&0), Excluded(&10)),
            (Included(&20), Included(&30)),
            (Included(&40), Included(&40))
        ]
    );
}

#[test]
fn get_interval_difference_str_works_as_expected() {
    let mut tree: IntervalTree<&str> = IntervalTree::default();

    let key1 = (Included("a"), Excluded("h"));
    let key2 = (Excluded("M"), Excluded("O"));

    tree.insert(key1);
    tree.insert(key2);

    assert!(tree.get_interval_difference(&("a".."h")).is_empty());
    assert_eq!(
        tree.get_interval_difference(&("M"..="P")),
        vec![
            (Included(&"M"), Included(&"M")),
            (Included(&"O"), Included(&"P"))
        ]
    );

    let not_covered_range = "h".."k";
    assert_eq!(
        tree.get_interval_difference(&not_covered_range),
        vec![(
            not_covered_range.start_bound(),
            not_covered_range.end_bound()
        )]
    );
}

#[test]
fn contains_point_works_as_expected() {
    let mut tree = IntervalTree::default();

    let key1 = (Included(10), Excluded(20));
    let key2 = (Excluded(30), Excluded(40));
    let key3 = 40..;

    tree.insert(key1);
    tree.insert(key2);
    tree.insert(key3);

    assert!(tree.contains_point(&10));
    assert!(!tree.contains_point(&20));
    assert!(tree.contains_point(&40));
    assert!(tree.contains_point(&100));
}

#[test]
fn contains_string_point_works_as_expected() {
    let mut tree = IntervalTree::default();

    let key1 = String::from("a")..String::from("h");
    let key2 = (Excluded(String::from("M")), Excluded(String::from("O")));

    tree.insert(key1);
    tree.insert(key2);

    assert!(tree.contains_point("b"));
    assert!(!tree.contains_point("n"));
    assert!(tree.contains_point(&String::from("N")));
    assert!(tree.contains_point("g"));
}

#[test]
fn contains_str_point_works_as_expected() {
    let mut tree: IntervalTree<&str> = IntervalTree::default();

    let key1 = "a".."h";
    let key2 = (Excluded("M"), Excluded("O"));

    tree.insert(key1);
    tree.insert(key2);

    assert!(tree.contains_point("b"));
    assert!(!tree.contains_point("n"));
    assert!(tree.contains_point(&"N"));
    assert!(tree.contains_point("g"));
}

#[test]
fn contains_works_as_expected() {
    let mut tree = IntervalTree::default();

    let key1 = (Included(10), Excluded(20));
    let key2 = (Excluded(30), Excluded(40));
    let key3 = 40..;

    tree.insert(key1);
    tree.insert(key2);
    tree.insert(key3);

    assert!(tree.contains_interval(&key1));
    assert!(!tree.contains_interval(&(Included(&10), Included(&20))));
    assert!(!tree.contains_interval(&(..=0)));
    assert!(tree.contains_interval(&(Included(35), Included(37))));
}

#[test]
fn contains_str_works_as_expected() {
    let mut tree: IntervalTree<&str> = IntervalTree::default();

    let key1 = "a".."h";
    let key2 = (Excluded("M"), Excluded("O"));

    tree.insert(key1.clone());
    tree.insert(key2);

    assert!(tree.contains_interval(&("a".."h")));
    assert!(tree.contains_interval(&("N"..="N")));
    assert!(tree.contains_interval::<&str, _>(&key1));
    assert!(!tree.contains_interval(&("N"..="O")));
}

#[test]
fn iter_works_as_expected() {
    let mut tree = IntervalTree::default();

    assert_eq!(tree.iter().next(), None);

    let key1 = (Included(10), Excluded(20));
    let key2 = (Included(40), Unbounded);
    let key3 = (Excluded(30), Excluded(40));
    let key4 = (Unbounded, Included(50));
    let key5 = (Excluded(-10), Included(-5));
    let key6 = (Included(-10), Included(-4));

    tree.insert(key1);
    tree.insert(key2);
    tree.insert(key3);
    tree.insert(key4);
    tree.insert(key5);
    tree.insert(key6);

    let inorder = [&key4, &key6, &key5, &key1, &key3, &key2];
    for (idx, interval) in tree.iter().enumerate() {
        assert_eq!(interval, inorder[idx]);
    }

    assert_eq!(tree.iter().count(), inorder.len());
}

#[test]
fn len_and_is_empty_works_as_expected() {
    let mut tree = IntervalTree::default();

    assert_eq!(tree.len(), 0);
    assert!(tree.is_empty());

    let key1 = (Included(16), Unbounded);
    let key2 = (Included(8), Excluded(9));

    tree.insert(key1);

    assert_eq!(tree.len(), 1);
    assert!(!tree.is_empty());

    tree.insert(key2);

    assert_eq!(tree.len(), 2);
    assert!(!tree.is_empty());

    tree.clear();

    assert_eq!(tree.len(), 0);
    assert!(tree.is_empty());
}

#[test]
fn clear_works_as_expected() {
    let mut tree = IntervalTree::default();

    tree.clear();

    let key1 = (Included(16), Unbounded);
    let key2 = (Included(8), Excluded(9));

    tree.insert(key1);
    tree.insert(key2);

    assert_eq!(tree.len(), 2);

    tree.clear();

    assert!(tree.is_empty());
    assert_eq!(tree.root, None);
}
