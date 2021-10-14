# rusty-avl

A Rust crate for creating AVL trees. Each tree can store generic key-value pairs. All tree operations are implemented iteratively.

## Usage

```rust
let avl = AvlTree::<i32, i32>::default(); // Default
let avl = AvlTree::new(Node::new(1, 1)); // With root node
let mut avl = Vec::from([(1, 1), (2, 2), (3, 3)])
	.into_iter()
	.collect::<AvlTree<_, _>>(); // From iterator

let insert_result = avl.insert(4, 4);
assert!(insert_result.is_none());

let remove_result = avl.remove(&2);
assert_eq!(remove_result, Some(2));

let node = avl.get_mut(&1).unwrap();
assert_eq!(node.key(), &1);

let old = node.set_value(123);
assert_eq!(old, 1);
assert_eq!(node.value(), &123);
```

### Methods

- new
- get
- get_mut
- insert
- remove
- contains
- min
- min_mut
- max
- max_mut
- successor
- predecessor
- is_empty
- clear
- len
- height
- iter_preorder
- iter_inorder
- iter_postorder
