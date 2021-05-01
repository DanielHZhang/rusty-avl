use crate::node::{Node, Tree};
use std::fmt::Debug;

#[derive(Debug)]
pub struct BinarySearchTree<K: Ord, V: PartialEq> {
	root: Tree<K, V>,
}

impl<K: Ord, V: PartialEq> BinarySearchTree<K, V> {
	pub fn empty() -> Self {
		Self { root: Tree(None) }
	}

	pub fn new(key: K, value: V) -> Self {
		Self {
			root: Tree(Some(Box::new(Node::new(key, value)))),
		}
	}

	pub fn get(&self, key: K) -> Option<&Node<K, V>> {
		self.root.get(key)
		// match self.root.as_deref() {
		// 	None => None,
		// 	Some(node) => node.get(key),
		// }
	}

	// pub fn get_mut(&mut self, key: K) -> Option<&mut Node<K, V>> {
	// 	match self.root.as_deref_mut() {
	// 		None => None,
	// 		Some(node) => node.get_mut(key),
	// 	}
	// }

	pub fn insert(&mut self, key: K, value: V) -> Option<&Node<K, V>> {
		match self.root.take() {
			None => {
				self.root = Some(Box::new(Node::new(key, value)));
				self.root.as_deref()
			}
			Some(node) => {
				self.root = Some(node);
				self.root.as_deref_mut().unwrap().insert(key, value)
			}
		}
	}

	pub fn delete(&mut self, key: K) {}

	// pub fn delete(&mut self, key: K, value: V) -> Option<Node<K, V>> {
	// 	match self.root.take() {
	// 		None => None,
	// 		Some(node) => {}
	// 	}
	// }
}

#[cfg(test)]
mod test {
	use super::BinarySearchTree;
	use crate::node::Node;

	// #[test]
	// fn init() {
	// 	let mut bst = BinarySearchTree::empty();
	// 	assert!(bst.root.is_none());
	// 	bst.insert(2, 10);

	// 	let bst = BinarySearchTree::new("key", "test");
	// 	assert!(bst.root.is_some());
	// 	let root = bst.root.unwrap();
	// 	assert_eq!(root.key, "key");
	// 	assert_eq!(root.value, "test");
	// }

	// #[test]
	// fn insertion() {
	// 	let mut bst = BinarySearchTree::empty();
	// 	let i1 = bst.insert(2, 2).unwrap();
	// 	assert_eq!(i1.key, 2);
	// 	assert_eq!(i1.value, 2);
	// }
}
