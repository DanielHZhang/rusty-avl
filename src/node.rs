use std::cmp::Ordering;
use std::fmt::Debug;

#[derive(Debug)]
pub struct Node<K: Ord, V: PartialEq> {
	pub key: K,
	pub value: V,
	pub count: u32,
	left: Tree<K, V>,
	right: Tree<K, V>,
}

#[derive(Debug)]
pub struct Tree<K: Ord, V: PartialEq>(pub Option<Box<Node<K, V>>>);

impl<K: Ord, V: PartialEq> Node<K, V> {
	pub fn new(key: K, value: V) -> Self {
		Self {
			key,
			value,
			count: 0,
			left: Tree(None),
			right: Tree(None),
		}
	}

	pub fn is_leaf(&self) -> bool {
		self.left.0.is_none() && self.right.0.is_none()
	}
}

impl<K: Ord, V: PartialEq> Tree<K, V> {
	pub fn get(&self, key: K) -> Option<&Node<K, V>> {
		let mut current = self;

		while let Some(node) = &current.0 {
			match node.key.cmp(&key) {
				Ordering::Less => current = &node.right,
				Ordering::Greater => current = &node.left,
				Ordering::Equal => break,
			}
		}

		current.0.as_deref()

		// if key < self.key {
		// 	let w = self.left.as_deref();
		// 	match w {
		// 		None => None,
		// 		Some(node) => node.get(key),
		// 	}
		// } else if key > self.key {
		// 	let w = self.right.as_deref();
		// 	match w {
		// 		None => None,
		// 		Some(node) => node.get(key),
		// 	}
		// } else {
		// 	Some(self)
		// }
	}

	// pub fn get_mut(&mut self, key: K) -> Option<&mut Self> {
	// 	if key < self.key {
	// 		match self.left.as_deref_mut() {
	// 			None => None,
	// 			Some(node) => node.get_mut(key),
	// 		}
	// 	} else if key > self.key {
	// 		match self.right.as_deref_mut() {
	// 			None => None,
	// 			Some(node) => node.get_mut(key),
	// 		}
	// 	} else {
	// 		Some(self)
	// 	}
	// }

	// pub fn insert(&mut self, key: K, value: V) -> Option<&Self> {
	// 	if key < self.key {
	// 		match self.left.take() {
	// 			None => {
	// 				self.left = Some(Box::new(Node::new(key, value)));
	// 				self.left.as_deref()
	// 			}
	// 			Some(node) => {
	// 				self.left = Some(node);
	// 				self.left.as_deref_mut().unwrap().insert(key, value)
	// 			}
	// 		}
	// 	} else if key > self.key {
	// 		match self.right.take() {
	// 			None => {
	// 				self.right = Some(Box::new(Node::new(key, value)));
	// 				self.right.as_deref()
	// 			}
	// 			Some(node) => {
	// 				self.right = Some(node);
	// 				self.right.as_deref_mut().unwrap().insert(key, value)
	// 			}
	// 		}
	// 	} else {
	// 		if value == self.value {
	// 			self.count += 1;
	// 			Some(self)
	// 		} else {
	// 			None
	// 		}
	// 	}
	// }

	// pub fn delete(&mut self, key: K) -> Option<Self> {
	// 	if key < self.key {
	// 		match self.left.as_deref() {
	// 			None => None,
	// 			Some(node) => {}
	// 		}
	// 	} else if key > self.key {
	// 	} else {
	// 		if self.count > 1 {
	// 			self.count -= 1;
	// 			None
	// 		}
	// 	}
	// }
}
