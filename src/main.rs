use std::fmt::format;
use std::io;

mod bst;
mod node;

use bst::BinarySearchTree;

fn main() {
	let mut bst = BinarySearchTree::new(2, "hello");
	// bst.insert(2, "hello");
	let node = bst.get(2);
	match node {
		None => println!("No node found"),
		Some(node) => {
			println!("Node with key {} found", node.key);
		}
	}
}
