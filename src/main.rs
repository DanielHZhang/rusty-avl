mod bst;
mod node;

use bst::BinarySearchTree;

fn main() {
	let mut bst = BinarySearchTree::new();
	bst.insert(2, "hello");
	let node = bst.get(2);
	match node {
		None => println!("No node found"),
		Some(node) => {
			println!("Node with key {} found", node.key);
		}
	}
}
