mod tree;

use tree::tree::BinarySearchTree;

fn main() {
  let mut bst = BinarySearchTree::new();
  bst.insert("wow", "hello");
  let node = bst.get_mut(&"wow");
  match node {
    None => println!("No node found"),
    Some(node) => {
      println!("Node with key {} found", node.key);
      let key = node.key;
      bst.delete(&key);
    }
  }
}
