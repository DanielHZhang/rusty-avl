mod tree;

use tree::tree::AvlTree;

fn main() {
  let mut tree = AvlTree::new();
  tree.insert("wow", "hello");
  let node = tree.get_mut(&"wow");
  match node {
    None => println!("No node found"),
    Some(node) => {
      println!("Node with key {} found", node.key);
      let key = node.key;
      tree.delete(&key);
    }
  }
}
