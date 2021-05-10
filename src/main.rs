mod bst;

use bst::tree::BinarySearchTree;

fn main() {
  let mut bst = BinarySearchTree::new();
  bst.insert("wow", "hello");
  let node = bst.get_mut(&"wow");
  match node {
    None => println!("No node found"),
    Some(node) => {
      println!("Node with key {} found", node.key);
      let key = node.key;
      bst.delete(key);
    }
  }
  let missing = bst.get(&"lol");
  // if missing.is_none() && bst.contains(&"lol") {
  //   let small = bst.smallest();
  //   let large = bst.largest();
  //   match (small, large) {
  //     (Some(s), Some(l)) => {
  //       if s.value == l.value {
  //         println!("Smallest equals largest!");
  //       }
  //     }
  //     _ => (),
  //   }
  // }
}
