use crate::node::{Node, NodeOption, Tree};
use std::{cmp::Ordering, fmt::Debug, usize};

#[derive(Debug)]
pub struct BinarySearchTree<K: Ord, V: PartialEq> {
  root: Tree<K, V>,
  size: u32,
  avl: bool,
}

impl<K: Ord, V: PartialEq> BinarySearchTree<K, V> {
  pub fn new() -> Self {
    Self {
      root: None,
      size: 0,
      avl: false,
    }
  }

  pub fn new_root(root: Node<K, V>) -> Self {
    Self {
      root: Some(Box::new(root)),
      size: 1,
      avl: false,
    }
  }

  pub fn get(&mut self, key: K) -> Option<&Node<K, V>> {
    match self.get_mut(key) {
      None => None,
      Some(node) => Some(&*node),
    }
  }

  pub fn get_mut(&mut self, key: K) -> Option<&mut Node<K, V>> {
    match self.root.as_mut() {
      None => None,
      Some(node) => {
        let mut cur = node;
        loop {
          let target = match key.cmp(&cur.key) {
            Ordering::Less => &mut cur.left,
            Ordering::Greater => &mut cur.right,
            Ordering::Equal => {
              return Some(cur.as_mut());
            }
          };
          if target.is_none() {
            return None;
          }
          cur = target.as_mut().unwrap();
        }
      }
    }
  }

  pub fn contains(&mut self, key: K) -> bool {
    self.get(key).is_some()
  }

  pub fn smallest(&mut self) -> Option<&mut Node<K, V>> {
    match self.root {
      None => None,
      Some(ref mut root) => {
        let mut cur = root;
        while let Some(ref mut node) = cur.left {
          cur = node;
        }
        Some(cur.as_mut())
      }
    }
  }

  pub fn largest(&mut self) -> Option<&mut Node<K, V>> {
    match self.root {
      None => None,
      Some(ref mut root) => {
        let mut cur = root;
        while let Some(ref mut node) = cur.right {
          cur = node;
        }
        Some(cur.as_mut())
      }
    }
  }

  pub fn successor(&mut self, key: K) -> Option<&Node<K, V>> {
    match self.root {
      None => None,
      Some(ref root) => {
        let wow = root;
        let mut visited: Vec<&Box<Node<K, V>>> = Vec::from([wow]);
        loop {
          let cur = visited.last();
          match cur {
            None => break,
            Some(node) => match key.cmp(&node.key) {
              Ordering::Less => match node.left.as_ref() {
                None => break,
                Some(left) => visited.push(left),
              },
              Ordering::Greater => match node.right.as_ref() {
                None => break,
                Some(right) => visited.push(right),
              },
              Ordering::Equal => {
                match node.right.as_deref() {
                  None => {
                    // Trace backwards through visited parents
                    for v in visited.iter().rev() {
                      if v.key > key {
                        return Some(*v);
                      }
                    }
                    return None;
                  }
                  Some(right) => {
                    // Find smallest node in right subtree
                    let a = right.smallest();
                    return a;
                  }
                }
              }
            },
          }
        }
        None
      }
    }

    // match self.root {
    //   None => None,
    //   Some(ref mut root) => {
    //     if key == root.key {
    //       match &mut root.right {
    //         None => None,
    //         Some(node) => {
    //           let a = node.smallest();
    //           a
    //         }
    //       }
    //     } else {
    //       // Minimum height of a BST with n nodes is floor(log2(n))
    //       // let min_height = f64::from(self.size).log2().floor();
    //       // let mut visited: Vec<&mut Node<K, V>> = Vec::with_capacity(min_height as usize);
    //       // visited.push(root);
    //       // let mut cur = root;
    //       let mut visited: Vec<&mut Node<K, V>> = Vec::from([root.as_mut()]);
    //       loop {
    //         let last = visited.pop();

    //         let a = last.unwrap();
    //         let b = a.left.as_mut();
    //         visited.push(a);

    //         let c = b;

    //         // match key.cmp(&last.key) {
    //         //   Ordering::Less => {
    //         //     let w = *last;
    //         //     let a = &mut last.left;
    //         //     let b = a.as_deref_mut().unwrap();
    //         //     visited.push(b);
    //         //   }
    //         //   Ordering::Greater => {
    //         //     //
    //         //   }
    //         //   Ordering::Equal => {
    //         //     //
    //         //   }
    //         // }
    //       }
    //       None
    //     }
    //   }
    // }

    // if key < last.key {
    //   let b = last.left.as_mut();
    //   visited.push(last);
    // }
    // if key < cur.key {
    //   let a = cur;
    // }
    // let target = match key.cmp(&cur.key) {
    //   Ordering::Less => &mut cur.left,
    //   Ordering::Greater => &mut cur.right,
    //   Ordering::Equal => match &mut cur.right {
    //     None => break, // Need to backtrace from current node
    //     Some(node) => {
    //       // Get smallest node in right subtree
    //       let a = node.smallest();
    //       return a;
    //     }
    //   },
    // };
    // if target.is_none() {
    //   return None; // Node with key not found in BST
    // }
    // let b = cur;
    // visited.push(cur);
  }

  pub fn predecessor(&mut self, key: K) -> Option<&mut Node<K, V>> {
    None
  }

  pub fn insert(&mut self, key: K, value: V) -> bool {
    match self.root.as_mut() {
      None => {
        self.root = Some(Box::new(Node::new(key, value)));
        self.size += 1;
        return true;
      }
      Some(node) => {
        let mut cur = node;
        loop {
          let target = match key.cmp(&cur.key) {
            Ordering::Less => &mut cur.left,
            Ordering::Greater => &mut cur.right,
            Ordering::Equal => {
              if value == cur.value {
                cur.count += 1;
                return true;
              }
              return false;
            }
          };
          if target.is_none() {
            *target = Some(Box::new(Node::new(key, value)));
            self.size += 1;
            return true;
          }
          cur = target.as_mut().unwrap();
        }
      }
    }
  }

  pub fn delete(&mut self, key: K) -> bool {
    let mut cur = &mut self.root;
    while let Some(ref mut node) = cur {
      match key.cmp(&node.key) {
        Ordering::Less => cur = &mut cur.as_mut().unwrap().left,
        Ordering::Greater => cur = &mut cur.as_mut().unwrap().right,
        Ordering::Equal => {
          if node.count > 1 {
            node.count -= 1;
          } else {
            match (node.left.as_mut(), node.right.as_mut()) {
              (None, None) => *cur = None,
              (Some(_), None) => *cur = node.left.take(),
              (None, Some(_)) => *cur = node.right.take(),
              (Some(_), Some(_)) => *cur = node.right.extract_min(),
            }
          }
          self.size -= 1;
          return true;
        }
      }
    }
    false
  }

  pub fn height() {}

  pub fn balance() {}

  fn right_rotation() {}

  fn left_rotation() {}

  pub fn iter_preorder() {}

  pub fn iter_inorder() {}

  pub fn iter_postorder() {}

  // pub fn into_vec(&self) -> Vec<&Node<K, V>> {
  //   let mut new_vec = Vec::with_capacity(self.size);
  //   new_vec
  // }
}

#[cfg(test)]
mod test {
  use super::BinarySearchTree;
  use crate::node::Node;

  #[test]
  fn init() {
    // fn new (empty root)
    let mut bst = BinarySearchTree::new();
    assert!(bst.root.is_none());
    bst.insert(2, 10);

    // fn new_with_root (provided root)
    let root = Node::new("key", "value");
    let bst = BinarySearchTree::new_root(root);
    assert!(bst.root.is_some());
    let got_root = bst.root.unwrap();
    assert_eq!(got_root.key, "key");
    assert_eq!(got_root.value, "value");
  }

  #[test]
  fn get() {
    let mut bst = BinarySearchTree::new_root(Node::new(2, 2));

    // fn get
    let mut found = bst.get(0);
    assert!(found.is_none());
    found = bst.get(2);
    assert!(found.is_some());
    let mut node = found.unwrap();
    assert_eq!(node.key, 2);
    assert_eq!(node.value, 2);

    // fn get_mut
    let found_mut = bst.get_mut(2);
    assert!(found_mut.is_some());
    let mut node_mut = found_mut.unwrap();
    node_mut.key = 5;
    node_mut.value = 10;
    found = bst.get(5);
    assert!(found.is_some());
    node = found.unwrap();
    assert_eq!(node.key, 5);
    assert_eq!(node.value, 10);

    // fn contains
    assert!(bst.contains(5));
    assert!(!bst.contains(10));
  }

  #[test]
  fn insertion() {
    let mut bst = BinarySearchTree::new();
    assert!(bst.insert(2, 2));
    assert!(bst.insert(3, 3));
    assert!(bst.insert(2, 2));
    assert!(!bst.insert(2, 5));
  }

  #[test]
  fn removal() {
    let mut bst = BinarySearchTree::new_root(Node::new(8, "eight"));
    bst.insert(2, "two");
    bst.insert(5, "five");
    bst.insert(1, "one");
    bst.insert(10, "ten");
    bst.insert(9, "nine");
    assert!(bst.delete(2));
    assert!(!bst.delete(2));
  }

  #[test]
  fn smallest() {
    let mut bst = BinarySearchTree::new_root(Node::new(5, "five"));
    bst.insert(2, "two");
    bst.insert(1, "one");
    let small = bst.smallest();
    assert!(small.is_some());
    let node = small.unwrap();
    assert_eq!(node.key, 1);
    assert!(bst.get(5).is_some());
    assert!(bst.get(2).is_some());
    assert!(bst.get(1).is_some());
  }
}
