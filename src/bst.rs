use crate::node::{Node, NodeOption, Tree};
use std::{cmp::Ordering, fmt::Debug};

#[derive(Debug)]
pub struct BinarySearchTree<K: Ord, V: PartialEq> {
  root: Tree<K, V>,
  size: usize,
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

  pub fn new_with_root(root: Node<K, V>) -> Self {
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
          return true;
        }
      }
    }
    false
  }

  pub fn iter_inorder() {}

  pub fn into_vec(&self) -> Vec<&Node<K, V>> {
    let mut new_vec = Vec::with_capacity(self.size);
    new_vec
  }
}

#[cfg(test)]
mod test {
  use super::BinarySearchTree;
  use crate::node::Node;

  #[test]
  fn init() {
    let mut bst = BinarySearchTree::new();
    assert!(bst.root.is_none());
    bst.insert(2, 10);
    let root = Node::new("key", "value");
    let bst = BinarySearchTree::new_with_root(root);
    assert!(bst.root.is_some());
    let got_root = bst.root.unwrap();
    assert_eq!(got_root.key, "key");
    assert_eq!(got_root.value, "test");
  }

  #[test]
  fn get() {
    let root = Node::new(2, 2);
    let mut bst = BinarySearchTree::new_with_root(root);
    let mut found = bst.get(0);
    assert!(found.is_none());
    found = bst.get(2);
    assert!(found.is_some());
    let node = found.unwrap();
    assert_eq!(node.key, 2);
    assert_eq!(node.value, 2);
  }

  // #[test]
  // fn insertion() {
  // 	let mut bst = BinarySearchTree::empty();
  // 	let i1 = bst.insert(2, 2).unwrap();
  // 	assert_eq!(i1.key, 2);
  // 	assert_eq!(i1.value, 2);
  // }
}
