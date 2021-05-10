use super::{
  iter::{NodeIterInorder, NodeIterPostorder, NodeIterPreorder},
  node::{Node, NodeOption, Tree},
};
use std::{cmp::Ordering, collections::VecDeque, fmt::Debug};

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

  pub fn new_avl() -> Self {
    Self {
      avl: true,
      ..BinarySearchTree::new()
    }
  }

  pub fn new_root(root: Node<K, V>) -> Self {
    Self {
      root: Some(Box::new(root)),
      size: 1,
      avl: false,
    }
  }

  pub fn new_avl_root(root: Node<K, V>) -> Self {
    Self {
      avl: true,
      ..BinarySearchTree::new_root(root)
    }
  }

  pub fn get(&self, key: &K) -> Option<&Node<K, V>> {
    match self.root.as_ref() {
      None => None,
      Some(node) => {
        let mut cur = node;
        loop {
          let target = match key.cmp(&cur.key) {
            Ordering::Less => &cur.left,
            Ordering::Greater => &cur.right,
            Ordering::Equal => {
              return Some(cur.as_ref());
            }
          };
          match target {
            None => return None,
            Some(node) => cur = node,
          }
        }
      }
    }
  }

  pub fn get_mut(&mut self, key: &K) -> Option<&mut Node<K, V>> {
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
          match target {
            None => return None,
            Some(node) => cur = node,
          }
        }
      }
    }
  }

  pub fn contains(&self, key: &K) -> bool {
    self.get(&key).is_some()
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

  pub fn successor(&mut self, key: &K) -> Option<&Node<K, V>> {
    match self.root.as_deref() {
      None => None,
      Some(root) => {
        let mut visited = Vec::from([root]);
        loop {
          match visited.last() {
            None => return None,
            Some(node) => match key.cmp(&node.key) {
              Ordering::Less => match node.left.as_deref() {
                None => return None,
                Some(left) => visited.push(left),
              },
              Ordering::Greater => match node.right.as_deref() {
                None => return None,
                Some(right) => visited.push(right),
              },
              Ordering::Equal => match node.right.as_deref() {
                None => {
                  // Trace backwards through visited parents
                  for &parent in visited.iter().rev() {
                    if parent.key > *key {
                      return Some(parent);
                    }
                  }
                  return None;
                }
                Some(right) => return right.smallest(),
              },
            },
          }
        }
      }
    }
  }

  pub fn predecessor(&mut self, key: &K) -> Option<&Node<K, V>> {
    match self.root.as_deref() {
      None => None,
      Some(root) => {
        let mut visited = Vec::from([root]);
        loop {
          match visited.last() {
            None => return None,
            Some(node) => match key.cmp(&node.key) {
              Ordering::Less => match node.left.as_deref() {
                None => return None,
                Some(node) => visited.push(node),
              },
              Ordering::Greater => match node.right.as_deref() {
                None => return None,
                Some(node) => visited.push(node),
              },
              Ordering::Equal => match node.left.as_deref() {
                None => {
                  // Trace backwards through visited parents
                  for &parent in visited.iter().rev() {
                    if parent.key < *key {
                      return Some(parent);
                    }
                  }
                  return None;
                }
                Some(left) => return left.largest(),
              },
            },
          }
        }
      }
    }
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
          match target {
            None => {
              *target = Some(Box::new(Node::new(key, value)));
              self.size += 1;
              return true;
            }
            Some(node) => cur = node,
          }
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
          if self.avl {
            //
          }
          return true;
        }
      }
    }
    false
  }

  /// Height is considered the node count, not the edge count
  pub fn height(&self) -> usize {
    match self.root.as_deref() {
      None => 0,
      Some(root) => {
        let mut height = 0;
        let mut queue: VecDeque<&Node<K, V>> = Vec::from([root]).into_iter().collect();
        while !queue.is_empty() {
          let mut size = queue.len();
          while size > 0 {
            let front = queue.pop_front().unwrap();
            if let Some(node) = front.left.as_deref() {
              queue.push_back(node);
            }
            if let Some(node) = front.right.as_deref() {
              queue.push_back(node);
            }
            size -= 1;
          }
          height += 1;
        }
        height
      }
    }
  }

  pub fn to_balanced(self) {}

  fn balance(&mut self) {}

  fn right_rotation() {}

  fn left_rotation() {}

  pub fn iter_preorder(&self) -> NodeIterPreorder<K, V> {
    NodeIterPreorder::new(self.root.as_deref())
  }

  pub fn iter_inorder(&self) -> NodeIterInorder<K, V> {
    NodeIterInorder::new(self.root.as_deref())
  }

  pub fn iter_postorder(&self) -> NodeIterPostorder<K, V> {
    NodeIterPostorder::new(self.root.as_deref())
  }

  // pub fn into_vec(&self) -> Vec<&Node<K, V>> {
  //   let mut new_vec = Vec::with_capacity(self.size);
  //   new_vec
  // }
}

#[cfg(test)]
mod test {
  use super::BinarySearchTree;
  use super::Node;

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
    let mut found = bst.get(&0);
    assert!(found.is_none());
    found = bst.get(&2);
    assert!(found.is_some());
    let mut node = found.unwrap();
    assert_eq!(node.key, 2);
    assert_eq!(node.value, 2);
    // fn get_mut
    let found_mut = bst.get_mut(&2);
    assert!(found_mut.is_some());
    let mut node_mut = found_mut.unwrap();
    node_mut.key = 5;
    node_mut.value = 10;
    found = bst.get(&5);
    assert!(found.is_some());
    node = found.unwrap();
    assert_eq!(node.key, 5);
    assert_eq!(node.value, 10);
    // fn contains
    assert!(bst.contains(&5));
    assert!(!bst.contains(&10));
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
    let mut bst = BinarySearchTree::new();
    bst.insert(8, "eight");
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
    let mut bst = BinarySearchTree::new();
    bst.insert(5, "five");
    bst.insert(2, "two");
    bst.insert(1, "one");
    let small = bst.smallest();
    assert!(small.is_some());
    let node = small.unwrap();
    assert_eq!(node.key, 1);
    assert!(bst.get(&5).is_some());
    assert!(bst.get(&2).is_some());
    assert!(bst.get(&1).is_some());
  }

  #[test]
  fn successor() {
    let mut bst = BinarySearchTree::new();
    bst.insert(5, "five");
    bst.insert(2, "two");
    bst.insert(1, "one");
    bst.insert(3, "three");
    bst.insert(4, "four");
    bst.insert(7, "seven");
    bst.insert(6, "six");
    bst.insert(8, "eight");
    let mut suc = bst.successor(&1).expect("Sucessor of key 1 was not found");
    assert_eq!(suc.key, 2);
    suc = bst.successor(&2).expect("Successor of key 2 was not found");
    assert_eq!(suc.key, 3);
    suc = bst.successor(&3).expect("Successor of key 3 was not found");
    assert_eq!(suc.key, 4);
    suc = bst.successor(&4).expect("Successor of key 4 was not found");
    assert_eq!(suc.key, 5);
    suc = bst.successor(&5).expect("Successor of key 5 way not found");
    assert_eq!(suc.key, 6);
    suc = bst.successor(&6).expect("Successor of key 6 way not found");
    assert_eq!(suc.key, 7);
    suc = bst.successor(&7).expect("Successor of key 7 way not found");
    assert_eq!(suc.key, 8);
    assert!(bst.successor(&8).is_none());
  }
}
