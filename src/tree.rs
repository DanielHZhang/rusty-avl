use super::{
  iter::{NodeIterInorder, NodeIterPostorder, NodeIterPreorder},
  node::{Branch, Node, NodeOption},
};
use std::{cmp::Ordering, collections::VecDeque, fmt::Debug};

#[derive(Debug)]
pub struct AvlTree<K: Ord, V: PartialEq> {
  root: Branch<K, V>,
  size: usize,
  avl: bool,
}

impl<K: Ord, V: PartialEq> Default for AvlTree<K, V> {
  fn default() -> Self {
    Self {
      root: None,
      size: 0,
      avl: false,
    }
  }
}

impl<K: Ord, V: PartialEq> AvlTree<K, V> {
  pub fn new() -> Self {
    AvlTree::default()
  }

  pub fn new_root(root: Node<K, V>) -> Self {
    Self {
      root: Some(Box::new(root)),
      size: 1,
      avl: false,
    }
  }

  pub fn new_avl() -> Self {
    Self {
      avl: true,
      ..AvlTree::default()
    }
  }

  pub fn new_avl_root(root: Node<K, V>) -> Self {
    Self {
      avl: true,
      ..AvlTree::new_root(root)
    }
  }

  pub fn is_empty(&self) -> bool {
    self.root.is_none()
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

  pub fn smallest(&self) -> Option<&Node<K, V>> {
    self
      .root
      .as_ref()
      .map(|root| root.smallest())
      .unwrap_or(None)
  }

  pub fn smallest_mut(&mut self) -> Option<&mut Node<K, V>> {
    self
      .root
      .as_mut()
      .map(|root| root.smallest_mut())
      .unwrap_or(None)
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
                  // Trace backwards through visited parents, until encountering successor
                  for parent in visited.into_iter().rev() {
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
                  // Trace backwards through visited parents, until encounting predecessor
                  for parent in visited.into_iter().rev() {
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
    let mut visited: Vec<*mut Node<K, V>> = Vec::new(); // Store raw mut pointers
    let mut cur = &mut self.root;
    // Find location to insert new node
    while let Some(node) = cur {
      visited.push(node.as_mut());
      match key.cmp(&node.key) {
        Ordering::Less => cur = &mut node.left,
        Ordering::Greater => cur = &mut node.right,
        Ordering::Equal => {
          if value == node.value {
            node.count += 1;
            return true;
          }
          return false;
        }
      };
    }
    // Perform insertion
    *cur = Some(Box::new(Node::new(key, value)));
    self.size += 1;
    if self.avl {
      // Trace backwards through visited parents, updating their heights
      for parent in visited.into_iter().rev() {
        let node = unsafe { &mut *parent }; // Unsafe deferencing of raw pointer
        node.update_height();
        node.rebalance();
      }
    }
    true
  }

  pub fn delete(&mut self, key: &K) -> Option<Node<K, V>> {
    let mut visited: Vec<*mut Node<K, V>> = Vec::new();
    let mut cur = &mut self.root;
    while let Some(node) = cur.as_deref() {
      match key.cmp(&node.key) {
        Ordering::Less => {
          let cur_node = cur.as_deref_mut().unwrap();
          visited.push(cur_node);
          cur = &mut cur_node.left;
        }
        Ordering::Greater => {
          let cur_node = cur.as_deref_mut().unwrap();
          visited.push(cur_node);
          cur = &mut cur_node.right;
        }
        Ordering::Equal => {
          break;
        }
      }
    }
    if cur.is_none() {
      return None;
    }
    let node = cur.as_mut().unwrap();
    if node.count > 1 {
      node.count -= 1;
    } else {
      match (node.left.as_mut(), node.right.as_mut()) {
        (None, None) => *cur = None,
        (Some(_), None) => *cur = node.left.take(),
        (None, Some(_)) => *cur = node.right.take(),
        (Some(_), Some(_)) => {
          let left = node.left.take();
          let extracted = node.right.extract_min();
          // todo: need to call delete on the node.right after finding smallest,
          // otherwise node.right may have a right child which gets inadvertently removed
        }
      }
    }

    if self.avl {
      for parent in visited.into_iter().rev() {
        let node = unsafe { &mut *parent };
        node.update_height();
        node.rebalance();
      }
    }
    //   if node.count > 1 {
    //     node.count -= 1; // Decrement node count if there are duplicates
    //   } else {
    //     match (node.left.as_mut(), node.right.as_mut()) {
    //       (None, None) => *cur = None,
    //       (Some(_), None) => *cur = node.left.take(),
    //       (None, Some(_)) => *cur = node.right.take(),
    //       (Some(_), Some(_)) => *cur = node.right.extract_min(),
    //     }
    //   }
    //   self.size -= 1;
    //   if self.avl {
    //     //
    //   }
    //   return true;
    // break;
    None
  }

  pub fn clear(&mut self) {
    self.root.take();
    self.size = 0;
  }

  /// Returns the number of nodes with unique keys contained in this tree.
  pub fn len(&self) -> usize {
    self.size
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

  /// Returns an iterator that performs a pre-order traversal of the tree
  pub fn iter_preorder(&self) -> NodeIterPreorder<K, V> {
    NodeIterPreorder::new(self.root.as_deref())
  }

  /// Returns an iterator that performs an in-order traversal of the tree
  pub fn iter_inorder(&self) -> NodeIterInorder<K, V> {
    NodeIterInorder::new(self.root.as_deref())
  }

  /// Returns an iterator that performs a post-order traversal of the tree
  pub fn iter_postorder(&self) -> NodeIterPostorder<K, V> {
    NodeIterPostorder::new(self.root.as_deref())
  }
}

#[cfg(test)]
mod test {
  use super::AvlTree;
  use super::Node;

  #[test]
  fn new() {
    let bst: AvlTree<i32, i32> = AvlTree::new();
    assert!(bst.is_empty());
    assert_eq!(bst.len(), 0);
  }

  #[test]
  fn new_root() {
    let root = Node::new("key", "value");
    let bst = AvlTree::new_root(root);
    assert!(!bst.is_empty());
    assert!(bst.root.is_some());
    assert_eq!(bst.len(), 1);
  }

  #[test]
  fn get() {
    let bst = AvlTree::new_root(Node::new(2, 2));
    let found = bst.get(&0);
    assert!(found.is_none());
    let found = bst.get(&2).unwrap();
    assert_eq!(found.key, 2);
    assert_eq!(found.value, 2);
  }

  #[test]
  fn get_mut() {
    let mut bst = AvlTree::new_root(Node::new(2, 2));
    let found = bst.get_mut(&2).unwrap();
    assert_eq!(found.key, 2);
    assert_eq!(found.value, 2);
    found.key = 5;
    found.value = 10;
    let found = bst.get_mut(&5).unwrap();
    assert_eq!(found.key, 5);
    assert_eq!(found.value, 10);
  }

  #[test]
  fn contains() {
    let bst = AvlTree::new_root(Node::new(5, 2));
    assert!(bst.contains(&5));
    assert!(!bst.contains(&10));
  }

  #[test]
  fn insert() {
    let mut bst = AvlTree::new();
    assert!(bst.insert(2, 2));
    assert!(bst.insert(3, 3));
    assert!(bst.insert(2, 2));
    assert!(!bst.insert(2, 5));
    assert_eq!(bst.len(), 2);
  }

  #[test]
  fn delete() {
    // let mut bst = BinarySearchTree::new();
    // bst.insert(8, "eight");
    // bst.insert(2, "two");
    // bst.insert(5, "five");
    // bst.insert(1, "one");
    // bst.insert(10, "ten");
    // bst.insert(9, "nine");
    // assert!(bst.delete(2));
    // assert!(!bst.delete(2));
    // assert!(bst.delete(10));
    // assert_eq!(bst.len(), 4);
    // assert!(bst.delete(9));
    // assert!(bst.delete(8));
    // // assert!(bst.delete(1));
    // assert!(bst.delete(5));
    // // assert!(bst.root.is_none());
    // // assert_eq!(bst.len(), 0);
    // println!("{:?}", bst.root.as_deref().unwrap());
  }

  #[test]
  fn smallest() {
    let mut bst = AvlTree::new();
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
    let mut bst = AvlTree::new();
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

  fn iter_test_setup() -> AvlTree<i32, i32> {
    let insertion_order = Vec::from([6, 3, 8, 1, 2, 9, 5, 4, 7, 10]);
    let mut bst = AvlTree::new();
    for key in insertion_order {
      bst.insert(key, key);
    }
    bst
  }

  #[test]
  fn iter_preorder() {
    let bst = iter_test_setup();
    let expected = Vec::from([6, 3, 1, 2, 5, 4, 8, 7, 9, 10]);
    for (index, node) in bst.iter_preorder().enumerate() {
      assert_eq!(node.key, expected[index]);
    }
  }

  #[test]
  fn iter_inorder() {
    let bst = iter_test_setup();
    let expected: Vec<i32> = (1..=10).collect();
    for (index, node) in bst.iter_inorder().enumerate() {
      assert_eq!(node.key, expected[index]);
    }
  }

  #[test]
  fn iter_postorder() {
    let bst = iter_test_setup();
    let expected = Vec::from([2, 1, 4, 5, 3, 7, 10, 9, 8, 6]);
    for (index, node) in bst.iter_postorder().enumerate() {
      assert_eq!(node.key, expected[index]);
    }
  }
}
