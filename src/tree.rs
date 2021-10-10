use super::{
  iter::{NodeIterInorder, NodeIterPostorder, NodeIterPreorder},
  node::{Branch, Node, NodeOption},
};
use std::{cmp::Ordering, collections::VecDeque, error::Error, fmt::Debug};

#[derive(Debug)]
pub struct AvlTree<K: Ord, V: PartialEq> {
  root: Branch<K, V>,
  size: usize,
}

impl<K: Ord, V: PartialEq> Default for AvlTree<K, V> {
  fn default() -> Self {
    Self {
      root: None,
      size: 0,
    }
  }
}

// TODO: implement FromIterator for AvlTree

impl<K: Ord + Debug, V: PartialEq> AvlTree<K, V> {
  /// Constructs a new AVL tree with an empty root.
  pub fn new(root: Node<K, V>) -> Self {
    Self {
      root: Some(Box::new(root)),
      size: 1,
    }
  }

  /// Returns true if the AVL tree contains no nodes.
  pub fn is_empty(&self) -> bool {
    self.root.is_none()
  }

  /// Returns true if the AVL tree contains a node with the provided key.
  pub fn contains(&self, key: &K) -> bool {
    self.get(&key).is_some()
  }

  /// Clears the AVL tree, removing all nodes.
  pub fn clear(&mut self) {
    self.root.take();
    self.size = 0;
  }

  /// Returns the number of unique nodes within the AVL tree.
  pub fn len(&self) -> usize {
    self.size
  }

  /// Returns a reference to the node with the provided key.
  pub fn get(&self, target: &K) -> Option<&Node<K, V>> {
    self
      .root
      .as_ref()
      .map(|root| {
        let mut cur = root;
        loop {
          if target < &cur.key {
            cur = match &cur.left {
              Some(node) => node,
              None => return None,
            };
          } else if target > &cur.key {
            cur = match &cur.right {
              Some(node) => node,
              None => return None,
            };
          } else {
            return Some(cur.as_ref());
          }
        }
      })
      .unwrap_or(None)
  }

  pub fn get_mut(&mut self, target: &K) -> Option<&mut Node<K, V>> {
    self
      .root
      .as_mut()
      .map(|root| {
        let mut cur = root;
        loop {
          if target < &cur.key {
            cur = match &mut cur.left {
              Some(node) => node,
              None => return None,
            };
          } else if target > &cur.key {
            cur = match &mut cur.right {
              Some(node) => node,
              None => return None,
            };
          } else {
            return Some(cur.as_mut());
          }
        }
      })
      .unwrap_or(None)
  }

  pub fn insert(&mut self, key: K, value: V) -> Option<V> {
    let mut visited: Vec<*mut Node<K, V>> = Vec::new(); // Store raw mut pointers
    let mut cur = &mut self.root;

    while let Some(ref mut node) = cur {
      visited.push(node.as_mut());
      match key.cmp(&node.key) {
        Ordering::Less => cur = &mut node.left,
        Ordering::Greater => cur = &mut node.right,
        Ordering::Equal => {
          let old = std::mem::replace(&mut node.value, value);
          return Some(old);
        }
      };
    }

    *cur = Some(Box::new(Node::new(key, value)));
    self.size += 1;

    // Trace backwards through visited parents, updating their heights
    for parent in visited.into_iter().rev() {
      let node = unsafe { &mut *parent };
      node.update_height();
      node.rebalance();
    }
    None
  }

  pub fn remove(&mut self, key: &K) -> Option<Node<K, V>> {
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
    // if node.count > 1 {
    //   node.count -= 1;
    // } else {
    match (node.left.as_mut(), node.right.as_mut()) {
      (None, None) => *cur = None,
      (Some(_), None) => *cur = node.left.take(),
      (None, Some(_)) => *cur = node.right.take(),
      (Some(_), Some(_)) => {
        let left = node.left.take();
        let extracted = node.right.extract_min();
        // todo: need to call delete on the node.right after finding smallest,
        // otherwise node.right may have a right child which gets inadvertently removed
      } // }
    }

    for parent in visited.into_iter().rev() {
      let node = unsafe { &mut *parent };
      node.update_height();
      node.rebalance();
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

  pub fn largest(&self) -> Option<&Node<K, V>> {
    self
      .root
      .as_ref()
      .map(|root| root.largest())
      .unwrap_or(None)
  }

  pub fn largest_mut(&mut self) -> Option<&mut Node<K, V>> {
    self
      .root
      .as_mut()
      .map(|root| root.largest_mut())
      .unwrap_or(None)
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
                  println!("Goes here for: {:?}", key);
                  for parent in visited.into_iter().rev() {
                    if parent.key > *key {
                      return Some(parent);
                    }
                  }
                  return None;
                }
                Some(right) => match right.smallest() {
                  Some(node) => return Some(node),
                  None => return Some(right),
                },
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

  /// Height is considered the node count, not the edge count
  pub fn height(&self) -> usize {
    self
      .root
      .as_deref()
      .map(|root| {
        let mut height = 0;
        let mut queue = Vec::from([root])
          .into_iter()
          .collect::<VecDeque<&Node<K, V>>>();
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
      })
      .unwrap_or(0)
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
    let avl: AvlTree<i32, i32> = AvlTree::default();
    assert!(avl.root.is_none());
    assert!(avl.is_empty());
    assert_eq!(avl.len(), 0);

    let avl = AvlTree::new(Node::new("key", "value"));
    assert!(avl.root.is_some());
    assert!(!avl.is_empty());
    assert_eq!(avl.len(), 1);
  }

  #[test]
  fn get() {
    let avl = AvlTree::new(Node::new(2, 2));
    let found = avl.get(&0);
    assert!(found.is_none());
    let found = avl.get(&2).unwrap();
    assert_eq!(found.key, 2);
    assert_eq!(found.value, 2);
  }

  #[test]
  fn get_mut() {
    let mut avl = AvlTree::new(Node::new(2, 2));
    let found = avl.get_mut(&2).unwrap();
    assert_eq!(found.key, 2);
    assert_eq!(found.value, 2);
    found.key = 5;
    found.value = 10;
    let found = avl.get_mut(&5).unwrap();
    assert_eq!(found.key, 5);
    assert_eq!(found.value, 10);
  }

  #[test]
  fn contains() {
    let avl = AvlTree::new(Node::new(5, 2));
    assert!(avl.contains(&5));
    assert!(!avl.contains(&10));
  }

  #[test]
  fn insert() {
    let mut avl = AvlTree::default();

    // Inserting unique keys should return None
    assert!(avl.insert(1, 2).is_none());
    assert!(avl.insert(2, 4).is_none());
    assert!(avl.insert(3, 6).is_none());
    assert!(avl.insert(4, 8).is_none());

    // Length should be updated
    assert_eq!(avl.len(), 4);

    // Inserting existing keys should return previous value
    assert_eq!(avl.insert(2, 9).unwrap(), 4);
    assert_eq!(avl.insert(4, 5).unwrap(), 8);
  }

  #[test]
  fn remove() {
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
    let mut avl = AvlTree::default();
    avl.insert(5, "five");
    avl.insert(2, "two");
    avl.insert(1, "one");

    let smallest_mut = avl.smallest_mut();
    assert_eq!(smallest_mut.unwrap().key, 1);

    let smallest = avl.smallest();
    assert_eq!(smallest.unwrap().key, 1);
  }

  #[test]
  fn largest() {
    let mut avl = AvlTree::default();
    avl.insert(5, "five");
    avl.insert(10, "ten");
    avl.insert(16, "sixteen");

    let largest_mut = avl.largest_mut();
    assert_eq!(largest_mut.unwrap().key, 16);

    let largest = avl.largest();
    assert_eq!(largest.unwrap().key, 16);
  }

  #[test]
  fn successor() {
    let mut avl = AvlTree::default();
    avl.insert(5, "five");
    avl.insert(2, "two");
    avl.insert(1, "one");
    avl.insert(3, "three");
    avl.insert(4, "four");
    avl.insert(7, "seven");
    avl.insert(6, "six");
    avl.insert(8, "eight");

    // println!("{:#?}", avl.iter_inorder().collect::<Vec<_>>());
    println!("{:#?}", avl.root.as_ref().unwrap());
    let mut suc = avl.successor(&1).unwrap();
    assert_eq!(suc.key, 2);
    suc = avl.successor(&2).unwrap();
    assert_eq!(suc.key, 3);
    suc = avl.successor(&3).unwrap();
    assert_eq!(suc.key, 4);
    suc = avl.successor(&4).unwrap();
    assert_eq!(suc.key, 5);
    suc = avl.successor(&5).unwrap();
    assert_eq!(suc.key, 6);
    suc = avl.successor(&6).unwrap();
    assert_eq!(suc.key, 7);
    suc = avl.successor(&7).unwrap();
    assert_eq!(suc.key, 8);
    assert!(avl.successor(&8).is_none());
  }

  fn iter_test_setup() -> AvlTree<i32, i32> {
    let insertion_order = Vec::from([6, 3, 8, 1, 2, 9, 5, 4, 7, 10]);
    let mut bst = AvlTree::default();
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
