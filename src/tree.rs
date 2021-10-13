use super::{
  iter::{IterInorder, IterPostorder, IterPreorder},
  node::{Branch, Extract, Node},
};
use std::{borrow::Borrow, cmp::Ordering, collections::VecDeque, fmt::Debug};

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
  pub fn get(&self, target: &K) -> Option<&Node<K, V>>
// where
  //   K: Borrow<Q>,
  //   Q: PartialOrd + Eq + ?Sized,
  {
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
      // println!("GOES HERE: {:?} WHAT IS HEIGHT: {}", node.key, node.height);
      node.update_height();
      node.rebalance();
    }
    None
  }

  pub fn remove(&mut self, key: &K) -> Option<V> {
    let mut visited = Vec::<*mut Node<K, V>>::new(); // Store raw mut pointers
    let mut target = &mut self.root;

    while let Some(node) = target.as_ref() {
      match key.cmp(&node.key) {
        Ordering::Less => {
          let node = target.as_deref_mut().unwrap();
          visited.push(node);
          target = &mut node.left;
        }
        Ordering::Greater => {
          let node = target.as_deref_mut().unwrap();
          visited.push(node);
          target = &mut node.right;
        }
        Ordering::Equal => {
          break;
        }
      }
    }

    if target.is_none() {
      return None;
    }
    self.size -= 1;

    let mut node = target.take().unwrap();
    match (node.left.as_mut(), node.right.as_mut()) {
      (None, None) => *target = None,
      (Some(_), None) => *target = node.left.take(),
      (None, Some(_)) => *target = node.right.take(),
      (Some(_), Some(_)) => {
        let mut extracted = node.right.extract_min();
        if let Some(ref mut root) = extracted {
          println!("GOIND TO REBALANCE");
          root.left = node.left;
          root.right = node.right;
          root.rebalance();
          println!("ROOT: {:?}, height: {}", root.key, root.height);
        }
        *target = extracted;
      }
    };

    for parent in visited.into_iter().rev() {
      let node = unsafe { &mut *parent };
      node.update_height();
      node.rebalance();
    }

    Some(node.value)
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
    self
      .root
      .as_deref()
      .map(|root| {
        let mut visited = Vec::from([root]);
        while let Some(node) = visited.last() {
          match key.cmp(&node.key) {
            Ordering::Less => match node.left.as_deref() {
              Some(left) => visited.push(left),
              None => break,
            },
            Ordering::Greater => match node.right.as_deref() {
              Some(right) => visited.push(right),
              None => break,
            },
            Ordering::Equal => match node.right.as_deref() {
              Some(right) => return right.smallest().or(Some(right)),
              None => {
                // Trace backwards through visited parents, until encountering successor
                return visited.into_iter().rev().find(|parent| &parent.key > key);
              }
            },
          };
        }
        None
      })
      .unwrap_or(None)
  }

  pub fn predecessor(&mut self, key: &K) -> Option<&Node<K, V>> {
    self
      .root
      .as_deref()
      .map(|root| {
        let mut visited = Vec::from([root]);
        while let Some(node) = visited.last() {
          match key.cmp(&node.key) {
            Ordering::Less => match node.left.as_deref() {
              Some(node) => visited.push(node),
              None => break,
            },
            Ordering::Greater => match node.right.as_deref() {
              Some(node) => visited.push(node),
              None => break,
            },
            Ordering::Equal => match node.left.as_deref() {
              Some(left) => return left.largest().or(Some(left)),
              None => {
                // Trace backwards through visited parents, until encounting predecessor
                return visited.into_iter().rev().find(|parent| &parent.key < key);
              }
            },
          }
        }
        None
      })
      .unwrap_or(None)
  }

  /// Returns the maximum node count (not edge count) from the root node to a leaf node.
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
  pub fn iter_preorder(&self) -> IterPreorder<K, V> {
    IterPreorder::new(self.root.as_deref())
  }

  /// Returns an iterator that performs an in-order traversal of the tree
  pub fn iter_inorder(&self) -> IterInorder<K, V> {
    IterInorder::new(self.root.as_deref())
  }

  /// Returns an iterator that performs a post-order traversal of the tree
  pub fn iter_postorder(&self) -> IterPostorder<K, V> {
    IterPostorder::new(self.root.as_deref())
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
    let mut avl = AvlTree::new(Node::new(2, 2));
    avl.insert(4, 4);

    assert!(avl.get(&0).is_none()); // Non-existent keys should return None

    let found = avl.get(&2).unwrap();
    assert_eq!(found.key, 2);
    assert_eq!(found.value, 2);

    let found = avl.get_mut(&4).unwrap();
    assert_eq!(found.key, 4);
    assert_eq!(found.value, 4);
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
    for key in [1, 2, 3, 4, 5] {
      let result = avl.insert(key, key);
      assert!(result.is_none());
    }

    assert_eq!(avl.len(), 5, "length should be updated");

    let root = avl.root.as_ref().unwrap();
    assert_eq!(root.key, 2, "rebalancing of root node should occur");
    let right = root.right.as_ref().unwrap();
    assert_eq!(right.key, 4, "rebalancing of right node should occur");

    println!("what: {:#?}", root);

    assert_eq!(root.height, 3, "height should be correct after rebalancing");

    // Inserting existing keys should return previous value
    assert_eq!(avl.insert(2, 12), Some(2));
    assert_eq!(avl.insert(4, 14), Some(4));
  }

  #[test]
  fn remove() {
    let mut avl = AvlTree::default();
    for key in [5, 2, 12, 1, 3, 8, 15, 10] {
      avl.insert(key, key);
    }

    assert!(avl.remove(&20).is_none()); // non-existent key

    // println!("{:#?}", avl.root.as_ref());

    assert_eq!(avl.remove(&5), Some(5)); // remove root value
    assert_eq!(avl.root.as_ref().unwrap().value, 8);

    // println!("{:#?}", avl.root.as_ref());
    // assert!(false);

    assert_eq!(avl.remove(&8), Some(8)); // remove root value
    assert_eq!(avl.root.as_ref().unwrap().value, 10);

    assert_eq!(avl.remove(&15), Some(15)); // remove leaf with no children

    assert_eq!(avl.remove(&10), Some(10)); // remove root, causing rebalance
                                           // println!("{:#?}", avl.root.as_ref());

    assert_eq!(avl.remove(&3), Some(3));

    // println!("{:#?}", avl.root.as_ref());
    assert!(false);
    // assert_eq!(avl.root.as_ref().unwrap().value, 3);
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

  fn avl_cessor_setup<'a>() -> AvlTree<i32, i32> {
    let mut avl = AvlTree::default();
    for key in [5, 2, 1, 3, 4, 7, 6, 8] {
      avl.insert(key, key);
    }
    avl
  }

  #[test]
  fn successor() {
    let mut avl = avl_cessor_setup();
    let mut key = 1;
    for expected in [2, 3, 4, 5, 6, 7, 8] {
      let suc = avl
        .successor(&key)
        .unwrap_or_else(|| panic!("Missing successor of {}", key));
      assert_eq!(suc.key, expected);
      key = suc.key;
    }
    assert!(avl.successor(&8).is_none());
  }

  #[test]
  fn predecessor() {
    let mut avl = avl_cessor_setup();
    let mut key = 8;
    for expected in [7, 6, 5, 4, 3, 2, 1] {
      let pre = avl
        .predecessor(&key)
        .unwrap_or_else(|| panic!("Missing predecessor of {}", key));
      assert_eq!(pre.key, expected);
      key = pre.key;
    }
    assert!(avl.predecessor(&1).is_none());
  }

  fn avl_iter_setup() -> AvlTree<i32, i32> {
    let mut avl = AvlTree::default();
    for key in [6, 3, 8, 1, 2, 9, 5, 4, 7, 10] {
      avl.insert(key, key);
    }
    avl
  }

  #[test]
  fn iter_preorder() {
    let bst = avl_iter_setup();
    let expected = Vec::from([6, 3, 1, 2, 5, 4, 8, 7, 9, 10]);
    for (index, node) in bst.iter_preorder().enumerate() {
      assert_eq!(node.key, expected[index]);
    }
  }

  #[test]
  fn iter_inorder() {
    let bst = avl_iter_setup();
    let expected: Vec<i32> = (1..=10).collect();
    for (index, node) in bst.iter_inorder().enumerate() {
      assert_eq!(node.key, expected[index]);
    }
  }

  #[test]
  fn iter_postorder() {
    let bst = avl_iter_setup();
    let expected = Vec::from([2, 1, 4, 5, 3, 7, 10, 9, 8, 6]);
    for (index, node) in bst.iter_postorder().enumerate() {
      assert_eq!(node.key, expected[index]);
    }
  }
}
