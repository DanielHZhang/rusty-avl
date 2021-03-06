use std::{cmp::Ordering, collections::VecDeque, iter::FromIterator};

use super::{
  iter::{IterInorder, IterPostorder, IterPreorder},
  node::{Branch, Extract, Node},
};

/// An AVL tree implemented using purely iterative lookups. Stores a pointer to the root node and
/// the current number of unique nodes within the tree.
#[derive(Debug)]
pub struct AvlTree<K, V> {
  root: Branch<K, V>,
  size: usize,
}

impl<K, V> Default for AvlTree<K, V> {
  fn default() -> Self {
    Self {
      root: None,
      size: 0,
    }
  }
}

impl<K: Ord, V: PartialEq> FromIterator<(K, V)> for AvlTree<K, V> {
  fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
    let mut tree = Self::default();
    for (key, value) in iter {
      tree.insert(key, value);
    }
    tree
  }
}

impl<K: Ord + PartialEq + Clone> FromIterator<K> for AvlTree<K, K> {
  fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
    let mut tree = Self::default();
    for key in iter {
      tree.insert(key.clone(), key);
    }
    tree
  }
}

impl<K: Ord, V: PartialEq> AvlTree<K, V> {
  /// Creates a new AVL tree with an empty root.
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

  /// Returns a mutable reference to the node with the provided key.
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

  /// Inserts a key-value pair into the tree. If the tree did not previously contain the given key,
  /// None is returned, otherwise the old value associated with the key is returned.
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

  /// Removes the Node with the given key from the tree, returning its value if a Node with the key
  /// was previously in the tree.
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
          root.left = node.left;
          root.right = node.right;
          root.update_height();
          root.rebalance();
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

  /// Returns a reference to the minimum Node in the tree.
  pub fn min(&self) -> Option<&Node<K, V>> {
    self.root.as_ref().map(|root| root.min()).unwrap_or(None)
  }

  /// Returns a reference to the minimum Node in the tree.
  pub fn min_mut(&mut self) -> Option<&mut Node<K, V>> {
    self
      .root
      .as_mut()
      .map(|root| root.min_mut())
      .unwrap_or(None)
  }

  /// Returns a reference to the maximum Node in the tree.
  pub fn max(&self) -> Option<&Node<K, V>> {
    self.root.as_ref().map(|root| root.max()).unwrap_or(None)
  }

  /// Returns a mutable reference to maximum Node in the tree.
  pub fn max_mut(&mut self) -> Option<&mut Node<K, V>> {
    self
      .root
      .as_mut()
      .map(|root| root.max_mut())
      .unwrap_or(None)
  }

  /// Returns a reference to the successor Node of the given key. The successor is defined as the
  /// Node with the minimum key value that is larger than the provided key.
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
              Some(right) => return right.min().or(Some(right)),
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

  /// Returns a reference to the predecessor Node of the given key. The predecessor is defined as
  /// the Node with the maximum key value that is smaller than the provided key.
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
              Some(left) => return left.max().or(Some(left)),
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
    let avl = AvlTree::<i32, i32>::default();
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

    assert!(avl.get(&0).is_none(), "non-existent key returns None");

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
    for key in [1, 2, 3, 4, 5] {
      let result = avl.insert(key, key);
      assert!(
        result.is_none(),
        "inserting unique key returned {:?}",
        result
      );
    }

    assert_eq!(avl.len(), 5, "length is updated");

    let root = avl.root.as_ref().unwrap();
    assert_eq!(root.key, 2, "rebalancing of root node");

    let right = root.right.as_ref().unwrap();
    assert_eq!(right.key, 4, "rebalancing of right node");

    assert_eq!(root.height, 3, "height is correct after rebalancing");

    assert_eq!(
      avl.insert(2, 12),
      Some(2),
      "inserting existing key returns previous value"
    );
  }

  #[test]
  fn remove() {
    /* Tree after insertion rebalancing:
              5
         2          12
       1	 3    8       15
                 10
    */
    let mut avl = Vec::from([5, 2, 12, 1, 3, 8, 15, 10])
      .into_iter()
      .collect::<AvlTree<_, _>>();

    assert!(avl.remove(&20).is_none(), "non-existent key");

    assert_eq!(avl.remove(&5), Some(5), "remove root key 5");
    assert_eq!(avl.root.as_ref().unwrap().key, 8, "new root is correct");

    assert_eq!(avl.remove(&8), Some(8), "remove root key 8");
    assert_eq!(avl.root.as_ref().unwrap().key, 10, "new root is correct");

    assert_eq!(avl.remove(&15), Some(15), "remove leaf with no children");

    assert_eq!(
      avl.remove(&10),
      Some(10),
      "remove root key 10, causing rebalance"
    );
    assert_eq!(avl.root.as_ref().unwrap().key, 2, "new root is correct");

    assert_eq!(
      avl.remove(&1),
      Some(1),
      "remove root key 1, causing rebalance"
    );
    assert_eq!(avl.root.as_ref().unwrap().key, 3, "new root is correct");

    assert_eq!(avl.remove(&3), Some(3));
    assert_eq!(avl.remove(&12), Some(12));
    assert_eq!(avl.remove(&2), Some(2));

    assert!(avl.root.is_none());
    assert_eq!(avl.len(), 0);
  }

  #[test]
  fn smallest() {
    let mut avl = AvlTree::default();
    avl.insert(5, "five");
    avl.insert(2, "two");
    avl.insert(1, "one");

    let smallest_mut = avl.min_mut();
    assert_eq!(smallest_mut.unwrap().key, 1);

    let smallest = avl.min();
    assert_eq!(smallest.unwrap().key, 1);
  }

  #[test]
  fn largest() {
    let mut avl = AvlTree::default();
    avl.insert(5, "five");
    avl.insert(10, "ten");
    avl.insert(16, "sixteen");

    let largest_mut = avl.max_mut();
    assert_eq!(largest_mut.unwrap().key, 16);

    let largest = avl.max();
    assert_eq!(largest.unwrap().key, 16);
  }

  const TEST_NODES: [i32; 8] = [5, 2, 1, 3, 4, 7, 6, 8];

  #[test]
  fn successor() {
    let mut avl = Vec::from(TEST_NODES).into_iter().collect::<AvlTree<_, _>>();
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
    let mut avl = Vec::from(TEST_NODES).into_iter().collect::<AvlTree<_, _>>();
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
}
