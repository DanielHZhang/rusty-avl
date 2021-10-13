use std::{
  cmp::{max, Ordering},
  fmt::Debug,
  mem, usize,
};

pub(crate) type Branch<K, V> = Option<Box<Node<K, V>>>;

enum BalanceFactor {
  Balanced,
  LeftHeavy(u8),
  RightHeavy(u8),
}

#[derive(Debug)]
pub struct Node<K: Ord, V: PartialEq> {
  pub key: K,
  pub value: V,
  pub left: Branch<K, V>,
  pub right: Branch<K, V>,
  pub(crate) height: usize,
}

impl<K: Ord + Debug, V: PartialEq> Node<K, V> {
  /// Creates an empty leaf Node with an initial height of 1.
  pub(crate) fn new(key: K, value: V) -> Self {
    Self {
      key,
      value,
      height: 1,
      left: None,
      right: None,
    }
  }

  /// Returns true if the Node has no children.
  pub fn is_leaf(&self) -> bool {
    self.left.is_none() && self.right.is_none()
  }

  /// Returns a reference to the minimum child Node from the current Node.
  pub(crate) fn min(&self) -> Option<&Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(node) = &cur.left {
      cur = node.as_ref();
    }
    Some(cur)
  }

  /// Returns a mutable reference to the minimum child Node from the current Node.
  pub(crate) fn min_mut(&mut self) -> Option<&mut Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(ref mut node) = cur.left {
      cur = node.as_mut();
    }
    Some(cur)
  }

  /// Returns a reference to the maximum child Node from the current Node.
  pub(crate) fn max(&self) -> Option<&Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(node) = &cur.right {
      cur = node.as_ref();
    }
    Some(cur)
  }

  /// Returns a mutable reference to the maximum child Node from the current Node.
  pub(crate) fn max_mut(&mut self) -> Option<&mut Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(ref mut node) = cur.right {
      cur = node.as_mut();
    }
    Some(cur)
  }

  /// Returns true if the current Node was rebalanced, false if the Node is already balanced.
  /// Rebalances the Node by performing a left rotation if the Node is right heavy, or a right
  /// rotation if the Node is left heavy.
  pub(crate) fn rebalance(&mut self) -> bool {
    match self.balance_factor() {
      BalanceFactor::RightHeavy(2) => match self.right.as_mut() {
        Some(right_child) => {
          // Check if right child of root is left heavy
          if let BalanceFactor::LeftHeavy(1) = right_child.balance_factor() {
            right_child.rotate_right();
          }
          self.rotate_left()
        }
        None => false,
      },
      BalanceFactor::LeftHeavy(2) => match self.left.as_mut() {
        Some(left_child) => {
          // Check if left child of root is right heavy
          if let BalanceFactor::RightHeavy(1) = left_child.balance_factor() {
            left_child.rotate_left();
          }
          self.rotate_right()
        }
        None => false,
      },
      _ => false, // No rebalancing required
    }
  }

  /// Returns true if the Node was rotated left. A left rotation demotes the root Node (that called
  /// rotate) into the left child and promotes its right child into the new root.
  fn rotate_left(&mut self) -> bool {
    if self.right.is_none() {
      return false;
    }
    let right = self.right.as_mut().unwrap();
    let right_left = right.left.take();
    let right_right = right.right.take();
    let mut new_root = mem::replace(&mut self.right, right_left);
    mem::swap(self, new_root.as_deref_mut().unwrap());
    self.left = new_root; // New root now contains old self
    self.right = right_right;

    // Update heights of all involved nodes
    if let Some(node) = &mut self.left {
      node.update_height();
    }
    if let Some(node) = &mut self.right {
      node.update_height();
    }
    self.update_height();
    true
  }

  /// Returns true fi the Node was rotated right. A right rotation demotes the root Node (that
  /// called rotate) into the right child and promotes its left child into the new root.
  fn rotate_right(&mut self) -> bool {
    if self.left.is_none() {
      return false;
    }
    let left = self.left.as_mut().unwrap();
    let left_left = left.left.take();
    let left_right = left.right.take();
    let mut new_root = mem::replace(&mut self.left, left_right);
    let new_root_node = new_root.as_deref_mut().unwrap();
    mem::swap(self, new_root_node);
    self.left = left_left;
    self.right = new_root; // New root now contains old self

    // Update heights of all involved nodes
    if let Some(node) = &mut self.left {
      node.update_height();
    }
    if let Some(node) = &mut self.right {
      node.update_height();
    }
    self.update_height();
    true
  }

  /// Returns the height of the left subtree or 0 if the Node has no left child.
  fn left_height(&self) -> usize {
    self.left.as_ref().map_or(0, |left| left.height)
  }

  /// Returns the height of the right subtree or 0 if the Node has no right child.
  fn right_height(&self) -> usize {
    self.right.as_ref().map_or(0, |right| right.height)
  }

  /// Updates the height of the Node given the updated heights of its left and right subtrees.
  pub fn update_height(&mut self) {
    self.height = 1 + max(self.left_height(), self.right_height());
  }

  /// Calculates the balance factor of the Node given the heights of its left and right subtrees.
  fn balance_factor(&mut self) -> BalanceFactor {
    let left_height = self.left_height();
    let right_height = self.right_height();

    // Ensure that difference is always positive for u8
    match left_height.cmp(&right_height) {
      Ordering::Less => BalanceFactor::RightHeavy((right_height - left_height) as u8),
      Ordering::Greater => BalanceFactor::LeftHeavy((left_height - right_height) as u8),
      Ordering::Equal => BalanceFactor::Balanced,
    }
  }
}

/// A trait for removing and returning the minimum Node within a subtree.
pub trait Extract {
  fn extract_min(&mut self) -> Self;
}

impl<K: Ord + Debug, V: PartialEq> Extract for Branch<K, V> {
  fn extract_min(&mut self) -> Self {
    let mut min = self;
    if min.is_none() {
      return None;
    }
    while min.as_ref().unwrap().left.is_some() {
      min = &mut min.as_mut().unwrap().left;
    }
    // Replace the found min node with it's right child
    let right_child = min.as_mut().unwrap().right.take();
    let extracted = std::mem::replace(min, right_child);
    extracted
  }
}

#[cfg(test)]
mod test {
  use super::Node;

  #[test]
  fn rotate_left() {
    /* Right-right case
       1               2
         2     ->    1   3
           3
    */
    let mut root = Box::new(Node {
      key: 1,
      value: 1,
      height: 3,
      left: None,
      right: Some(Box::new(Node {
        key: 2,
        value: 2,
        height: 2,
        left: None,
        right: Some(Box::new(Node::new(3, 3))),
      })),
    });

    assert!(root.rotate_left());
    assert_eq!(root.key, 2, "rotated root key");

    let left = root.left.as_mut().unwrap();
    let right = root.right.as_mut().unwrap();

    assert_eq!(left.key, 1, "left child key");
    assert_eq!(right.key, 3, "right child key");
  }

  #[test]
  fn rotate_right() {
    /* Left-left case
           3           2
         2     ->    1   3
       1
    */
    let mut root = Box::new(Node {
      key: 3,
      value: 3,
      height: 3,
      left: Some(Box::new(Node {
        key: 2,
        value: 2,
        height: 2,
        left: Some(Box::new(Node::new(1, 1))),
        right: None,
      })),
      right: None,
    });

    assert!(root.rotate_right());
    assert_eq!(root.key, 2, "rotated root key");

    let left = root.left.as_mut().unwrap();
    let right = root.right.as_mut().unwrap();

    assert_eq!(left.key, 1, "left child key");
    assert_eq!(right.key, 3, "right child key");
  }

  #[test]
  fn rebalance_right_left() {
    /* First rotate right to get the right-right case, then rotate left
       1           1                  2
         3    ->     2      ->     1    3
       2               3
    */
    let mut root = Box::new(Node {
      key: 1,
      value: 1,
      height: 3,
      left: None,
      right: Some(Box::new(Node {
        key: 3,
        value: 3,
        height: 2,
        left: Some(Box::new(Node::new(2, 2))),
        right: None,
      })),
    });

    assert!(root.rebalance());
    assert_eq!(root.key, 2);
    assert_eq!(root.height, 2);

    let left = root.left.as_ref().unwrap();
    assert_eq!(left.key, 1);
    assert_eq!(left.height, 1);

    let right = root.right.as_ref().unwrap();
    assert_eq!(right.key, 3);
    assert_eq!(right.height, 1);
  }

  #[test]
  fn rebalance_left_right() {
    /* First rotate right to get the right-right case, then rotate left
         3              3             2
       1      ->      2      ->     1   3
         2          1
    */
    let mut root = Box::new(Node {
      key: 3,
      value: 3,
      height: 3,
      left: Some(Box::new(Node {
        key: 1,
        value: 1,
        height: 2,
        left: None,
        right: Some(Box::new(Node::new(2, 2))),
      })),
      right: None,
    });

    assert!(root.rebalance());
    assert_eq!(root.key, 2);
    assert_eq!(root.height, 2);

    let left = root.left.as_ref().unwrap();
    assert_eq!(left.key, 1);
    assert_eq!(left.height, 1);

    let right = root.right.as_ref().unwrap();
    assert_eq!(right.key, 3);
    assert_eq!(right.height, 1);
  }
}
