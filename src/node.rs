use std::{cmp::max, fmt::Debug, mem, usize};

pub type Branch<K, V> = Option<Box<Node<K, V>>>;

enum BalanceFactor {
  Balanced,
  LeftHeavy(i8),
  RightHeavy(i8),
}

#[derive(Debug)]
pub struct Node<K: Ord, V: PartialEq> {
  pub(crate) height: usize,
  pub key: K,
  pub value: V,
  pub left: Branch<K, V>,
  pub right: Branch<K, V>,
}

impl<K: Ord + Debug, V: PartialEq> Node<K, V> {
  pub fn new(key: K, value: V) -> Self {
    Self {
      key,
      value,
      height: 1,
      left: None,
      right: None,
    }
  }

  pub fn is_leaf(&self) -> bool {
    self.left.is_none() && self.right.is_none()
  }

  pub(crate) fn smallest(&self) -> Option<&Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(node) = &cur.left {
      cur = node.as_ref();
    }
    Some(cur)
  }

  pub(crate) fn smallest_mut(&mut self) -> Option<&mut Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(ref mut node) = cur.left {
      cur = node.as_mut();
    }
    Some(cur)
  }

  pub(crate) fn largest(&self) -> Option<&Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(node) = &cur.right {
      cur = node.as_ref();
    }
    Some(cur)
  }

  pub(crate) fn largest_mut(&mut self) -> Option<&mut Self> {
    if self.is_leaf() {
      return None;
    }
    let mut cur = self;
    while let Some(ref mut node) = cur.right {
      cur = node.as_mut();
    }
    Some(cur)
  }

  pub(crate) fn rebalance(&mut self) -> bool {
    // self.update_height();
    match self.balance_factor() {
      BalanceFactor::RightHeavy(2) => match self.right.as_deref_mut() {
        Some(right_child) => {
          // Check if right child of root is left heavy
          if let BalanceFactor::LeftHeavy(1) = right_child.balance_factor() {
            right_child.rotate_right();
          }
          self.rotate_left()
        }
        None => false,
      },
      BalanceFactor::LeftHeavy(2) => match self.left.as_deref_mut() {
        Some(left_child) => {
          println!("SHOULD BE LEFT HEAVY: {:?}", left_child.key);
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

  /// Assuming you are at the parent node to be demoted
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

  /// Assuming you are at the parent node to be demoted
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

  fn left_height(&self) -> usize {
    self.left.as_ref().map_or(0, |left| left.height)
  }

  fn right_height(&self) -> usize {
    self.right.as_ref().map_or(0, |right| right.height)
  }

  pub fn update_height(&mut self) {
    self.height = 1 + max(self.left_height(), self.right_height());
  }

  fn balance_factor(&mut self) -> BalanceFactor {
    let left_height = self.left_height();
    let right_height = self.right_height();
    // TODO: convert to match on ordering and change back to u8
    if left_height > right_height {
      BalanceFactor::LeftHeavy((left_height - right_height) as i8)
    } else if left_height < right_height {
      BalanceFactor::RightHeavy((right_height - left_height) as i8)
    } else {
      BalanceFactor::Balanced
    }
  }
}

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
    // Remove extracted min, replacing it with the right child or left child passed from parent
    let mut right_child = min.as_mut().unwrap().right.take();
    if let Some(ref mut child) = right_child {
      child.rebalance();
    }

    // let new_child = match min.as_mut().unwrap().right.take() {
    //   Some(mut node) => {
    //     assert!(node.left.is_none()); // cur should equal left child if it existed
    //     node.left = child; // Set the left child passed down from the parent
    //     node.rebalance();
    //     Some(node)
    //   }
    //   None => child,
    // };
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
