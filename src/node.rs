use std::{cmp::max, fmt::Debug, mem, usize};

pub type Branch<K, V> = Option<Box<Node<K, V>>>;

enum BalanceFactor {
  Balanced,
  LeftHeavy(u8),
  RightHeavy(u8),
}

#[derive(Debug)]
pub struct Node<K: Ord, V: PartialEq> {
  height: usize,
  pub key: K,
  pub value: V,
  pub count: u32,
  pub left: Branch<K, V>,
  pub right: Branch<K, V>,
}

impl<K: Ord, V: PartialEq> Node<K, V> {
  pub fn new(key: K, value: V) -> Self {
    Self {
      key,
      value,
      count: 0,
      height: 0,
      left: None,
      right: None,
    }
  }

  pub fn branch(key: K, value: V, left: Self, right: Self) -> Self {
    Self {
      key,
      value,
      count: 0,
      height: 0,
      left: Some(Box::new(left)),
      right: Some(Box::new(right)),
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

  fn left_height(&self) -> usize {
    self.left.as_ref().map_or(0, |left| left.height)
  }

  fn right_height(&self) -> usize {
    self.right.as_ref().map_or(0, |right| right.height)
  }

  fn balance_factor(&mut self) -> BalanceFactor {
    let left_height = self.left_height();
    let right_height = self.right_height();
    if left_height > right_height {
      BalanceFactor::LeftHeavy((left_height - right_height) as u8)
    } else if left_height < right_height {
      BalanceFactor::RightHeavy((right_height - left_height) as u8)
    } else {
      BalanceFactor::Balanced
    }
  }

  pub fn update_height(&mut self) {
    self.height = 1 + max(self.left_height(), self.right_height());
  }

  /// Assuming you are at the parent node to be demoted
  pub fn rotate_left(&mut self) -> bool {
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
    true
  }

  /// Assuming you are at the parent node to be demoted
  pub fn rotate_right(&mut self) -> bool {
    if self.left.is_none() {
      return false;
    }
    let left = self.left.as_mut().unwrap();
    let left_left = left.left.take();
    let left_right = left.right.take();
    let mut new_root = mem::replace(&mut self.left, left_right);
    let new_root_node = new_root.as_deref_mut().unwrap();
    mem::swap(self, new_root_node);
    // mem::swap(&mut self.value, &mut new_root_node.value);
    // mem::swap(&mut self.key, &mut new_root_node.key);
    // mem::swap(&mut self.count, &mut new_root_node.count);
    self.left = left_left;
    self.right = new_root; // New root now contains old self
    true
  }

  pub fn rebalance(&mut self) -> bool {
    match self.balance_factor() {
      BalanceFactor::RightHeavy(2) => match self.right.as_deref_mut() {
        None => false,
        Some(right_child) => {
          // Check if right child of root is left heavy
          if let BalanceFactor::LeftHeavy(1) = right_child.balance_factor() {
            right_child.rotate_right();
          }
          self.rotate_left()
        }
      },
      BalanceFactor::LeftHeavy(2) => match self.left.as_deref_mut() {
        None => false,
        Some(left_child) => {
          // Check if left child of root is right heavy
          if let BalanceFactor::RightHeavy(1) = left_child.balance_factor() {
            left_child.rotate_left();
          }
          self.rotate_right()
        }
      },
      _ => false, // No rebalancing required
    }
  }
}

pub trait NodeOption<K: Ord, V: PartialEq> {
  fn extract_min(&mut self) -> Self;
  fn extract_max(&mut self) -> Self;
}

impl<K: Ord, V: PartialEq> NodeOption<K, V> for Option<Box<Node<K, V>>> {
  fn extract_min(&mut self) -> Self {
    let mut cur = self;
    while cur
      .as_ref()
      .expect("Cannot extract from None branch")
      .left
      .is_some()
    {
      cur = &mut cur.as_mut().unwrap().left;
    }
    cur.take()
  }

  fn extract_max(&mut self) -> Self {
    let mut cur = self;
    while cur
      .as_ref()
      .expect("Cannot extract from None branch")
      .left
      .is_some()
    {
      cur = &mut cur.as_mut().unwrap().right;
    }
    cur.take()
  }
}

#[cfg(test)]
mod test {
  use super::Node;
  use crate::iter::{NodeIterInorder, NodeIterPostorder, NodeIterPreorder};

  #[test]
  fn rotate_right() {
    let mut root = Node::branch(
      4,
      4,
      Node::branch(2, 2, Node::new(1, 1), Node::new(3, 3)),
      Node::new(5, 5),
    );
    assert!(root.rotate_right());
    let expected_preorder = Vec::from([2, 1, 4, 3, 5]);
    for (index, node) in NodeIterPreorder::new(Some(&root)).enumerate() {
      assert_eq!(node.key, expected_preorder[index]);
    }
    let expected_postorder = Vec::from([1, 3, 5, 4, 2]);
    for (index, node) in NodeIterPostorder::new(Some(&root)).enumerate() {
      assert_eq!(node.key, expected_postorder[index]);
    }
  }

  #[test]
  fn rotate_left() {
    let mut root = Node::branch(
      2,
      2,
      Node::new(1, 1),
      Node::branch(4, 4, Node::new(3, 3), Node::new(5, 5)),
    );
    assert!(root.rotate_left());
    let expected_preorder = Vec::from([4, 2, 1, 3, 5]);
    for (index, node) in NodeIterPreorder::new(Some(&root)).enumerate() {
      assert_eq!(node.key, expected_preorder[index]);
    }
    let expected_postorder = Vec::from([1, 3, 2, 5, 4]);
    for (index, node) in NodeIterPostorder::new(Some(&root)).enumerate() {
      assert_eq!(node.key, expected_postorder[index]);
    }
  }
}
