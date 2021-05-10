use std::fmt::Debug;

pub type Tree<K, V> = Option<Box<Node<K, V>>>;

#[derive(Debug)]
pub struct Node<K: Ord, V: PartialEq> {
  pub key: K,
  pub value: V,
  pub count: u32,
  pub left: Tree<K, V>,
  pub right: Tree<K, V>,
}

impl<K: Ord, V: PartialEq> Node<K, V> {
  pub fn new(key: K, value: V) -> Self {
    Self {
      key,
      value,
      count: 0,
      left: None,
      right: None,
    }
  }

  pub fn is_leaf(&self) -> bool {
    self.left.is_none() && self.right.is_none()
  }

  pub fn smallest(&self) -> Option<&Self> {
    let mut cur = self;
    while let Some(ref node) = cur.left {
      cur = node.as_ref();
    }
    Some(cur)
  }

  pub fn smallest_mut(&mut self) -> Option<&mut Self> {
    let mut cur = self;
    while let Some(ref mut node) = cur.left {
      cur = node.as_mut();
    }
    Some(cur)
  }

  pub fn largest(&self) -> Option<&Self> {
    let mut cur = self;
    while let Some(ref node) = cur.right {
      cur = node.as_ref();
    }
    Some(cur)
  }

  pub fn largest_mut(&mut self) -> Option<&mut Self> {
    let mut cur = self;
    while let Some(ref mut node) = cur.right {
      cur = node.as_mut();
    }
    Some(cur)
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
