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

  // pub fn iter(&self) -> NodePreorderIter<K, V> {
  //   NodePreorderIter(self)
  // }
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

pub struct NodePreorderIter<'a, K: Ord, V: PartialEq> {
  stack: Vec<&'a Node<K, V>>,
}

impl<'a, K: Ord, V: PartialEq> NodePreorderIter<'a, K, V> {
  pub fn new(root: Option<&'a Node<K, V>>) -> Self {
    match root {
      None => NodePreorderIter::default(),
      Some(node) => NodePreorderIter {
        stack: Vec::from([node]),
      },
    }
  }
}

impl<K: Ord, V: PartialEq> Default for NodePreorderIter<'_, K, V> {
  fn default() -> Self {
    NodePreorderIter { stack: Vec::new() }
  }
}

impl<'a, K: Ord, V: PartialEq> Iterator for NodePreorderIter<'a, K, V> {
  type Item = &'a Node<K, V>;

  fn next(&mut self) -> Option<Self::Item> {
    // match self.stack
    None
  }
}

struct NodeInorderIter<'a, K: Ord, V: PartialEq>(&'a Node<K, V>);
