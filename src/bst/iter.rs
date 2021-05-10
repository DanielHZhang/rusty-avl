use super::node::Node;
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
    let top = self.stack.pop();
    match top {
      None => None,
      Some(node) => {
        if let Some(right) = node.right.as_deref() {
          self.stack.push(right);
        }
        if let Some(left) = node.left.as_deref() {
          self.stack.push(left);
        }
        Some(node)
      }
    }
  }
}

struct NodeInorderIter<'a, K: Ord, V: PartialEq> {
  stack: Vec<&'a Node<K, V>>,
  current: Option<&'a Node<K, V>>,
}

impl<'a, K: Ord, V: PartialEq> NodeInorderIter<'a, K, V> {
  pub fn new(root: Option<&'a Node<K, V>>) -> Self {
    NodeInorderIter {
      stack: Vec::new(),
      current: root,
    }
  }
}

impl<'a, K: Ord, V: PartialEq> Iterator for NodeInorderIter<'a, K, V> {
  type Item = &'a Node<K, V>;

  fn next(&mut self) -> Option<Self::Item> {
    match self.current {
      None => match self.stack.pop() {
        None => None,
        Some(node) => {
          self.current = node.right.as_deref();
          Some(node)
        }
      },
      Some(mut cur) => loop {
        match cur.left.as_deref() {
          None => {
            self.current = cur.right.as_deref();
            return Some(cur);
          }
          Some(left) => {
            self.stack.push(cur);
            cur = left;
          }
        }
      },
    }
  }
}
