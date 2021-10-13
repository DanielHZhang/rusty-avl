use super::Node;

pub struct IterPreorder<'a, K: Ord, V: PartialEq> {
  stack: Vec<&'a Node<K, V>>,
}

impl<K: Ord, V: PartialEq> Default for IterPreorder<'_, K, V> {
  fn default() -> Self {
    IterPreorder { stack: Vec::new() }
  }
}

impl<'a, K: Ord, V: PartialEq> IterPreorder<'a, K, V> {
  pub fn new(root: Option<&'a Node<K, V>>) -> Self {
    match root {
      Some(node) => IterPreorder {
        stack: Vec::from([node]),
      },
      None => Self::default(),
    }
  }
}

impl<'a, K: Ord, V: PartialEq> Iterator for IterPreorder<'a, K, V> {
  type Item = &'a Node<K, V>;

  fn next(&mut self) -> Option<Self::Item> {
    self
      .stack
      .pop()
      .map(|node| {
        if let Some(right) = node.right.as_deref() {
          self.stack.push(right);
        }
        if let Some(left) = node.left.as_deref() {
          self.stack.push(left);
        }
        Some(node)
      })
      .unwrap_or(None)
  }
}

pub struct IterInorder<'a, K: Ord, V: PartialEq> {
  stack: Vec<&'a Node<K, V>>,
  current: Option<&'a Node<K, V>>,
}

impl<K: Ord, V: PartialEq> Default for IterInorder<'_, K, V> {
  fn default() -> Self {
    IterInorder {
      stack: Vec::new(),
      current: None,
    }
  }
}

impl<'a, K: Ord, V: PartialEq> IterInorder<'a, K, V> {
  pub fn new(root: Option<&'a Node<K, V>>) -> Self {
    IterInorder {
      stack: Vec::new(),
      current: root,
    }
  }
}

impl<'a, K: Ord, V: PartialEq> Iterator for IterInorder<'a, K, V> {
  type Item = &'a Node<K, V>;

  fn next(&mut self) -> Option<Self::Item> {
    match self.current {
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
      None => self
        .stack
        .pop()
        .map(|node| {
          self.current = node.right.as_deref();
          Some(node)
        })
        .unwrap_or(None),
    }
  }
}

pub struct IterPostorder<'a, K: Ord, V: PartialEq> {
  stack: Vec<&'a Node<K, V>>,
  current: Option<&'a Node<K, V>>,
}

impl<K: Ord, V: PartialEq> Default for IterPostorder<'_, K, V> {
  fn default() -> Self {
    IterPostorder {
      stack: Vec::new(),
      current: None,
    }
  }
}

impl<'a, K: Ord, V: PartialEq> IterPostorder<'a, K, V> {
  pub fn new(root: Option<&'a Node<K, V>>) -> Self {
    match root {
      None => Self::default(),
      Some(node) => Self {
        stack: Vec::from([node]),
        current: root,
      },
    }
  }
}

impl<'a, K: std::fmt::Debug + Ord, V: PartialEq> Iterator for IterPostorder<'a, K, V> {
  type Item = &'a Node<K, V>;

  fn next(&mut self) -> Option<Self::Item> {
    self
      .current
      .map(|node| {
        while let Some(top) = self.stack.pop() {
          let finished_subtrees = match (top.right.as_deref(), top.left.as_deref()) {
            (None, None) => false,
            (None, Some(left)) => left.key == node.key,
            (Some(right), None) => right.key == node.key,
            (Some(right), Some(left)) => right.key == node.key || left.key == node.key,
          };
          if finished_subtrees || top.is_leaf() {
            self.current = Some(top);
            return Some(top);
          } else {
            self.stack.push(top);
            if let Some(right) = top.right.as_deref() {
              self.stack.push(right);
            }
            if let Some(left) = top.left.as_deref() {
              self.stack.push(left);
            }
          }
        }
        None
      })
      .unwrap_or(None)
  }
}

#[cfg(test)]
mod test {
  use crate::AvlTree;

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
