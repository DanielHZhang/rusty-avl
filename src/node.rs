use std::cmp::Ordering;
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
      let a = node.as_ref();
      cur = a;
    }
    Some(cur)
  }

  pub fn smallest_mut(&mut self) -> Option<&mut Self> {
    let mut cur = self;
    while let Some(ref mut node) = cur.left {
      let a = node.as_mut();
      cur = a;
    }
    Some(cur)
  }
}

pub trait NodeOption<K: Ord, V: PartialEq> {
  fn get(&self, key: K) -> Option<&Node<K, V>>;
  fn extract_min(&mut self) -> Self;
  fn extract_max(&mut self) -> Self;
}

impl<K: Ord, V: PartialEq> NodeOption<K, V> for Option<Box<Node<K, V>>> {
  fn get(&self, key: K) -> Option<&Node<K, V>> {
    let mut current = self;
    while let Some(node) = current {
      match &key.cmp(&node.key) {
        Ordering::Less => current = &node.left,
        Ordering::Greater => current = &node.right,
        Ordering::Equal => break,
      }
    }
    current.as_deref()
  }

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

  // pub fn get_mut(&mut self, key: K) -> Option<&mut Node<K, V>> {
  // 	None
  // }

  // pub fn get_mut(&mut self, key: K) -> Option<&mut Self> {
  // 	if key < self.key {
  // 		match self.left.as_deref_mut() {
  // 			None => None,
  // 			Some(node) => node.get_mut(key),
  // 		}
  // 	} else if key > self.key {
  // 		match self.right.as_deref_mut() {
  // 			None => None,
  // 			Some(node) => node.get_mut(key),
  // 		}
  // 	} else {
  // 		Some(self)
  // 	}
  // }

  // while cur.is_some() {
  //   let node = cur.unwrap();
  //   if key < node.key {
  //     cur = &mut node.left;
  //   } else if key > node.key {
  //     cur = &mut node.right;
  //   } else {
  //     cur = &mut Some(node);
  //   }
  // }
  // if cur.is_none() {
  //   *cur = Some(Box::new(Node::new(key, value)));
  //   //
  //   // cur.replace(Box::new(Node::new(key, value)));
  // }

  // let mut current = self.as_deref_mut();
  // while let Some(node) = current {
  //   match &key.cmp(&node.key) {
  //     Ordering::Less => {
  //       let w = node.left.as_deref_mut();
  //       current = w;
  //     }
  //     Ordering::Greater => current = node.right.as_deref_mut(),
  //     Ordering::Equal => {
  //       current = Some(node);
  //       // node.count += 1;
  //       // if node.key == key {
  //       //   node.count += 1;
  //       // }
  //       break;
  //     }
  //   }
  // }
  // if current.is_none() {
  //   ()
  // }
  // let w = current;
  // it = Some(Box::new(Node::new(key, value)));

  // match self {
  //   None => *self = Some(Box::new(Node::new(key, value))),
  //   Some(node) => {
  //     let mut current = node;
  //   }
  // }
  // let mut next = self.as_mut().unwrap();
  // loop {
  //   // let current = &next;
  //   if key < next.key {
  //     let l = next.left.as_mut();
  //   } else if key > next.key {
  //     let r = next.right.as_mut().unwrap();
  //     next = r;
  //   } else {
  //     if value == next.value {
  //       next.count += 1;
  //     } else {
  //       // return None;
  //       return;
  //     }
  //   }
  // }
}

// pub fn delete(&mut self, key: K) -> Option<Self> {
// 	if key < self.key {
// 		match self.left.as_deref() {
// 			None => None,
// 			Some(node) => {}
// 		}
// 	} else if key > self.key {
// 	} else {
// 		if self.count > 1 {
// 			self.count -= 1;
// 			None
// 		}
// 	}
// }
