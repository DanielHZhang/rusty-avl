pub struct Tree<T> {
  root: Link<T>,
  size: usize,
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
  elem: T,
  left: Link<T>,
  right: Link<T>,
}

impl<T> Node<T> {
  fn new(elem: T) -> Self {
    Node {
      elem: elem,
      left: None,
      right: None,
    }
  }
}

impl<T: Ord> Tree<T> {
  pub fn new() -> Self {
    Tree {
      root: None,
      size: 0,
    }
  }

  pub fn insert(&mut self, elem: T) {
    match self.root.as_mut() {
      None => {
        self.root = Some(Box::new(Node::new(elem)));
        self.size = 1;
      }
      // it seems the scope of match is a little weird, we can not bind
      // anything inside `Some`, otherwise compiler would forbid
      // assigning new node to self.root in None branch
      Some(_) => {
        let mut next = self.root.as_mut().unwrap();
        loop {
          // it seems borrow checker is not smart enough, so we
          // have to use different variable name
          let cur = next;
          let target = {
            let elem_ref = &elem;
            if cur.elem == *elem_ref {
              return;
            }
            if cur.elem < *elem_ref {
              &mut cur.right
            } else {
              &mut cur.left
            }
          };
          if target.is_some() {
            next = target.as_mut().unwrap();
            continue;
          }
          *target = Some(Box::new(Node::new(elem)));
          self.size += 1;
          return;
        }
      }
    }
  }

  // This is recursive fn, be careful with stack overflow, we can use threaded
  // tree traversal to avoid that, but since we are using Box instead of Rc,
  // we can't do it. Or we can use unsafe code to do it.
  fn iter<'a, 'b>(node: Option<&'a Box<Node<T>>>, vec: &'b mut Vec<&'a T>) {
    node.map(|node| {
      let node: &Node<T> = &**node;
      Tree::iter(node.left.as_ref(), vec);
      vec.push(&node.elem);
      Tree::iter(node.right.as_ref(), vec);
    });
  }

  pub fn into_vec(&self) -> Vec<&T> {
    let mut result = Vec::with_capacity(self.size);
    Tree::iter(self.root.as_ref(), &mut result);
    result
  }
}

#[cfg(test)]
mod test {
  use tree::Tree;

  #[test]
  fn it_works() {
    let mut tree = Tree::new();
    tree.insert(3);
    tree.insert(1);
    tree.insert(2);

    assert_eq!(tree.size, 3);
    assert_eq!(tree.into_vec(), vec![&1, &2, &3]);
  }
}
