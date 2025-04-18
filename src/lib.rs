// Name: Dandy Arya Akbar
// NIM: 1313623028
// Class of: 2023
// Class Sector: A
// Subject: Algorithm Analysis and Design 122

pub mod rbtree_implementation {
    use std::rc::Rc;

    use std::cell::{Ref, RefCell};

    // use std::cmp::Ordering;

    // use std::fmt;

    #[derive(Clone, Copy, PartialEq, Debug)]
    pub enum Colour {
        Red,
        Black,
    }

    type Vertex = Rc<RefCell<RedBlackTreeNode>>;

    type OptionalVertex = Option<Vertex>;

    #[derive(Clone, Debug, PartialEq)]
    pub struct RedBlackTreeNode {
        pub(crate) colour: Colour,
        pub(crate) key: i32,
        pub(crate) parent: OptionalVertex,
        pub(crate) left: OptionalVertex,
        pub(crate) right: OptionalVertex,
    }

    impl RedBlackTreeNode {
        fn new(key: i32) -> Vertex {
            Rc::new(RefCell::new(RedBlackTreeNode {
                colour: Colour::Red,
                key,
                parent: None,
                left: None,
                right: None,
            }))
        }

        fn new_sentinel_nil() -> Vertex {
            Rc::new(RefCell::new(RedBlackTreeNode {
                colour: Colour::Black,
                key: i32::default(),
                parent: None,
                left: None,
                right: None,
            }))
        }

        /* fn is_sentinel_nil(node_opt: &OptionalVertex) -> bool {
            match node_opt {
                None => true,
                Some(node_rc) => {
                    let node = node_rc.borrow();
                    node.colour == Colour::Black
                        && node.parent.is_none()
                        && node.left.is_none()
                        && node.right.is_none()
                        && node.key == i32::default()
                }
            }
        } */

        /* fn get_key(&self) -> i32 {
            self.key
        } */

        /* fn set_key(&mut self, key: i32) {
            self.key = key;
        } */

        /* fn get_colour(&self) -> Colour {
            self.colour
        } */

        /* fn set_colour(&mut self, colour: Colour) {
            self.colour = colour;
        } */

        /* fn get_parent(&self) -> OptionalVertex {
            self.parent.clone()
        } */

        /* fn set_parent(&mut self, parent: OptionalVertex) {
            self.parent = parent;
        } */

        /* fn get_left_child(&self) -> OptionalVertex {
            self.left.clone()
        } */

        /* fn set_left_child(&mut self, left: OptionalVertex) {
            self.left = left;
        } */

        /* fn get_right_child(&self) -> OptionalVertex {
            self.right.clone()
        } */

        /* fn set_right_child(&mut self, right: OptionalVertex) {
            self.right = right;
        } */
    }

    #[derive(Debug)]
    pub struct RedBlackTree {
        pub(crate) root: OptionalVertex,
        pub(crate) sentinel_nil: Vertex,
    }

    fn clone_node(node: &Vertex) -> Vertex {
        Rc::clone(node)
    }

    fn clone_node_optional(node_optional: &OptionalVertex) -> OptionalVertex {
        node_optional.as_ref().map(clone_node)
    }

    impl RedBlackTree {
        pub fn new() -> Self {
            let sentinel_nil: Rc<RefCell<RedBlackTreeNode>> = RedBlackTreeNode::new_sentinel_nil();
            RedBlackTree {
                root: None,
                sentinel_nil: sentinel_nil,
            }
        }

        /* pub fn get_root(&self) -> OptionalVertex {
            self.root.clone()
        } */

        /* pub fn set_root(&mut self, root: OptionalVertex) {
            self.root = root;
        } */

        /* pub fn get_sentinel_nil(&self) -> Vertex {
            self.sentinel_nil.clone()
        } */

        /* pub fn set_sentinel_nil(&mut self, sentinel_nil: Vertex) {
            self.sentinel_nil = sentinel_nil;
        } */

        fn is_sentinel_nil(&self, node_optional: &OptionalVertex) -> bool {
            match node_optional {
                None => true,
                Some(node_rc) => Rc::ptr_eq(node_rc, &self.sentinel_nil),
            }
        }

        fn left_rotate(&mut self, x: Vertex) {
            let y: Option<Rc<RefCell<RedBlackTreeNode>>> = clone_node_optional(&x.borrow().right);
            if self.is_sentinel_nil(&y) {
                return;
            }
            let y_rc: Rc<RefCell<RedBlackTreeNode>> = y.unwrap();
            x.borrow_mut().right = clone_node_optional(&y_rc.borrow().left);
            if !self.is_sentinel_nil(&x.borrow().right) {
                x.borrow().right.as_ref().unwrap().borrow_mut().parent = Some(clone_node(&x));
            }
            y_rc.borrow_mut().parent = clone_node_optional(&x.borrow().parent);
            if self.is_sentinel_nil(&x.borrow().parent) {
                self.root = Some(clone_node(&y_rc));
            } else {
                let x_parent: Rc<RefCell<RedBlackTreeNode>> =
                    x.borrow().parent.as_ref().unwrap().clone();
                if Rc::ptr_eq(
                    &x,
                    &x_parent
                        .borrow()
                        .left
                        .as_ref()
                        .unwrap_or(&self.sentinel_nil),
                ) {
                    x_parent.borrow_mut().left = Some(clone_node(&y_rc));
                } else {
                    x_parent.borrow_mut().right = Some(clone_node(&y_rc));
                }
            }
            y_rc.borrow_mut().left = Some(clone_node(&x));
            x.borrow_mut().parent = Some(y_rc);
        }

        fn right_rotate(&mut self, y: Vertex) {
            let x: Option<Rc<RefCell<RedBlackTreeNode>>> = clone_node_optional(&y.borrow().left);
            if self.is_sentinel_nil(&x) {
                return;
            }
            let x_rc: Rc<RefCell<RedBlackTreeNode>> = x.unwrap();
            y.borrow_mut().left = clone_node_optional(&x_rc.borrow().right);
            if !self.is_sentinel_nil(&y.borrow().left) {
                y.borrow().left.as_ref().unwrap().borrow_mut().parent = Some(clone_node(&y));
            }
            x_rc.borrow_mut().parent = clone_node_optional(&y.borrow().parent);
            if self.is_sentinel_nil(&y.borrow().parent) {
                self.root = Some(clone_node(&x_rc));
            } else {
                let y_parent: Rc<RefCell<RedBlackTreeNode>> =
                    y.borrow().parent.as_ref().unwrap().clone();
                if Rc::ptr_eq(
                    &y,
                    &y_parent
                        .borrow()
                        .left
                        .as_ref()
                        .unwrap_or(&self.sentinel_nil),
                ) {
                    y_parent.borrow_mut().left = Some(clone_node(&x_rc));
                } else {
                    y_parent.borrow_mut().right = Some(clone_node(&x_rc));
                }
            }
            x_rc.borrow_mut().right = Some(clone_node(&y));
            y.borrow_mut().parent = Some(x_rc);
        }

        pub fn insert(&mut self, key: i32) {
            let z: Rc<RefCell<RedBlackTreeNode>> = RedBlackTreeNode::new(key);
            z.borrow_mut().left = Some(clone_node(&self.sentinel_nil));
            z.borrow_mut().right = Some(clone_node(&self.sentinel_nil));
            let mut y: OptionalVertex = None;
            let mut x: OptionalVertex = clone_node_optional(&self.root);
            while !self.is_sentinel_nil(&x) {
                y = clone_node_optional(&x);
                let x_rc: Rc<RefCell<RedBlackTreeNode>> = x.as_ref().unwrap().clone();
                if z.borrow().key < x_rc.borrow().key {
                    x = clone_node_optional(&x_rc.borrow().left);
                } else {
                    x = clone_node_optional(&x_rc.borrow().right);
                }
            }
            z.borrow_mut().parent = clone_node_optional(&y);
            if self.is_sentinel_nil(&y) {
                self.root = Some(clone_node(&z));
            } else {
                let y_rc: &Rc<RefCell<RedBlackTreeNode>> = y.as_ref().unwrap();
                if z.borrow().key < y_rc.borrow().key {
                    y_rc.borrow_mut().left = Some(clone_node(&z));
                } else {
                    y_rc.borrow_mut().right = Some(clone_node(&z));
                }
            }
            z.borrow_mut().left = Some(Rc::clone(&self.sentinel_nil));
            z.borrow_mut().right = Some(Rc::clone(&self.sentinel_nil));
            z.borrow_mut().colour = Colour::Red;
            self.insert_fixup(z);
        }

        fn insert_fixup(&mut self, z_arg: Vertex) {
            let mut z: Rc<RefCell<RedBlackTreeNode>> = z_arg;
            while z
                .borrow()
                .parent
                .as_ref()
                .map_or(false, |p: &Rc<RefCell<RedBlackTreeNode>>| {
                    p.borrow().colour == Colour::Red
                })
            {
                let z_parent: Rc<RefCell<RedBlackTreeNode>> =
                    z.borrow().parent.as_ref().unwrap().clone();
                let z_grandparent: Rc<RefCell<RedBlackTreeNode>> =
                    z_parent.borrow().parent.as_ref().unwrap().clone();
                if Rc::ptr_eq(
                    &z_parent,
                    &z_grandparent
                        .borrow()
                        .left
                        .as_ref()
                        .unwrap_or(&self.sentinel_nil),
                ) {
                    let y: Option<Rc<RefCell<RedBlackTreeNode>>> =
                        clone_node_optional(&z_grandparent.borrow().right);
                    if y.as_ref()
                        .map_or(false, |uncle: &Rc<RefCell<RedBlackTreeNode>>| {
                            uncle.borrow().colour == Colour::Red
                        })
                    {
                        z_parent.borrow_mut().colour = Colour::Black;
                        y.unwrap().borrow_mut().colour = Colour::Black;
                        z_grandparent.borrow_mut().colour = Colour::Red;
                        z = z_grandparent;
                    } else {
                        if Rc::ptr_eq(
                            &z,
                            &z_parent
                                .borrow()
                                .right
                                .as_ref()
                                .unwrap_or(&self.sentinel_nil),
                        ) {
                            z = z_parent;
                            self.left_rotate(clone_node(&z));
                        }
                        let z_parent_case3: Rc<RefCell<RedBlackTreeNode>> =
                            z.borrow().parent.as_ref().unwrap().clone();
                        let z_grandparent_case3: Rc<RefCell<RedBlackTreeNode>> =
                            z_parent_case3.borrow().parent.as_ref().unwrap().clone();
                        z_parent_case3.borrow_mut().colour = Colour::Black;
                        z_grandparent_case3.borrow_mut().colour = Colour::Red;
                        self.right_rotate(z_grandparent_case3);
                    }
                } else {
                    let y: Option<Rc<RefCell<RedBlackTreeNode>>> =
                        clone_node_optional(&z_grandparent.borrow().left);
                    if y.as_ref()
                        .map_or(false, |uncle: &Rc<RefCell<RedBlackTreeNode>>| {
                            uncle.borrow().colour == Colour::Red
                        })
                    {
                        z_parent.borrow_mut().colour = Colour::Black;
                        y.unwrap().borrow_mut().colour = Colour::Black;
                        z_grandparent.borrow_mut().colour = Colour::Red;
                        z = z_grandparent;
                    } else {
                        if Rc::ptr_eq(
                            &z,
                            &z_parent
                                .borrow()
                                .left
                                .as_ref()
                                .unwrap_or(&self.sentinel_nil),
                        ) {
                            z = z_parent;
                            self.right_rotate(clone_node(&z));
                        }
                        let z_parent_case3: Rc<RefCell<RedBlackTreeNode>> =
                            z.borrow().parent.as_ref().unwrap().clone();
                        let z_grandparent_case3: Rc<RefCell<RedBlackTreeNode>> =
                            z_parent_case3.borrow().parent.as_ref().unwrap().clone();
                        z_parent_case3.borrow_mut().colour = Colour::Black;
                        z_grandparent_case3.borrow_mut().colour = Colour::Red;
                        self.left_rotate(z_grandparent_case3);
                    }
                }
                if self.is_sentinel_nil(&z.borrow().parent) {
                    break;
                }
            }
            if let Some(root_rc) = &self.root {
                root_rc.borrow_mut().colour = Colour::Black;
            }
        }

        fn minimum(&self, x_optional: &OptionalVertex) -> OptionalVertex {
            if self.is_sentinel_nil(x_optional) {
                return None;
            }
            let mut current: Rc<RefCell<RedBlackTreeNode>> = x_optional.as_ref().unwrap().clone();
            while !self.is_sentinel_nil(&current.borrow().left) {
                let next: Rc<RefCell<RedBlackTreeNode>> =
                    current.borrow().left.as_ref().unwrap().clone();
                current = next;
            }
            Some(current)
        }

        fn maximum(&self, x_optional: &OptionalVertex) -> OptionalVertex {
            if self.is_sentinel_nil(x_optional) {
                return None;
            }
            let mut current = x_optional.as_ref().unwrap().clone();
            while !self.is_sentinel_nil(&current.borrow().right) {
                let next = current.borrow().right.as_ref().unwrap().clone();
                current = next;
            }
            Some(current)
        }

        fn transplant(&mut self, u: Vertex, v: OptionalVertex) {
            if self.is_sentinel_nil(&u.borrow().parent) {
                self.root = v.clone();
            } else {
                let u_parent: Rc<RefCell<RedBlackTreeNode>> =
                    u.borrow().parent.as_ref().unwrap().clone();
                let is_left_child = Rc::ptr_eq(
                    &u,
                    &u_parent
                        .borrow()
                        .left
                        .as_ref()
                        .unwrap_or(&self.sentinel_nil),
                );
                if is_left_child {
                    u_parent.borrow_mut().left = v.clone();
                } else {
                    u_parent.borrow_mut().right = v.clone();
                }
            }
            if let Some(v_rc) = &v {
                v_rc.borrow_mut().parent = clone_node_optional(&u.borrow().parent);
            }
        }

        pub fn delete(&mut self, z: Vertex) {
            let mut y: Rc<RefCell<RedBlackTreeNode>> = clone_node(&z);
            let mut y_original_colour: Colour = y.borrow().colour;
            let /* mut */ x: OptionalVertex;
            if self.is_sentinel_nil(&z.borrow().left) {
                x = clone_node_optional(&z.borrow().right);
                self.transplant(clone_node(&z), clone_node_optional(&z.borrow().right));
            } else if self.is_sentinel_nil(&z.borrow().right) {
                x = clone_node_optional(&z.borrow().left);
                self.transplant(clone_node(&z), clone_node_optional(&z.borrow().left));
            } else {
                y = self.minimum(&z.borrow().right).unwrap();
                y_original_colour = y.borrow().colour;
                x = clone_node_optional(&y.borrow().right);
                if y.borrow()
                    .parent
                    .as_ref()
                    .map_or(false, |p: &Rc<RefCell<RedBlackTreeNode>>| Rc::ptr_eq(p, &z))
                {
                    if let Some(x_rc) = &x {
                        x_rc.borrow_mut().parent = Some(clone_node(&y));
                    }
                } else {
                    self.transplant(clone_node(&y), clone_node_optional(&y.borrow().right));
                    y.borrow_mut().right = clone_node_optional(&z.borrow().right);
                    y.borrow().right.as_ref().unwrap().borrow_mut().parent = Some(clone_node(&y));
                }
                self.transplant(clone_node(&z), Some(clone_node(&y)));
                y.borrow_mut().left = clone_node_optional(&z.borrow().left);
                y.borrow().left.as_ref().unwrap().borrow_mut().parent = Some(clone_node(&y));
                y.borrow_mut().colour = z.borrow().colour;
            }
            if y_original_colour == Colour::Black {
                let x_parent: Option<Rc<RefCell<RedBlackTreeNode>>> = if let Some(x_rc) = &x {
                    clone_node_optional(&x_rc.borrow().parent)
                } else {
                    if y.borrow()
                        .parent
                        .as_ref()
                        .map_or(false, |p: &Rc<RefCell<RedBlackTreeNode>>| Rc::ptr_eq(p, &z))
                    {
                        Some(clone_node(&y))
                    } else {
                        clone_node_optional(&y.borrow().parent)
                    }
                };
                self.delete_fixup(x, x_parent);
            }
        }

        fn delete_fixup(&mut self, mut x: OptionalVertex, mut x_parent: OptionalVertex) {
            while x != self.root
                && x.as_ref()
                    .map_or(true, |n: &Rc<RefCell<RedBlackTreeNode>>| {
                        n.borrow().colour == Colour::Black
                    })
            {
                let parent: Option<Rc<RefCell<RedBlackTreeNode>>> = clone_node_optional(&x_parent);
                let p_rc: Rc<RefCell<RedBlackTreeNode>> = parent.as_ref().unwrap().clone();
                let x_is_left_child = match (&p_rc.borrow().left, &x) {
                    (Some(left_rc), Some(x_rc)) => Rc::ptr_eq(left_rc, x_rc),
                    (None, None) => true,
                    (Some(_), None) => self.is_sentinel_nil(&p_rc.borrow().left),
                    _ => false,
                };
                if x_is_left_child {
                    let mut w: Option<Rc<RefCell<RedBlackTreeNode>>> =
                        clone_node_optional(&p_rc.borrow().right);
                    if w.as_ref()
                        .map_or(false, |n: &Rc<RefCell<RedBlackTreeNode>>| {
                            n.borrow().colour == Colour::Red
                        })
                    {
                        w.as_ref().unwrap().borrow_mut().colour = Colour::Black;
                        p_rc.borrow_mut().colour = Colour::Red;
                        self.left_rotate(clone_node(&p_rc));
                        w = clone_node_optional(&p_rc.borrow().right);
                    }
                    let w_rc: Rc<RefCell<RedBlackTreeNode>> =
                        w.as_ref().unwrap_or(&self.sentinel_nil).clone();
                    let w_left_is_black = w_rc
                        .borrow()
                        .left
                        .as_ref()
                        .map_or(true, |c: &Rc<RefCell<RedBlackTreeNode>>| {
                            c.borrow().colour == Colour::Black
                        });
                    let w_right_is_black = w_rc
                        .borrow()
                        .right
                        .as_ref()
                        .map_or(true, |c: &Rc<RefCell<RedBlackTreeNode>>| {
                            c.borrow().colour == Colour::Black
                        });
                    if w_left_is_black && w_right_is_black {
                        w_rc.borrow_mut().colour = Colour::Red;
                        x = clone_node_optional(&parent);
                        x_parent = clone_node_optional(&x.as_ref().and_then(
                            |n: &Rc<RefCell<RedBlackTreeNode>>| n.borrow().parent.clone(),
                        ));
                    } else {
                        if w_right_is_black {
                            if let Some(w_left) = &w_rc.borrow().left {
                                w_left.borrow_mut().colour = Colour::Black;
                            }
                            w_rc.borrow_mut().colour = Colour::Red;
                            self.right_rotate(clone_node(&w_rc));
                            w = clone_node_optional(&p_rc.borrow().right);
                        }
                        let new_w_rc: &Rc<RefCell<RedBlackTreeNode>> = w.as_ref().unwrap();
                        new_w_rc.borrow_mut().colour = p_rc.borrow().colour;
                        p_rc.borrow_mut().colour = Colour::Black;
                        if let Some(w_right) = &new_w_rc.borrow().right {
                            w_right.borrow_mut().colour = Colour::Black;
                        }
                        self.left_rotate(clone_node(&p_rc));
                        x = clone_node_optional(&self.root);
                        x_parent = None;
                    }
                } else {
                    let mut w: Option<Rc<RefCell<RedBlackTreeNode>>> =
                        clone_node_optional(&p_rc.borrow().left);
                    if w.as_ref()
                        .map_or(false, |n: &Rc<RefCell<RedBlackTreeNode>>| {
                            n.borrow().colour == Colour::Red
                        })
                    {
                        w.as_ref().unwrap().borrow_mut().colour = Colour::Black;
                        p_rc.borrow_mut().colour = Colour::Red;
                        self.right_rotate(clone_node(&p_rc));
                        w = clone_node_optional(&p_rc.borrow().left);
                    }
                    let w_rc: Rc<RefCell<RedBlackTreeNode>> =
                        w.as_ref().unwrap_or(&self.sentinel_nil).clone();
                    let w_left_is_black = w_rc
                        .borrow()
                        .left
                        .as_ref()
                        .map_or(true, |c: &Rc<RefCell<RedBlackTreeNode>>| {
                            c.borrow().colour == Colour::Black
                        });
                    let w_right_is_black = w_rc
                        .borrow()
                        .right
                        .as_ref()
                        .map_or(true, |c: &Rc<RefCell<RedBlackTreeNode>>| {
                            c.borrow().colour == Colour::Black
                        });
                    if w_left_is_black && w_right_is_black {
                        w_rc.borrow_mut().colour = Colour::Red;
                        x = clone_node_optional(&parent);
                        x_parent = clone_node_optional(&x.as_ref().and_then(
                            |n: &Rc<RefCell<RedBlackTreeNode>>| n.borrow().parent.clone(),
                        ));
                    } else {
                        if w_left_is_black {
                            if let Some(w_right) = &w_rc.borrow().right {
                                w_right.borrow_mut().colour = Colour::Black;
                            }
                            w_rc.borrow_mut().colour = Colour::Red;
                            self.left_rotate(clone_node(&w_rc));
                            w = clone_node_optional(&p_rc.borrow().left);
                        }
                        let new_w_rc: &Rc<RefCell<RedBlackTreeNode>> = w.as_ref().unwrap();
                        new_w_rc.borrow_mut().colour = p_rc.borrow().colour;
                        p_rc.borrow_mut().colour = Colour::Black;
                        if let Some(w_left) = &new_w_rc.borrow().left {
                            w_left.borrow_mut().colour = Colour::Black;
                        }
                        self.right_rotate(clone_node(&p_rc));
                        x = clone_node_optional(&self.root);
                        x_parent = None;
                    }
                }
            }
            if let Some(x_rc) = x {
                x_rc.borrow_mut().colour = Colour::Black;
            }
        }

        pub fn search(&self, key: i32) -> OptionalVertex {
            let mut current: Option<Rc<RefCell<RedBlackTreeNode>>> =
                clone_node_optional(&self.root);
            while !self.is_sentinel_nil(&current) {
                let current_rc: Rc<RefCell<RedBlackTreeNode>> = current.as_ref().unwrap().clone();
                let current_key: i32 = current_rc.borrow().key;
                if key == current_key {
                    return Some(current_rc);
                } else if key < current_key {
                    current = clone_node_optional(&current_rc.borrow().left);
                } else {
                    current = clone_node_optional(&current_rc.borrow().right);
                }
            }
            None
        }

        pub fn successor(&self, x_optional_reference: &OptionalVertex) -> OptionalVertex {
            if self.is_sentinel_nil(x_optional_reference) {
                return None;
            }
            let x_rc: &Rc<RefCell<RedBlackTreeNode>> = x_optional_reference.as_ref().unwrap();
            let x_right_child: Option<Rc<RefCell<RedBlackTreeNode>>> =
                clone_node_optional(&x_rc.borrow().right);
            if !self.is_sentinel_nil(&x_right_child) {
                return self.minimum(&x_right_child);
            }
            let mut current_x_node_optional: OptionalVertex = x_optional_reference.clone();
            let mut y_optional: OptionalVertex = clone_node_optional(&x_rc.borrow().parent);
            while !self.is_sentinel_nil(&y_optional) {
                let y_rc: Rc<RefCell<RedBlackTreeNode>> = y_optional.as_ref().unwrap().clone();
                let y_right_child_optional: Option<Rc<RefCell<RedBlackTreeNode>>> =
                    clone_node_optional(&y_rc.borrow().right);
                let x_is_y_right_child = match (&current_x_node_optional, &y_right_child_optional) {
                    (Some(current_rc), Some(y_right_rc)) => Rc::ptr_eq(current_rc, y_right_rc),
                    _ => false,
                };
                if x_is_y_right_child {
                    current_x_node_optional = y_optional.clone();
                    y_optional = clone_node_optional(&y_rc.borrow().parent);
                } else {
                    break;
                }
            }
            return y_optional;
        }

        pub fn predecessor(&self, x_optional_reference: &OptionalVertex) -> OptionalVertex {
            if self.is_sentinel_nil(x_optional_reference) {
                return None;
            }
            let x_rc: &Rc<RefCell<RedBlackTreeNode>> = x_optional_reference.as_ref().unwrap();
            let x_left_child: Option<Rc<RefCell<RedBlackTreeNode>>> =
                clone_node_optional(&x_rc.borrow().left);
            if !self.is_sentinel_nil(&x_left_child) {
                return self.maximum(&x_left_child);
            }
            let mut current_x_node_optional: OptionalVertex = x_optional_reference.clone();
            let mut y_optional: OptionalVertex = clone_node_optional(&x_rc.borrow().parent);
            while !self.is_sentinel_nil(&y_optional) {
                let y_rc: Rc<RefCell<RedBlackTreeNode>> = y_optional.as_ref().unwrap().clone();
                let y_left_child_optional: Option<Rc<RefCell<RedBlackTreeNode>>> =
                    clone_node_optional(&y_rc.borrow().left);
                let x_is_y_left_child = match (&current_x_node_optional, &y_left_child_optional) {
                    (Some(current_rc), Some(y_left_rc)) => Rc::ptr_eq(current_rc, y_left_rc),
                    _ => false,
                };
                if x_is_y_left_child {
                    current_x_node_optional = y_optional.clone();
                    y_optional = clone_node_optional(&y_rc.borrow().parent);
                } else {
                    break;
                }
            }
            return y_optional;
        }

        fn print_preorder(&self, node_optional: &OptionalVertex) {
            if self.is_sentinel_nil(node_optional) {
                return;
            }
            let node_rc: &Rc<RefCell<RedBlackTreeNode>> = node_optional.as_ref().unwrap();
            println!(
                "Key: {}, Colour: {:?}",
                node_rc.borrow().key,
                node_rc.borrow().colour
            );
            self.print_preorder(&node_rc.borrow().left);
            self.print_preorder(&node_rc.borrow().right);
        }

        fn print_inorder(&self, node_optional: &OptionalVertex) {
            if self.is_sentinel_nil(node_optional) {
                return;
            }
            let node_rc: &Rc<RefCell<RedBlackTreeNode>> = node_optional.as_ref().unwrap();
            self.print_inorder(&node_rc.borrow().left);
            println!(
                "Key: {}, Colour: {:?}",
                node_rc.borrow().key,
                node_rc.borrow().colour,
            );
            self.print_inorder(&node_rc.borrow().right);
        }

        fn print_postorder(&self, node_optional: &OptionalVertex) {
            if self.is_sentinel_nil(node_optional) {
                return;
            }
            let node_rc: &Rc<RefCell<RedBlackTreeNode>> = node_optional.as_ref().unwrap();
            self.print_postorder(&node_rc.borrow().left);
            self.print_postorder(&node_rc.borrow().right);
            println!(
                "Key: {}, Colour: {:?}",
                node_rc.borrow().key,
                node_rc.borrow().colour
            );
        }

        pub fn print_tree(&self, order: &str) {
            if self.is_sentinel_nil(&self.root) {
                println!("The Red-Black Tree is currently empty. Nothing to print.");
                return;
            }
            let valid_orders: [&str; 3] = ["preorder", "inorder", "postorder"];
            if !valid_orders.contains(&order) {
                println!(
                    "Invalid order specified. You can only use either 'preorder', 'inorder', or 'postorder'."
                );
                return;
            }
            match order {
                "preorder" => {
                    println!("--- Red Black Tree (Pre-Order Traversal) ---:");
                    self.print_preorder(&self.root);
                }
                "inorder" => {
                    println!("--- Red Black Tree (In-Order Traversal) ---:");
                    self.print_inorder(&self.root);
                }
                "postorder" => {
                    println!("--- Red Black Tree (Post-Order Traversal) ---:");
                    self.print_postorder(&self.root);
                }
                _ => unreachable!(),
            }
            println!("--- End of the Red Black Tree ---");
        }

        pub fn pretty_print_tree(&self) {
            println!("--- Current State of the Red Black Tree (Pretty-Print Style) ---");
            self.pretty_print_tree_internal(&self.root, 0);
            println!("--- End of the Pretty-Print of the Red Black Tree ---");
        }

        fn pretty_print_tree_internal(&self, node: &OptionalVertex, indent: usize) {
            if self.is_sentinel_nil(node) {
                println!("{} - NIL", " ".repeat(indent));
                return;
            }
            let node_rc: &Rc<RefCell<RedBlackTreeNode>> = node.as_ref().unwrap();
            let n: Ref<'_, RedBlackTreeNode> = node_rc.borrow();
            println!(
                "{} - Key: {}, Colour: {:?}",
                " ".repeat(indent),
                n.key,
                n.colour
            );
            self.pretty_print_tree_internal(&n.left, indent + 4);
            self.pretty_print_tree_internal(&n.right, indent + 4);
        }
    }
}
