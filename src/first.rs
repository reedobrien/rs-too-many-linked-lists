use std::{boxed::Box, mem};

#[derive(Debug, PartialEq, PartialOrd)]
pub struct List {
    head: Link,
}

impl Drop for List {
    fn drop(&mut self) {
        let mut cur_link = mem::replace(&mut self.head, Link::Empty);

        while let Link::More(mut boxed_node) = cur_link {
            cur_link = mem::replace(&mut boxed_node.next, Link::Empty);
        }
    }
}

impl List {
    fn new() -> Self {
        List { head: Link::Empty }
    }

    fn push(&mut self, elem: i32) {
        let n = Box::new(Node {
            elem,
            next: mem::replace(&mut self.head, Link::Empty),
        });
        self.head = Link::More(n);
    }

    fn pop(&mut self) -> Option<i32> {
        match mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(node) => {
                self.head = node.next;
                Some(node.elem)
            }
        }
    }
}

#[derive(Debug, PartialEq, PartialOrd)]
enum Link {
    Empty,
    More(Box<Node>),
}

#[derive(Debug, PartialEq, PartialOrd)]
struct Node {
    elem: i32,
    next: Link,
}

#[cfg(test)]
mod unit {
    use super::*;

    #[test]
    fn test_new() {
        let tut = List::new();

        assert_eq!(tut.head, Link::Empty);
    }

    #[test]
    fn test_push() {
        let mut tut = List::new();

        tut.push(5);

        assert_eq!(
            tut.head,
            Link::More(Box::new(Node {
                elem: 5,
                next: Link::Empty
            }))
        );
    }

    #[test]
    fn test_pop() {
        let mut tut = List::new();
        tut.push(5);
        let got = tut.pop();
        assert_eq!(got, Some(5));
        assert_eq!(tut.head, Link::Empty);
    }

    #[test]
    fn push_many_pop_many() {
        let mut tut = List::new();

        tut.push(1);
        tut.push(2);
        tut.push(3);

        assert_eq!(tut.pop(), Some(3));
        assert_eq!(tut.pop(), Some(2));

        tut.push(4);
        tut.push(5);

        assert_eq!(tut.pop(), Some(5));
        assert_eq!(tut.pop(), Some(4));
        assert_eq!(tut.pop(), Some(1));
        assert_eq!(tut.pop(), None);
        assert_eq!(tut.pop(), None);
        assert_eq!(tut.pop(), None);
    }
}
