use std::{mem, ptr};

pub struct List<T> {
    head: Link<T>,
    tail: *mut Node<T>,
}

type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug, PartialEq)]
pub struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        List {
            head: None,
            tail: ptr::null_mut(),
        }
    }

    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|head| {
            let head = *head;
            self.head = head.next;

            if self.head.is_none() {
                self.tail = ptr::null_mut();
            }

            head.elem
        })
    }

    pub fn push(&mut self, elem: T) {
        let mut new_tail = Box::new(Node { elem, next: None });

        let raw_tail: *mut _ = &mut *new_tail;

        if !self.tail.is_null() {
            unsafe {
                (*self.tail).next = Some(new_tail);
            }
        } else {
            self.head = Some(new_tail);
        }

        self.tail = raw_tail;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let tut = List::<i32>::new();

        assert_eq!(tut.head, None)
    }

    #[test]
    fn push_pop() {
        let mut tut = List::<i32>::new();
        assert_eq!(tut.pop(), None);

        tut.push(1);
        tut.push(2);
        tut.push(3);
        tut.push(4);

        assert_eq!(tut.pop(), Some(1));
        assert_eq!(tut.pop(), Some(2));

        tut.push(5);
        tut.push(6);

        assert_eq!(tut.pop(), Some(3));
        assert_eq!(tut.pop(), Some(4));
        assert_eq!(tut.pop(), Some(5));
        assert_eq!(tut.pop(), Some(6));
        assert_eq!(tut.pop(), None);

        tut.push(7);
        tut.push(8);

        assert_eq!(tut.pop(), Some(7));
        assert_eq!(tut.pop(), Some(8));
        assert_eq!(tut.pop(), None);
    }
}
