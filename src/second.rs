use std::boxed::Box;

#[derive(Debug, PartialEq, PartialOrd)]
pub struct List<T> {
    head: Link<T>,
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut cur_link = self.head.take();

        while let Some(mut boxed_node) = cur_link {
            cur_link = boxed_node.next.take();
        }
    }
}

pub struct IntoIter<T>(List<T>);

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}

pub struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_deref();
            &node.elem
        })
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|node| {
            self.next = node.next.as_deref_mut();
            &mut node.elem
        })
    }
}

impl<T> List<T> {
    fn new() -> Self {
        List { head: None }
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_deref(),
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            next: self.head.as_deref_mut(),
        }
    }
    fn peek(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    fn peek_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| &mut node.elem)
    }

    fn push(&mut self, elem: T) {
        let node = Box::new(Node {
            elem,
            next: self.head.take(),
        });
        self.head = Some(node);
    }

    fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.elem
        })
    }
}

type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug, PartialEq, PartialOrd)]
struct Node<T> {
    elem: T,
    next: Link<T>,
}

#[cfg(test)]
mod unit {
    use super::*;

    #[test]
    fn test_new() {
        let tut: List<i32> = List::new();

        assert_eq!(tut.head, None);
    }

    #[test]
    fn test_push() {
        let mut tut = List::new();

        tut.push(5);

        assert_eq!(
            tut.head,
            Some(Box::new(Node {
                elem: 5,
                next: None
            }))
        );
    }

    #[test]
    fn test_pop() {
        let mut tut = List::new();
        tut.push(5);
        let got = tut.pop();
        assert_eq!(got, Some(5));
        assert_eq!(tut.head, None);
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

    #[test]
    fn test_peek() {
        let mut list = List::new();

        assert_eq!(list.peek(), None);
        assert_eq!(list.peek_mut(), None);

        list.push(1);
        list.push(2);
        list.push(3);
        assert_eq!(list.peek(), Some(&3));
        assert_eq!(list.peek_mut(), Some(&mut 3));

        list.peek_mut().map(|value| *value = 42);

        assert_eq!(list.peek(), Some(&42));
        assert_eq!(list.pop(), Some(42));
    }

    #[test]
    fn test_into_iter() {
        let mut tut = List::<i32>::new();

        tut.push(1);
        tut.push(2);
        tut.push(3);

        let mut iter = tut.into_iter();
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter() {
        let mut tut = List::<u32>::new();
        tut.push(1);
        tut.push(2);
        tut.push(3);
        tut.push(4);

        let mut it = tut.iter();
        assert_eq!(it.next(), Some(&4));
        assert_eq!(it.next(), Some(&3));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.next(), Some(&1));
    }

    #[test]
    fn test_iter_mut() {
        let mut tut = List::<u32>::new();
        tut.push(1);
        tut.push(2);
        tut.push(3);
        tut.push(4);

        let mut it = tut.iter_mut();

        assert_eq!(it.next(), Some(&mut 4));
        assert_eq!(it.next(), Some(&mut 3));
        assert_eq!(it.next(), Some(&mut 2));
        assert_eq!(it.next(), Some(&mut 1));
    }
}
