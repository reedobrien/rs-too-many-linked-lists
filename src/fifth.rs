use std::{mem, ptr};

pub struct List<T> {
    head: Link<T>,
    tail: *mut Node<T>,
}

type Link<T> = *mut Node<T>;

#[derive(Debug, PartialEq)]
pub struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        while let Some(_) = self.pop() {}
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
        unsafe {
            self.next.map(|node| {
                self.next = node.next.as_ref();
                &node.elem
            })
        }
    }
}

pub struct IterMut<'a, T> {
    next: Option<&'a mut Node<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            self.next.take().map(|node| {
                self.next = node.next.as_mut();
                &mut node.elem
            })
        }
    }
}

impl<T> List<T> {
    pub fn new() -> Self {
        List {
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
        }
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    pub fn iter(&self) -> Iter<'_, T> {
        unsafe {
            Iter {
                next: self.head.as_ref(),
            }
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        unsafe {
            IterMut {
                next: self.head.as_mut(),
            }
        }
    }

    pub fn peek(&self) -> Option<&T> {
        unsafe { self.head.as_ref().map(|node| &node.elem) }
    }

    pub fn peek_mut(&mut self) -> Option<&mut T> {
        unsafe { self.head.as_mut().map(|node| &mut node.elem) }
    }

    pub fn pop(&mut self) -> Option<T> {
        unsafe {
            if self.head.is_null() {
                None
            } else {
                let head = Box::from_raw(self.head);
                self.head = head.next;

                if self.head.is_null() {
                    self.tail = ptr::null_mut();
                }

                Some(head.elem)
            }
        }
    }

    pub fn push(&mut self, elem: T) {
        unsafe {
            let mut new_tail = Box::into_raw(Box::new(Node {
                elem,
                next: ptr::null_mut(),
            }));

            if !self.tail.is_null() {
                unsafe {
                    (*self.tail).next = new_tail;
                }
            } else {
                self.head = new_tail;
            }

            self.tail = new_tail;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let tut = List::<i32>::new();

        assert!(tut.head.is_null())
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

    #[test]
    fn miri_food_peekmut() {
        let mut tut = List::new();
        tut.push(1);
        tut.push(2);
        tut.push(3);

        assert_eq!(tut.pop(), Some(1));
        tut.push(4);
        assert_eq!(tut.pop(), Some(2));
        tut.push(5);

        assert_eq!(tut.peek(), Some(&3));
        tut.push(6);
        tut.peek_mut().map(|x| *x *= 10);
        assert_eq!(tut.peek(), Some(&30));
        assert_eq!(tut.pop(), Some(30));

        for elem in tut.iter_mut() {
            *elem *= 100;
        }

        let mut iter = tut.iter();
        assert_eq!(iter.next(), Some(&400));
        assert_eq!(iter.next(), Some(&500));
        assert_eq!(iter.next(), Some(&600));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);

        assert_eq!(tut.pop(), Some(400));
        tut.peek_mut().map(|x| *x *= 10);
        assert_eq!(tut.peek(), Some(&5000));
        tut.push(7);
        assert_eq!(tut.pop(), Some(5000));
        assert_eq!(tut.pop(), Some(600));
        assert_eq!(tut.pop(), Some(7));
        assert_eq!(tut.pop(), None);

        tut.push(8);
    }
}
