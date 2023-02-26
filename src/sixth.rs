use std::{marker::PhantomData, ptr::NonNull};

struct LinkedList<T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    // We semantically store values of T by value.
    _boo: PhantomData<T>,
}

type Link<T> = Option<NonNull<Node<T>>>;

struct Node<T> {
    front: Link<T>,
    back: Link<T>,
    elem: T,
}

pub struct Iter<'a, T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    _boo: PhantomData<&'a T>,
}

pub struct IterMut<'a, T> {
    front: Link<T>,
    back: Link<T>,
    len: usize,
    _boo: PhantomData<&'a mut T>,
}

pub struct IntoIter<T> {
    list: LinkedList<T>,
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        while let Some(_) = self.pop_front() {}
    }
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        Self {
            front: None,
            back: None,
            len: 0,
            _boo: PhantomData,
        }
    }

    pub fn back(&self) -> Option<&T> {
        unsafe { self.back.map(|node| &(*node.as_ptr()).elem) }
        // Same but uses ? which is an early return so maybe don't use it in keeping with the rest
        // of the impl.
        // unsafe { Some(&(*self.back?.as_ptr()).elem) }
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        unsafe { self.back.map(|node| &mut (*node.as_ptr()).elem) }
    }

    pub fn clear(&mut self) {
        while let Some(_) = self.pop_front() {}
    }

    pub fn front(&self) -> Option<&T> {
        unsafe { self.front.map(|node| &(*node.as_ptr()).elem) }
        // Same but uses ? which is an early return so maybe don't use it in keeping with the rest
        // of the impl.
        // unsafe { Some(&(*self.front?.as_ptr()).elem) }
    }

    pub fn front_mut(&mut self) -> Option<&mut T> {
        unsafe { self.front.map(|node| &mut (*node.as_ptr()).elem) }
    }

    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter { list: self }
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            front: self.front,
            back: self.back,
            len: self.len(),
            _boo: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut {
            front: self.front,
            back: self.back,
            len: self.len(),
            _boo: PhantomData,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn push_front(&mut self, elem: T) {
        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                front: None,
                back: None,
                elem,
            })));

            if let Some(old) = self.front {
                (*old.as_ptr()).front = Some(new);
                (*new.as_ptr()).back = Some(old);
            } else {
                // If there's no front, then we're the empty list and need
                // to set the back too.
                self.back = Some(new);
            }
            self.front = Some(new);
            self.len += 1;
        }
    }

    pub fn push_back(&mut self, elem: T) {
        unsafe {
            let new = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                front: None,
                back: None,
                elem,
            })));

            if let Some(old) = self.back {
                (*old.as_ptr()).back = Some(new);
                (*new.as_ptr()).front = Some(old);
            } else {
                // If there's no front, then we're the empty list and need
                // to set the back too.
                self.front = Some(new);
            }
            self.back = Some(new);
            self.len += 1;
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        unsafe {
            // Only have to do stuff if there is a front node to pop.
            self.front.map(|node| {
                // Bring the Box back to life so we can move out its value and
                // Drop it (Box continues to magically understand this for us).
                let boxed_node = Box::from_raw(node.as_ptr());
                let result = boxed_node.elem;

                // Make the next node into the new front.
                self.front = boxed_node.back;
                if let Some(new) = self.front {
                    // Cleanup its reference to the removed node
                    (*new.as_ptr()).front = None;
                } else {
                    // If the front is now null, then this list is now empty!
                    self.back = None;
                }

                self.len -= 1;
                result
                // Box gets implicitly freed here, knows there is no T.
            })
        }
    }

    pub fn pop_back(&mut self) -> Option<T> {
        unsafe {
            // Only have to do stuff if there is a front node to pop.
            self.front.map(|node| {
                // Bring the Box back to life so we can move out its value and
                // Drop it (Box continues to magically understand this for us).
                let boxed_node = Box::from_raw(node.as_ptr());
                let result = boxed_node.elem;

                // Make the next node into the new front.
                self.back = boxed_node.front;
                if let Some(new) = self.back {
                    // Cleanup its reference to the removed node
                    (*new.as_ptr()).back = None;
                } else {
                    // If the front is now null, then this list is now empty!
                    self.front = None;
                }

                self.len -= 1;
                result
                // Box gets implicitly freed here, knows there is no T.
            })
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<T: Clone> Clone for LinkedList<T> {
    fn clone(&self) -> Self {
        let mut new = Self::new();
        self.iter().for_each(|item| new.push_back(item.clone()));

        new
    }
}

impl<T> Default for LinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.back.map(|node| unsafe {
                self.len -= 1;
                self.back = (*node.as_ptr()).back;
                &(*node.as_ptr()).elem
            })
        } else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.back.map(|node| unsafe {
                self.len -= 1;
                self.back = (*node.as_ptr()).back;
                &mut (*node.as_ptr()).elem
            })
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.list.len
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T> IntoIterator for LinkedList<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

// impl<'a, T> IntoIterator for &'a LinkedList<T> {
//     type IntoIter = Iter<'a, T>;
//     type Item = &'a T;

//     fn into_iter(self) -> Self::IntoIter {
//         self.iter()
//     }
// }

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        // While self.front == self.back is a tempting condition to check here,
        // it won't do the right for yielding the last element! That sort of
        // thing only works for arrays because of "one-past-the-end" pointers.
        if self.len > 0 {
            // We could unwrap front, but this is safer and easier
            self.front.map(|node| unsafe {
                self.len -= 1;
                self.front = (*node.as_ptr()).back;
                &(*node.as_ptr()).elem
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        // While self.front == self.back is a tempting condition to check here,
        // it won't do the right for yielding the last element! That sort of
        // thing only works for arrays because of "one-past-the-end" pointers.
        if self.len > 0 {
            // We could unwrap front, but this is safer and easier
            self.front.map(|node| unsafe {
                self.len -= 1;
                self.front = (*node.as_ptr()).back;
                &mut (*node.as_ptr()).elem
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let tut = LinkedList::<i32>::new();
        assert_eq!(tut.len, 0);
        assert_eq!(tut.front, None);
        assert_eq!(tut.back, None);
    }

    #[test]
    fn push_pop_front_len() {
        let mut tut = LinkedList::new();
        // Try to break an empty list
        assert_eq!(tut.len(), 0);
        assert_eq!(tut.pop_front(), None);
        assert_eq!(tut.len(), 0);

        // Try to break a one item list
        tut.push_front(10);
        assert_eq!(tut.len(), 1);
        assert_eq!(tut.pop_front(), Some(10));
        assert_eq!(tut.len(), 0);
        assert_eq!(tut.pop_front(), None);
        assert_eq!(tut.len(), 0);

        // Mess around
        tut.push_front(2);
        assert_eq!(tut.len(), 1);
        assert_eq!(tut.pop_front(), Some(2));
        assert_eq!(tut.len(), 0);
        assert_eq!(tut.pop_front(), None);

        tut.push_front(3);
        assert_eq!(tut.len(), 1);
        assert_eq!(tut.pop_front(), Some(3));
        assert_eq!(tut.len(), 0);
        assert_eq!(tut.pop_front(), None);

        tut.push_front(4);
        assert_eq!(tut.len(), 1);
        tut.push_front(5);
        assert_eq!(tut.len(), 2);
        tut.push_front(6);
        assert_eq!(tut.len(), 3);
        assert_eq!(tut.pop_front(), Some(6));
        assert_eq!(tut.len(), 2);
        assert_eq!(tut.pop_front(), Some(5));
        assert_eq!(tut.len(), 1);
        assert_eq!(tut.pop_front(), Some(4));
        assert_eq!(tut.len(), 0);
        assert_eq!(tut.pop_front(), None);
        assert_eq!(tut.len(), 0);
        assert_eq!(tut.pop_front(), None);
        assert_eq!(tut.len(), 0);
    }

    #[test]
    fn front() {
        let mut tut = LinkedList::new();

        tut.push_front(1);
        assert_eq!(tut.len(), 1);
        assert_eq!(tut.front(), Some(&1));
    }

    #[test]
    fn test_basic_front() {
        let mut list = LinkedList::new();

        // Try to break an empty list
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        // Try to break a one item list
        list.push_front(10);
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        // Mess around
        list.push_front(10);
        assert_eq!(list.len(), 1);
        list.push_front(20);
        assert_eq!(list.len(), 2);
        list.push_front(30);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(30));
        assert_eq!(list.len(), 2);
        list.push_front(40);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(40));
        assert_eq!(list.len(), 2);
        assert_eq!(list.pop_front(), Some(20));
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn iter() {
        let mut tut = LinkedList::new();

        tut.push_front(2);
        tut.push_front(3);
        tut.push_front(4);
        tut.push_front(5);
        tut.push_back(1);
        tut.push_back(0);

        let mut it = tut.iter();
        assert_eq!(it.next(), Some(&5));
        assert_eq!(it.next(), Some(&4));
        assert_eq!(it.next(), Some(&3));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.next(), Some(&1));
        assert_eq!(it.next(), Some(&0));
    }

    #[test]
    fn into_iter() {
        let mut tut = LinkedList::new();

        tut.push_front(2);
        tut.push_front(3);
        tut.push_front(4);
        tut.push_front(5);
        tut.push_back(1);
        tut.push_back(0);

        let mut it = tut.into_iter();
        assert_eq!(it.next(), Some(5));
        assert_eq!(it.next(), Some(4));
        assert_eq!(it.next(), Some(3));
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), Some(1));
        assert_eq!(it.next(), Some(0));
    }

    #[test]
    fn iter_mut() {
        let mut tut = LinkedList::new();

        tut.push_front(2);
        tut.push_front(3);
        tut.push_front(4);
        tut.push_front(5);
        tut.push_back(1);
        tut.push_back(0);

        let mut it = tut.iter_mut();
        assert_eq!(it.next(), Some(&mut 5));
        assert_eq!(it.next(), Some(&mut 4));
        assert_eq!(it.next(), Some(&mut 3));
        assert_eq!(it.next(), Some(&mut 2));
        assert_eq!(it.next(), Some(&mut 1));
        assert_eq!(it.next(), Some(&mut 0));
    }

    #[test]
    fn is_empty() {
        let mut tut = LinkedList::new();
        assert!(tut.is_empty());

        tut.push_back(1);
        assert!(!tut.is_empty());
    }

    #[test]
    fn clear() {
        let mut tut = LinkedList::new();
        assert!(tut.is_empty());

        tut.push_back(1);
        tut.push_back(2);
        tut.push_back(3);

        assert!(!tut.is_empty());

        tut.clear();
        assert!(tut.is_empty());
    }

    #[test]
    fn clone() {
        let mut tut = LinkedList::new();
        tut.push_front(1);
        tut.push_front(2);
        tut.push_front(3);

        let mut cloned = tut.clone();

        assert_eq!(cloned.pop_front().unwrap(), 3);
        assert_eq!(cloned.pop_front().unwrap(), 2);
        assert_eq!(cloned.pop_front().unwrap(), 1);
    }
}
