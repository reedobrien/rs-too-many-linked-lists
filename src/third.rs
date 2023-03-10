use std::sync::Arc;

pub struct List<T> {
    head: Link<T>,
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

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        let mut head = self.head.take();

        while let Some(node) = head {
            if let Ok(mut node) = Arc::try_unwrap(node) {
                head = node.next.take();
            } else {
                break;
            }
        }
    }
}

impl<T> List<T> {
    pub fn new() -> Self {
        List { head: None }
    }

    pub fn head(&self) -> Option<&T> {
        self.head.as_ref().map(|node| &node.elem)
    }

    pub fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_deref(),
        }
    }

    pub fn prepend(&self, elem: T) -> List<T> {
        List {
            head: Some(Arc::new(Node {
                elem,
                next: self.head.clone(),
            })),
        }
    }

    pub fn tail(&self) -> List<T> {
        List {
            head: self.head.as_ref().and_then(|node| node.next.clone()),
        }
    }
}

type Link<T> = Option<Arc<Node<T>>>;

#[derive(Debug, PartialEq)]
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
    fn test_head() {
        let tut = List::<i32>::new();
        assert_eq!(tut.head, None);

        let got = tut.prepend(1).prepend(2).prepend(3).prepend(4);
        assert_eq!(got.head(), Some(&4));

        let got = got.tail();
        assert_eq!(got.head(), Some(&3));

        let got = got.tail();
        assert_eq!(got.head(), Some(&2));

        let got = got.tail();
        assert_eq!(got.head(), Some(&1));

        let got = got.tail();
        assert_eq!(got.head(), None);
    }

    #[test]
    fn test_iter() {
        let tut = List::new().prepend(1).prepend(2).prepend(3);

        let mut it = tut.iter();
        assert_eq!(it.next(), Some(&3));
        assert_eq!(it.next(), Some(&2));
        assert_eq!(it.next(), Some(&1));
    }
}
