use std::mem;

pub struct List<'a, T> {
    head: Link<T>,
    tail: Link<Option<&'a mut T>>,
}

type Link<T> = Option<Box<Node<T>>>;

#[derive(Debug, PartialEq)]
pub struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<'a, T> List<'a, T> {
    pub fn new() -> Self {
        List {
            head: None,
            tail: None,
        }
    }

    pub fn push(&'a mut self, elem: T) {
        let new_tail = Box::new(Node { elem, next: None });

        let new_tail = match self.head.take() {
            Some(old_tail) => {
                old_tail.next = Some(new_tail);
                old_tail.next.as_deref_mut()
            }
            None => {
                self.head = Some(new_tail);
                self.head.as_deref_mut()
            }
        };

        self.tail = new_tail;
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
}
