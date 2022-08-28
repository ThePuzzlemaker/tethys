use std::{
    cell::RefCell,
    collections::HashMap,
    hash::{BuildHasher, Hash, Hasher},
    ptr,
};

use id_arena::{Arena, Id};

use self::private::Private;

#[derive(Debug)]
pub struct Interner<T: Hash> {
    data: RefCell<HashMap<u64, Interned<T>>>,
}

impl<T: Hash> Default for Interner<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Hash> Interner<T> {
    pub fn new() -> Self {
        Self {
            data: RefCell::new(HashMap::new()),
        }
    }

    pub fn clear(&self) {
        self.data.borrow_mut().clear();
    }

    pub fn intern(&self, arena: &mut Arena<T>, value: T) -> Interned<T> {
        let mut data = self.data.borrow_mut();
        let mut hasher = data.hasher().build_hasher();
        value.hash(&mut hasher);
        let hash = hasher.finish();
        *data
            .entry(hash)
            .or_insert_with(|| Interned::new_unchecked(arena.alloc(value)))
    }
}

#[derive(Debug)]
pub struct Interned<T>(pub Id<T>, Private);

impl<T> Interned<T> {
    pub(crate) fn new_unchecked(t: Id<T>) -> Self {
        Interned(t, private::Private)
    }
}

impl<T> Copy for Interned<T> {}
impl<T> Clone for Interned<T> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}

impl<T> PartialEq<Interned<T>> for Interned<T> {
    fn eq(&self, other: &Interned<T>) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for Interned<T> {}
impl<T> Hash for Interned<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

mod private {
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub struct Private;
}
