// use std::{
//     cell::RefCell,
//     collections::HashMap,
//     hash::{BuildHasher, Hash, Hasher},
//     ptr,
// };

// use typed_arena::Arena;

// use self::private::Private;

// pub struct Interner<T: Hash> {
//     data: RefCell<HashMap<u64, Interned<T>>>,
// }

// impl<T: Hash> Default for Interner<T> {
//     fn default() -> Self {
//         Self::new()
//     }
// }

// impl<T: Hash> Interner<T> {
//     pub fn new() -> Self {
//         Self {
//             data: RefCell::new(HashMap::new()),
//         }
//     }

//     pub fn intern(&self, arena: &'a Arena<T>, value: T) -> Interned<T> {
//         let mut data = self.data.borrow_mut();
//         let mut hasher = data.hasher().build_hasher();
//         value.hash(&mut hasher);
//         let hash = hasher.finish();
//         *data
//             .entry(hash)
//             .or_insert_with(|| Interned::new_unchecked(arena.alloc(value)))
//     }
// }

// #[derive(Debug)]
// pub struct Interned<T>(pub &'a T, Private);

// impl<'a, T> Interned<'a, T> {
//     pub(crate) fn new_unchecked(t: &'a T) -> Self {
//         Interned(t, private::Private)
//     }
// }

// impl<'a, T> Copy for Interned<'a, T> {}
// impl<'a, T> Clone for Interned<'a, T> {
//     fn clone(&self) -> Self {
//         Self(self.0, self.1)
//     }
// }

// impl<'a, T> PartialEq<Interned<'a, T>> for Interned<'a, T> {
//     fn eq(&self, other: &Interned<T>) -> bool {
//         ptr::eq(self.0, other.0)
//     }
// }

// impl<'a, T> Eq for Interned<'a, T> {}
// impl<'a, T> Hash for Interned<'a, T> {
//     fn hash<H: Hasher>(&self, state: &mut H) {
//         (self.0 as *const T).hash(state)
//     }
// }

// mod private {
//     #[derive(Copy, Clone, Debug, PartialEq, Eq)]
//     pub struct Private;
// }
