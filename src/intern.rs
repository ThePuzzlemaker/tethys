//! Arena-backed interning using a combination of a [`HashMap`] and a
//! [`typed_arena::Arena`]. This allows interning to occur, without leaking
//! memory or requiring the use of [`Arc`](std::sync::Arc) or similar
//! structures.
//!
//! This strategy is partially based on rustc's interning strategy, and some of
//! the code is practically verbatim, minus some small implementation
//! differences (e.g. using a regular [`HashMap`], not a sharded one)

use hashbrown::{
    hash_map::{DefaultHashBuilder, RawEntryMut},
    HashMap,
};
use std::{
    borrow::Borrow,
    cell::RefCell,
    hash::{BuildHasher, Hash, Hasher},
};

/// An interner backed by a [`HashMap`] and an arena.
#[derive(Debug, Default)]
pub struct Interner<'a, T: 'a + ?Sized> {
    map: RefCell<HashMap<Interned<'a, T>, ()>>,
}

impl<'a, T: 'a + ?Sized> Interner<'a, T>
where
    Interned<'a, T>: Eq + Hash + Copy,
{
    /// Intern a value.
    ///
    /// Tip: To intern things, you probably want to use the functions provided
    /// on [`ctxt::Interners`][crate::ctxt::Interners].
    ///
    /// This function is taken nearly verbatim from rustc, with some simplification.
    pub fn intern<Q>(&self, value: Q, make: impl FnOnce(Q) -> Interned<'a, T>) -> Interned<'a, T>
    where
        Interned<'a, T>: Borrow<Q>,
        Q: Hash + Eq,
    {
        let hash = make_hash(&value);
        let mut map = self.map.borrow_mut();
        let entry = map.raw_entry_mut().from_key_hashed_nocheck(hash, &value);

        match entry {
            RawEntryMut::Occupied(e) => *e.key(),
            RawEntryMut::Vacant(e) => {
                let v = make(value);
                e.insert_hashed_nocheck(hash, v, ());
                v
            }
        }
    }
}

/// An entry in an interner.
#[derive(Copy, Clone, Debug)]
pub struct Interned<'a, T: ?Sized>(&'a T);

/// Taken verbatim from rustc, with changes for AHash used by [`hashbrown`].
#[inline]
fn make_hash<K: Hash + ?Sized>(val: &K) -> u64 {
    let mut state = DefaultHashBuilder::default().build_hasher();
    val.hash(&mut state);
    state.finish()
}
