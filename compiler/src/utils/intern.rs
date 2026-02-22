use rustc_hash::FxHashSet;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::ptr;

mod private {
    #[derive(Clone, Copy, Debug)]
    pub struct PrivateZst;
}

/// A reference to a value that is interned, and is known to be unique.
///
/// Note that it is possible to have a `T` and a `Interned<T>` that are (or
/// refer to) equal but different values. But if you have two different
/// `Interned<T>`s, they both refer to the same value, at a single location in
/// memory. This means that equality and hashing can be done on the value's
/// address rather than the value's contents, which can improve performance.
///
/// The `PrivateZst` field means you can pattern match with `Interned(v, _)`
/// but you can only construct a `Interned` with `new_unchecked`, and not
/// directly.
#[derive(Debug)]
pub struct Interned<'a, T>(pub &'a T, pub private::PrivateZst);

impl<'a, T> Interned<'a, T> {
    /// Create a new `Interned` value. The value referred to *must* be interned
    /// and thus be unique, and it *must* remain unique in the future. This
    /// function has `_unchecked` in the name but is not `unsafe`, because if
    /// the uniqueness condition is violated condition it will cause incorrect
    /// behaviour but will not affect memory safety.
    #[inline]
    pub const fn new_unchecked(t: &'a T) -> Self {
        Interned(t, private::PrivateZst)
    }
}

impl<'a, T> Clone for Interned<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> Copy for Interned<'a, T> {}

impl<'a, T> Deref for Interned<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.0
    }
}

impl<'a, T> PartialEq for Interned<'a, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Pointer equality implies equality, due to the uniqueness constraint.
        ptr::eq(self.0, other.0)
    }
}

impl<'a, T> Eq for Interned<'a, T> {}

impl<'a, T: PartialOrd> PartialOrd for Interned<'a, T> {
    fn partial_cmp(&self, other: &Interned<'a, T>) -> Option<Ordering> {
        // Pointer equality implies equality, due to the uniqueness constraint,
        // but the contents must be compared otherwise.
        if ptr::eq(self.0, other.0) {
            Some(Ordering::Equal)
        } else {
            let res = self.0.partial_cmp(other.0);
            debug_assert_ne!(res, Some(Ordering::Equal));
            res
        }
    }
}

impl<'a, T: Ord> Ord for Interned<'a, T> {
    fn cmp(&self, other: &Interned<'a, T>) -> Ordering {
        // Pointer equality implies equality, due to the uniqueness constraint,
        // but the contents must be compared otherwise.
        if ptr::eq(self.0, other.0) {
            Ordering::Equal
        } else {
            let res = self.0.cmp(other.0);
            debug_assert_ne!(res, Ordering::Equal);
            res
        }
    }
}

impl<'a, T> Hash for Interned<'a, T>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, s: &mut H) {
        // Pointer hashing is sufficient, due to the uniqueness constraint.
        ptr::hash(self.0, s)
    }
}

/// Interned list wrapper with pointer-identity semantics.
///
/// Values of this type must only be created from compiler interners that
/// guarantee uniqueness by content.
#[derive(Debug, Clone, Copy)]
pub struct List<'a, T>(&'a [T]);

impl<'a, T> List<'a, T> {
    #[inline]
    pub(crate) fn from_interned_slice(slice: &'a [T]) -> Self {
        List(slice)
    }

    #[inline]
    pub const fn empty() -> Self {
        List(&[])
    }

    #[inline]
    pub fn as_slice(self) -> &'a [T] {
        self.0
    }
}

impl<'a, T> Deref for List<'a, T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, T> PartialEq for List<'a, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if self.0.is_empty() && other.0.is_empty() {
            return true;
        }

        self.0.len() == other.0.len() && ptr::eq(self.0.as_ptr(), other.0.as_ptr())
    }
}

impl<'a, T> Eq for List<'a, T> {}

impl<'a, T> Hash for List<'a, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.len().hash(state);
        if !self.0.is_empty() {
            self.0.as_ptr().hash(state);
        }
    }
}

impl<'a, T> Default for List<'a, T> {
    #[inline]
    fn default() -> Self {
        List::empty()
    }
}

impl<'a, T> IntoIterator for List<'a, T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

pub struct WrappedHashSet<K> {
    wrapped: RefCell<FxHashSet<K>>,
}

impl<K> WrappedHashSet<K> {
    pub fn new() -> WrappedHashSet<K> {
        WrappedHashSet {
            wrapped: RefCell::new(FxHashSet::default()),
        }
    }
}

pub type InternedSet<'tcx, T> = WrappedHashSet<InternedInSet<'tcx, T>>;
// This type holds a `T` in the interner. The `T` is stored in the arena and
// this type just holds a pointer to it, but it still effectively owns it. It
// impls `Borrow` so that it can be looked up using the original
// (non-arena-memory-owning) types.
pub struct InternedInSet<'tcx, T: ?Sized>(pub &'tcx T);

impl<'tcx, T: 'tcx + ?Sized> Clone for InternedInSet<'tcx, T> {
    fn clone(&self) -> Self {
        InternedInSet(self.0)
    }
}

impl<'tcx, T: 'tcx + ?Sized> Copy for InternedInSet<'tcx, T> {}

impl<'a, T: ?Sized> Borrow<T> for InternedInSet<'a, T> {
    fn borrow(&self) -> &T {
        self.0
    }
}

impl<'a, T> Borrow<[T]> for InternedInSet<'a, Vec<T>> {
    fn borrow(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<'tcx, T> PartialEq for InternedInSet<'tcx, T>
where
    T: ?Sized + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<'tcx, T> Eq for InternedInSet<'tcx, T> where T: ?Sized + Eq {}

impl<'tcx, T> Hash for InternedInSet<'tcx, T>
where
    T: ?Sized + Hash,
{
    fn hash<H: Hasher>(&self, s: &mut H) {
        self.0.hash(s)
    }
}

impl<K: Eq + Hash + Copy> WrappedHashSet<K> {
    #[inline]
    pub fn intern<Q>(&self, value: Q, make: impl FnOnce(Q) -> K) -> K
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut set = self.wrapped.borrow_mut();
        if let Some(v) = set.get(&value) {
            return *v;
        } else {
            let v = make(value);
            set.insert(v);
            v
        }
    }

    #[inline]
    pub fn intern_ref<Q>(&self, value: &Q, make: impl FnOnce() -> K) -> K
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let mut set = self.wrapped.borrow_mut();
        if let Some(v) = set.get(value) {
            *v
        } else {
            let v = make();
            set.insert(v);
            v
        }
    }
}
