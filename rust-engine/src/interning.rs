//! # Interning System
//!
//! This module provides a minimal system for **global interning** of values in
//! Rust. Interning allows you to deduplicate equal values and replace them with
//! cheap, copyable handles (`Interned<T>`) that support **O(1) equality**,
//! hashing, and compact storage.
//!
//! ## Core Concepts
//!
//! - [`Interned<T>`]: A compact, copyable handle to a deduplicated value.
//! - [`InterningTable<T>`]: Stores interned values and manages uniqueness.
//! - [`HasGlobal`]: A trait to register global interning tables for types.
//! - [`InternExtTrait`]: A convenience trait to call `.intern()` on any value.
//!
//! ## Safety Note
//!
//! The `.get()` method on `Interned<T>` returns a `&'static T` using an
//! internal `transmute`, assuming the backing storage (interning table) never
//! remove items from its table. This is guaranteed by the implementation of
//! `InterningTable`.

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    ops::Deref,
    sync::{LazyLock, Mutex},
};

use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// An interning table storing unique values of `T` and assigning them stable indices.
///
/// This type is primarily an implementation detail behind [`Interned<T>`] and
/// the [`HasGlobal`] trait. You typically won't use it directly unless you're
/// wiring up a new globally‑interned type.
pub struct InterningTable<T> {
    /// The raw items: item at index `n` will be an `Interned { index: n }`.
    /// Fast lookup.
    items: Vec<T>,
    /// A map from `T`s to indexes, for fast interning of existing values.
    ids: HashMap<T, Interned<T>>,
}

impl<T> Default for InterningTable<T> {
    fn default() -> Self {
        Self {
            items: Default::default(),
            ids: Default::default(),
        }
    }
}

/// A statically interned value of type `T`.
///
/// An `Interned<T>` is a compact, copyable handle that deduplicates equal values
/// and compares in **O(1)** using its index. It behaves like `&'static T` via
/// [`Deref`], and can be obtained with [`InternExtTrait::intern`] or
/// [`Interned::intern`].
// Note: `Interned<T>` has `PartialEq` only if `T` has `PartialEq`. If we
// implement `PartialEq` manually, we loose the ability to pattern match on
// constant of this type. This is because of structural equality (see
// https://doc.rust-lang.org/stable/std/marker/trait.StructuralPartialEq.html).
#[derive(Hash, Eq, PartialEq)]
pub struct Interned<T> {
    phantom: PhantomData<T>,
    index: u32,
}

impl<T: Eq> PartialOrd for Interned<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: Eq> Ord for Interned<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index.cmp(&other.index)
    }
}

impl<T: Serialize + HasGlobal> Serialize for Interned<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.get().serialize(serializer)
    }
}

impl<T: HasGlobal> AsRef<T> for Interned<T> {
    fn as_ref(&self) -> &T {
        (*self).get()
    }
}

impl<'a, T: Deserialize<'a> + HasGlobal> Deserialize<'a> for Interned<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'a>,
    {
        Ok(Interned::intern(&T::deserialize(deserializer)?))
    }
}

impl<T: JsonSchema> JsonSchema for Interned<T> {
    fn schema_name() -> String {
        T::schema_name()
    }

    fn json_schema(generator: &mut schemars::r#gen::SchemaGenerator) -> schemars::schema::Schema {
        T::json_schema(generator)
    }
}

impl<T: HasGlobal + Debug> Debug for Interned<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Interned")
            .field("index", &self.index)
            .field("value", self.get())
            .finish()
    }
}

impl<T> Clone for Interned<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Interned<T> {}

/// A tiny, `FnOnce`-compatible wrapper used to initialize a `LazyLock` with a captured value.
///
/// This is a utility to build `LazyLock<T>` where the initializer needs to
/// own some value prepared in a `const` context.
///
/// You usually don't need this directly unless you're calling
/// [`InterningTable::new_with_values`].
pub struct ExplicitClosure<T, R>(T, fn(T) -> R);
impl<T, R> FnOnce<()> for ExplicitClosure<T, R> {
    type Output = R;

    extern "rust-call" fn call_once(self, _: ()) -> Self::Output {
        let Self(input, function) = self;
        function(input)
    }
}

impl<T: Hash + Eq + Clone + Send> InterningTable<T> {
    fn intern(&mut self, value: &T) -> Interned<T> {
        if let Some(interned) = self.ids.get(value) {
            *interned
        } else {
            let index = self.items.len();
            self.items.push(value.clone());
            let handle = Interned {
                phantom: PhantomData,
                index: index as u32,
            };
            self.ids.insert(value.clone(), handle);
            handle
        }
    }
    fn get(&self, interned: Interned<T>) -> &T {
        &self.items[interned.index as usize]
    }

    /// Creates a global `LazyLock` interning table prepopulated with `values`,
    /// and returns both the lock and the corresponding `Interned<T>` handles.
    ///
    /// # Panics
    ///
    /// Panics if `values` contains duplicates (by `Eq`).
    pub const fn new_with_values<const N: usize>(
        values: fn() -> [T; N],
    ) -> (LazyLockNewWithValue<T, N>, [Interned<T>; N]) {
        let mut i = 0;
        let mut interned_values: [Interned<T>; N] = [Interned {
            phantom: PhantomData,
            index: 0,
        }; N];
        while i < N {
            interned_values[i].index = i as u32;
            i += 1;
        }
        let lazy_lock = LazyLock::new(ExplicitClosure(values, |values| {
            let values = values();
            {
                // Ensure `value` has no duplicate.
                let set: HashSet<_> = values.iter().collect();
                if set.len() != values.len() {
                    panic!("new_with_values: the input has duplicates");
                }
            }

            let mut table = InterningTable::default();
            for value in values {
                table.intern(&value);
            }
            Mutex::new(table)
        }));
        (lazy_lock, interned_values)
    }
}

/// A type alias representing a lazily initialized `Mutex<InterningTable<T>>`
/// backed by a fixed-size array initializer.
///
/// This is the return type of [`InterningTable::new_with_values`].
pub type LazyLockNewWithValue<T, const N: usize> =
    LazyLock<Mutex<InterningTable<T>>, ExplicitClosure<fn() -> [T; N], Mutex<InterningTable<T>>>>;

/// Types that have a single, process‑global interning table.
///
/// Implement this for your type to opt in to interning:
/// provide a `static` (usually a `LazyLock<Mutex<InterningTable<Self>>>`)
/// and return a reference to it.
pub trait HasGlobal: Sized + Hash + Eq + Clone + Send + 'static {
    /// Returns the global interning table for `Self`.
    fn interning_table() -> &'static Mutex<InterningTable<Self>>;
}

impl<T: HasGlobal> Interned<T> {
    /// Interns a `value` and returns its compact handle.
    ///
    /// If an equal value has been interned before, this returns the existing
    /// handle; otherwise it inserts the value into the global table.
    pub fn intern(value: &T) -> Self {
        // Invariant: the interning mutex is only locked here, and InterningTable::intern
        // is panic-free (and does not invoke user code that may panic). Therefore, no
        // panic can occur while the mutex is held, so the mutex cannot be poisoned.
        // If this ever panics, our invariant was broken elsewhere.
        let mut table = T::interning_table()
            .lock()
            .expect("interning table mutex poisoned");
        table.intern(value)
    }

    /// Returns a `&'static T` for this handle.
    ///
    /// # Safety & Lifetimes
    ///
    /// This method relies on the fact that the backing storage lives for the
    /// entire program (it is kept in a `static` global table). The `'static`
    /// reference is sound as long as values are never removed from that table.
    /// This implementation uses `transmute` internally for that reason.
    pub fn get(self) -> &'static T {
        let table = T::interning_table().lock().unwrap();
        let local_reference = table.get(self);
        let static_reference: &'static T = unsafe { std::mem::transmute(local_reference) };
        static_reference
    }
}

/// Extension trait to intern values ergonomically via a method call.
///
/// This is blanket‑implemented for any `T` that can be globally interned.
pub trait InternExtTrait: Sized {
    /// Interns `self` and returns an [`Interned<Self>`].
    fn intern(&self) -> Interned<Self>;
}

impl<T: HasGlobal> InternExtTrait for T {
    fn intern(&self) -> Interned<Self> {
        Interned::intern(self)
    }
}

impl<T: HasGlobal> Deref for Interned<T> {
    type Target = T;

    /// Dereferences to the underlying value (`&'static T`).
    ///
    /// Equivalent to calling [`Interned::get`].
    fn deref(&self) -> &Self::Target {
        self.get()
    }
}
