use super::clone::Clone;

/// See [`std::marker::Copy`]
pub trait Copy: Clone {}
/// See [`std::marker::Send`]
pub trait Send {}
/// See [`std::marker::Sync`]
pub trait Sync {}
/// See [`std::marker::Sized`]
pub trait Sized {}
/// See [`std::marker::StructuralPartialEq`]
pub trait StructuralPartialEq {}

// In our models, all types implement those marker traits
impl<T> Send for T {}
impl<T> Sync for T {}
impl<T> Sized for T {}
// The F* model; the other backends use the per-integer impls below.
#[cfg(hax_backend_fstar)]
impl<T: Clone> Copy for T {}

macro_rules! copy_impl_for_int {
    ($($t:ty),*) => {
        $(
            impl Copy for $t {}
        )*
    };
}

#[cfg(not(hax_backend_fstar))]
copy_impl_for_int!(
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

/// See [`std::marker::PhantomData`]
#[hax_lib::fstar::replace("type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T")]
#[hax_lib::legacy_lean::replace("structure PhantomData (T : Type) where")]
struct PhantomData<T>(T);

// The remaining `core::marker` traits are empty markers: the compiler decides
// who implements them, and nothing in the model dispatches on them. They are
// declared so that a signature mentioning one still resolves, and left without
// impls — a blanket `impl<T> Trait for T {}` would multiply the extracted trait
// impls for no gain.
//
// DEVIATION(std): the real hierarchy is `Sized: MetaSized: PointeeSized` (and
// `Unsize<T>: PointeeSized`); the model keeps these independent of its `Sized`
// above, so that `Sized`'s blanket impl does not drag two more in.
//
// `core::marker::{ConstParamTy, CoercePointee}` are missing on purpose: both are
// compiler-builtin *derive* macros, which only a proc-macro crate can provide.

/// See [`std::marker::MetaSized`]
pub trait MetaSized {}
/// See [`std::marker::PointeeSized`]
pub trait PointeeSized {}
/// See [`std::marker::Unsize`]
pub trait Unsize<T> {}
/// See [`std::marker::Freeze`]
pub trait Freeze {}
/// See [`std::marker::Unpin`]
pub trait Unpin {}
/// See [`std::marker::Destruct`]
pub trait Destruct {}
/// See [`std::marker::Tuple`]
pub trait Tuple {}
/// See [`std::marker::ConstParamTy_`]
//
// DEVIATION(std): std's supertraits are `StructuralPartialEq + Eq`. Naming
// `cmp::Eq` here would make `Core_models.Marker` depend on `Core_models.Cmp`,
// and `Cmp` is part of hax's mutually-recursive `Core_models.Bundle`, so F*'s
// dependency scan closes a cycle: `Bundle -> Marker -> Cmp -> Bundle`. Nothing
// dispatches on this trait and it has no impls, so the bound is dropped.
pub trait ConstParamTy_: StructuralPartialEq {}

/// See [`std::marker::FnPtr`]
//
// `FnPtr::addr` is left out: it returns `*const ()`, and the model has no raw
// pointers.
pub trait FnPtr: Copy {}

/// See [`std::marker::DiscriminantKind`]
pub trait DiscriminantKind {
    /// See [`std::marker::DiscriminantKind::Discriminant`]. std bounds it by
    /// `Clone + Copy + Debug + Eq + PartialEq + Hash + Send + Sync + Unpin`;
    /// the model carries no bound, since nothing here consumes a discriminant.
    type Discriminant;
}

/// See [`std::marker::PhantomPinned`]
pub struct PhantomPinned;

/// See [`std::marker::Variance`]. std seals this trait behind an associated
/// `const VALUE: Self`; the model uses the `Default` supertrait std also
/// requires, which is what [`variance`] is documented to be equivalent to.
pub trait Variance: super::default::Default {}

/// See [`std::marker::variance`]
pub fn variance<T: Variance>() -> T {
    <T as super::default::Default>::default()
}

// The `Phantom{Co,Contra,In}variant{,Lifetime}` markers.
//
// DEVIATION(std): std picks the phantom's argument to obtain the variance the
// name promises (`PhantomData<fn() -> T>`, `PhantomData<fn(T)>`,
// `PhantomData<fn(T) -> T>`). Variance is a compiler-level property with no
// counterpart in the extracted models, so all three carry `PhantomData<T>`.
macro_rules! phantom_variance {
    ($($name:ident),*) => {
        $(
            /// See [`std::marker::PhantomCovariant`] (and similar for the other
            /// variance markers)
            pub struct $name<T>(std::marker::PhantomData<T>);

            impl<T> $name<T> {
                /// See [`std::marker::PhantomCovariant::new`] (and similar for
                /// the other variance markers)
                pub fn new() -> $name<T> {
                    $name(std::marker::PhantomData)
                }
            }

            #[hax_lib::attributes]
            impl<T> super::default::Default for $name<T> {
                fn default() -> $name<T> {
                    $name::new()
                }
            }

            impl<T> Variance for $name<T> {}
        )*
    };
}

phantom_variance!(PhantomCovariant, PhantomContravariant, PhantomInvariant);

macro_rules! phantom_variance_lifetime {
    ($($name:ident($inner:ident)),*) => {
        $(
            /// See [`std::marker::PhantomCovariantLifetime`] (and similar for
            /// the other variance-lifetime markers)
            pub struct $name<'a>($inner<&'a ()>);

            impl<'a> $name<'a> {
                /// See [`std::marker::PhantomCovariantLifetime::new`] (and
                /// similar for the other variance-lifetime markers)
                pub fn new() -> $name<'a> {
                    $name($inner::new())
                }
            }

            #[hax_lib::attributes]
            impl<'a> super::default::Default for $name<'a> {
                fn default() -> $name<'a> {
                    $name::new()
                }
            }

            impl<'a> Variance for $name<'a> {}
        )*
    };
}

phantom_variance_lifetime!(
    PhantomCovariantLifetime(PhantomCovariant),
    PhantomContravariantLifetime(PhantomContravariant),
    PhantomInvariantLifetime(PhantomInvariant)
);

#[cfg(test)]
mod tests {
    use super::*;

    /// The variance markers are zero-sized and carry no state, so the only
    /// behaviour to pin is that `new()` and `Default::default()` agree — which
    /// is what makes `variance::<T>()` (documented as `Default::default()`)
    /// usable. std's counterparts are unstable (`phantom_variance_markers`), so
    /// the expectation is pinned here rather than compared against std.
    #[test]
    fn test_variance_markers_new_is_default() {
        let _: PhantomCovariant<u8> = PhantomCovariant::new();
        let _: PhantomContravariant<u8> = PhantomContravariant::new();
        let _: PhantomInvariant<u8> = PhantomInvariant::new();
        let _: PhantomCovariantLifetime = PhantomCovariantLifetime::new();
        let _: PhantomContravariantLifetime = PhantomContravariantLifetime::new();
        let _: PhantomInvariantLifetime = PhantomInvariantLifetime::new();

        assert_eq!(
            std::mem::size_of::<PhantomCovariant<u64>>(),
            std::mem::size_of::<std::marker::PhantomData<u64>>()
        );
        assert_eq!(std::mem::size_of::<PhantomPinned>(), 0);
    }

    /// `variance::<T>()` must go through `T`'s `Default`, for every marker.
    #[test]
    fn test_variance() {
        let _: PhantomCovariant<u8> = variance();
        let _: PhantomContravariant<u8> = variance();
        let _: PhantomInvariant<u8> = variance();
        let _: PhantomCovariantLifetime = variance();
        let _: PhantomContravariantLifetime = variance();
        let _: PhantomInvariantLifetime = variance();
    }

    /// A `Variance` marker whose `Default` is observable: `variance()` must
    /// return exactly what `Default::default()` does, not a value conjured
    /// some other way.
    #[test]
    fn test_variance_uses_default() {
        struct Witness(u8);
        #[hax_lib::attributes]
        impl crate::default::Default for Witness {
            fn default() -> Witness {
                Witness(7)
            }
        }
        impl Variance for Witness {}

        assert_eq!(variance::<Witness>().0, 7);
    }
}
