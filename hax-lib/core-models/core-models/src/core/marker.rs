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

// Empty markers without impls, declared so that signatures mentioning them resolve.
// DEVIATION(std): independent of `Sized`, unlike `Sized: MetaSized: PointeeSized`.

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
// DEVIATION(std): no `Eq` supertrait; it would close an F* module cycle via `Cmp`.
pub trait ConstParamTy_: StructuralPartialEq {}

/// See [`std::marker::FnPtr`]
pub trait FnPtr: Copy {}

/// See [`std::marker::DiscriminantKind`]
pub trait DiscriminantKind {
    /// See [`std::marker::DiscriminantKind::Discriminant`]
    type Discriminant;
}

/// See [`std::marker::PhantomPinned`]
pub struct PhantomPinned;

pub use self::variance::{
    PhantomContravariant, PhantomContravariantLifetime, PhantomCovariant, PhantomCovariantLifetime,
    PhantomInvariant, PhantomInvariantLifetime, Variance, variance,
};

/// The variance markers, in a submodule as in core, for their extracted names.
//
// DEVIATION(std): all wrap `PhantomData<T>`; variance has no meaning in the model.
mod variance {
    /// See [`std::marker::Variance`]. Uses `Default` rather than a `VALUE` const.
    pub trait Variance: crate::default::Default {}

    /// See [`std::marker::variance`]
    pub fn variance<T: Variance>() -> T {
        <T as crate::default::Default>::default()
    }

    /// See [`std::marker::PhantomCovariant`]
    pub struct PhantomCovariant<T>(std::marker::PhantomData<T>);
    /// See [`std::marker::PhantomContravariant`]
    pub struct PhantomContravariant<T>(std::marker::PhantomData<T>);
    /// See [`std::marker::PhantomInvariant`]
    pub struct PhantomInvariant<T>(std::marker::PhantomData<T>);
    /// See [`std::marker::PhantomCovariantLifetime`]
    pub struct PhantomCovariantLifetime<'a>(PhantomCovariant<&'a ()>);
    /// See [`std::marker::PhantomContravariantLifetime`]
    pub struct PhantomContravariantLifetime<'a>(PhantomContravariant<&'a ()>);
    /// See [`std::marker::PhantomInvariantLifetime`]
    pub struct PhantomInvariantLifetime<'a>(PhantomInvariant<&'a ()>);

    // hax names `new` after its impl's position; the empty impls match core's positions.
    // rustc numbers impls without an attribute macro first, hence `hax_lib::attributes`.
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {
        /// See [`std::marker::PhantomCovariantLifetime::new`]
        pub fn new() -> PhantomCovariantLifetime<'a> {
            PhantomCovariantLifetime(PhantomCovariant::new())
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::default::Default for PhantomCovariantLifetime<'a> {
        fn default() -> PhantomCovariantLifetime<'a> {
            PhantomCovariantLifetime::new()
        }
    }
    #[hax_lib::attributes]
    impl<'a> Variance for PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {
        /// See [`std::marker::PhantomContravariantLifetime::new`]
        pub fn new() -> PhantomContravariantLifetime<'a> {
            PhantomContravariantLifetime(PhantomContravariant::new())
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::default::Default for PhantomContravariantLifetime<'a> {
        fn default() -> PhantomContravariantLifetime<'a> {
            PhantomContravariantLifetime::new()
        }
    }
    #[hax_lib::attributes]
    impl<'a> Variance for PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {
        /// See [`std::marker::PhantomInvariantLifetime::new`]
        pub fn new() -> PhantomInvariantLifetime<'a> {
            PhantomInvariantLifetime(PhantomInvariant::new())
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::default::Default for PhantomInvariantLifetime<'a> {
        fn default() -> PhantomInvariantLifetime<'a> {
            PhantomInvariantLifetime::new()
        }
    }
    #[hax_lib::attributes]
    impl<'a> Variance for PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    // Real core's derived impls on the lifetime markers.
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {
        /// See [`std::marker::PhantomCovariant::new`]
        pub fn new() -> PhantomCovariant<T> {
            PhantomCovariant(std::marker::PhantomData)
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::default::Default for PhantomCovariant<T> {
        fn default() -> PhantomCovariant<T> {
            PhantomCovariant::new()
        }
    }
    #[hax_lib::attributes]
    impl<T> Variance for PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {
        /// See [`std::marker::PhantomContravariant::new`]
        pub fn new() -> PhantomContravariant<T> {
            PhantomContravariant(std::marker::PhantomData)
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::default::Default for PhantomContravariant<T> {
        fn default() -> PhantomContravariant<T> {
            PhantomContravariant::new()
        }
    }
    #[hax_lib::attributes]
    impl<T> Variance for PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {
        /// See [`std::marker::PhantomInvariant::new`]
        pub fn new() -> PhantomInvariant<T> {
            PhantomInvariant(std::marker::PhantomData)
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::default::Default for PhantomInvariant<T> {
        fn default() -> PhantomInvariant<T> {
            PhantomInvariant::new()
        }
    }
    #[hax_lib::attributes]
    impl<T> Variance for PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
}

#[cfg(test)]
mod tests {
    use super::*;

    /// std's variance markers are unstable, so the expectation is pinned here.
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

    #[test]
    fn test_variance() {
        let _: PhantomCovariant<u8> = variance();
        let _: PhantomContravariant<u8> = variance();
        let _: PhantomInvariant<u8> = variance();
        let _: PhantomCovariantLifetime = variance();
        let _: PhantomContravariantLifetime = variance();
        let _: PhantomInvariantLifetime = variance();
    }

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
