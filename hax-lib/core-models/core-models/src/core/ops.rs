pub mod arith {
    /// See [`std::ops::Add`]
    pub trait Add<Rhs = Self> {
        type Output;
        fn add(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Sub`]
    pub trait Sub<Rhs = Self> {
        type Output;
        fn sub(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Mul`]
    pub trait Mul<Rhs = Self> {
        type Output;
        fn mul(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Div`]
    pub trait Div<Rhs = Self> {
        type Output;
        fn div(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Neg`]
    pub trait Neg {
        type Output;
        fn neg(self) -> Self::Output;
    }
    /// See [`std::ops::Rem`]
    pub trait Rem<Rhs = Self> {
        type Output;
        fn rem(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::AddAssign`]
    pub trait AddAssign<Rhs = Self> {
        fn add_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::SubAssign`]
    pub trait SubAssign<Rhs = Self> {
        fn sub_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::MulAssign`]
    pub trait MulAssign<Rhs = Self> {
        fn mul_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::DivAssign`]
    pub trait DivAssign<Rhs = Self> {
        fn div_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::RemAssign`]
    pub trait RemAssign<Rhs = Self> {
        fn rem_assign(&mut self, rhs: Rhs);
    }

    macro_rules! int_trait_impls {
        ($($Self:ty)*) => {
            use hax_lib::ToInt;
            $(
            #[hax_lib::attributes]
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl crate::ops::arith::AddAssign<$Self> for $Self {
                #[hax_lib::requires(self.to_int() + rhs.to_int() <= $Self::MAX.to_int())]
                fn add_assign(&mut self, rhs: $Self) {
                    *self = *self + rhs
                }
            }
            #[hax_lib::attributes]
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl crate::ops::arith::SubAssign<$Self> for $Self {
                #[hax_lib::requires(self.to_int() - rhs.to_int() >= 0.to_int())]
                fn sub_assign(&mut self, rhs: $Self) {
                    *self = *self - rhs
                }
            })*
        }
    }

    int_trait_impls!(u8 u16 u32 u64);
}

pub mod bit {
    /// See [`std::ops::Shr`]
    pub trait Shr<Rhs = Self> {
        type Output;
        fn shr(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Shl`]
    pub trait Shl<Rhs = Self> {
        type Output;
        fn shl(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::BitXor`]
    pub trait BitXor<Rhs = Self> {
        type Output;
        fn bitxor(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::BitAnd`]
    pub trait BitAnd<Rhs = Self> {
        type Output;
        fn bitand(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::BitOr`]
    pub trait BitOr<Rhs = Self> {
        type Output;
        fn bitor(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Not`]
    pub trait Not {
        type Output;
        fn not(self) -> Self::Output;
    }
    /// See [`std::ops::ShrAssign`]
    pub trait ShrAssign<Rhs = Self> {
        fn shr_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::ShlAssign`]
    pub trait ShlAssign<Rhs = Self> {
        fn shl_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::BitXorAssign`]
    pub trait BitXorAssign<Rhs = Self> {
        fn bitxor_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::BitAndAssign`]
    pub trait BitAndAssign<Rhs = Self> {
        fn bitand_assign(&mut self, rhs: Rhs);
    }
    /// See [`std::ops::BitOrAssign`]
    pub trait BitOrAssign<Rhs = Self> {
        fn bitor_assign(&mut self, rhs: Rhs);
    }
}

pub mod control_flow {
    use crate::option::Option;
    use crate::result::Result;

    /// See [`std::ops::ControlFlow`]
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub enum ControlFlow<B, C> {
        /// See [`std::ops::ControlFlow::Continue`]
        Continue(C),
        /// See [`std::ops::ControlFlow::Break`]
        Break(B),
    }

    impl<B, C> ControlFlow<B, C> {
        /// See [`std::ops::ControlFlow::is_break`]
        pub fn is_break(&self) -> bool {
            matches!(*self, ControlFlow::Break(_))
        }

        /// See [`std::ops::ControlFlow::is_continue`]
        pub fn is_continue(&self) -> bool {
            matches!(*self, ControlFlow::Continue(_))
        }

        /// See [`std::ops::ControlFlow::break_value`]
        pub fn break_value(self) -> Option<B> {
            match self {
                ControlFlow::Continue(_) => Option::None,
                ControlFlow::Break(x) => Option::Some(x),
            }
        }

        /// See [`std::ops::ControlFlow::break_ok`]
        pub fn break_ok(self) -> Result<B, C> {
            match self {
                ControlFlow::Continue(c) => Result::Err(c),
                ControlFlow::Break(b) => Result::Ok(b),
            }
        }

        /// See [`std::ops::ControlFlow::map_break`]
        pub fn map_break<T, F: FnOnce(B) -> T>(self, f: F) -> ControlFlow<T, C> {
            match self {
                ControlFlow::Continue(x) => ControlFlow::Continue(x),
                ControlFlow::Break(x) => ControlFlow::Break(f(x)),
            }
        }

        /// See [`std::ops::ControlFlow::continue_value`]
        pub fn continue_value(self) -> Option<C> {
            match self {
                ControlFlow::Continue(x) => Option::Some(x),
                ControlFlow::Break(_) => Option::None,
            }
        }

        /// See [`std::ops::ControlFlow::continue_ok`]
        pub fn continue_ok(self) -> Result<C, B> {
            match self {
                ControlFlow::Continue(c) => Result::Ok(c),
                ControlFlow::Break(b) => Result::Err(b),
            }
        }

        /// See [`std::ops::ControlFlow::map_continue`]
        pub fn map_continue<T, F: FnOnce(C) -> T>(self, f: F) -> ControlFlow<B, T> {
            match self {
                ControlFlow::Continue(x) => ControlFlow::Continue(f(x)),
                ControlFlow::Break(x) => ControlFlow::Break(x),
            }
        }
    }

    // Matching a `ControlFlow<T, T>` binds `T` twice, which Aeneas's `do`
    // elaborator rejects; `patch_lean.py` drops the `do` from the extraction of
    // `into_value` (its body has no monadic binds).
    impl<T> ControlFlow<T, T> {
        /// See [`std::ops::ControlFlow::into_value`]
        pub fn into_value(self) -> T {
            match self {
                ControlFlow::Continue(x) => x,
                ControlFlow::Break(x) => x,
            }
        }
    }
}

pub mod index {
    /// See [`std::ops::Index`]
    pub trait Index<Idx> {
        type Output: ?Sized;
        fn index(&self, i: Idx) -> &Self::Output;
    }
    /// See [`std::ops::IndexMut`]
    //
    // Lean-only. The impls delegate to the mutable slice accessors
    // (`SliceIndex::get_mut`), which model `&mut` returns; the F* backend does
    // not use those (it lowers indexed assignment to `Slice.update` /
    // `Array.update`), so `IndexMut` is excluded there.
    #[cfg(not(hax_backend_fstar))]
    pub trait IndexMut<Idx>: Index<Idx> {
        fn index_mut(&mut self, i: Idx) -> &mut Self::Output;
    }
}

pub mod function {
    /// See [`std::ops::FnOnce`]
    #[hax_lib::attributes]
    pub trait FnOnce<Args> {
        type Output;
        #[hax_lib::requires(true)]
        fn call_once(&self, args: Args) -> Self::Output;
    }

    /// See [`std::ops::Fn`]
    #[hax_lib::attributes]
    pub trait FnMut<Args>: FnOnce<Args> {
        #[hax_lib::requires(true)]
        fn call_mut(&self, args: Args) -> Self::Output;
    }

    /// See [`std::ops::Fn`]
    /* Instances of the `Fn*` classes for F* arrows (arities 1 to 3), so that a
    closure can be passed where a `Fn*` bound is expected. Hand-written rather
    than extracted from Rust impls on `fn(..) -> _`: hax emits
    `_super_i0 = FStar.Tactics.Typeclasses.solve`, which F* cannot relate to the
    arrow's return type. Writing them out also gives the post-conditions (`res == x0 x1`). */
    #[cfg_attr(
        all(not(test), hax_backend_fstar),
        hax_lib::fstar::after(
            "unfold instance fnonce_arrow_binder t u
  : t_FnOnce (_:t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

unfold instance fnmut_arrow_binder t u
  : t_FnMut (_:t -> u) t = {
    _super_i0 = fnonce_arrow_binder t u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_mut = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

unfold instance fn_arrow_binder t u
  : t_Fn (_:t -> u) t = {
    _super_i0 = fnmut_arrow_binder t u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

unfold instance fnonce_arrow_binder2 t1 t2 u
  : t_FnOnce (t1 -> t2 -> u) (t1 & t2) = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) (res: u) -> res == x0 x1._1 x1._2);
    f_call_once = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) -> x0 x1._1 x1._2);
  }

unfold instance fnmut_arrow_binder2 t1 t2 u
  : t_FnMut (t1 -> t2 -> u) (t1 & t2) = {
    _super_i0 = fnonce_arrow_binder2 t1 t2 u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) (res: u) -> res == x0 x1._1 x1._2);
    f_call_mut = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) -> x0 x1._1 x1._2);
  }

unfold instance fn_arrow_binder2 t1 t2 u
  : t_Fn (t1 -> t2 -> u) (t1 & t2) = {
    _super_i0 = fnmut_arrow_binder2 t1 t2 u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) (res: u) -> res == x0 x1._1 x1._2);
    f_call = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) -> x0 x1._1 x1._2);
  }

unfold instance fnonce_arrow_binder3 t1 t2 t3 u
  : t_FnOnce (t1 -> t2 -> t3 -> u) (t1 & t2 & t3) = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) (res: u) -> res == x0 x1._1 x1._2 x1._3);
    f_call_once = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) -> x0 x1._1 x1._2 x1._3);
  }

unfold instance fnmut_arrow_binder3 t1 t2 t3 u
  : t_FnMut (t1 -> t2 -> t3 -> u) (t1 & t2 & t3) = {
    _super_i0 = fnonce_arrow_binder3 t1 t2 t3 u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) (res: u) -> res == x0 x1._1 x1._2 x1._3);
    f_call_mut = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) -> x0 x1._1 x1._2 x1._3);
  }

unfold instance fn_arrow_binder3 t1 t2 t3 u
  : t_Fn (t1 -> t2 -> t3 -> u) (t1 & t2 & t3) = {
    _super_i0 = fnmut_arrow_binder3 t1 t2 t3 u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) (res: u) -> res == x0 x1._1 x1._2 x1._3);
    f_call = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) -> x0 x1._1 x1._2 x1._3);
  }"
        )
    )]
    #[hax_lib::attributes]
    pub trait Fn<Args>: FnMut<Args> {
        #[hax_lib::requires(true)]
        fn call(&self, args: Args) -> Self::Output;
    }
}

pub mod try_trait {
    /// See [`std::ops::FromResidual`]
    pub trait FromResidual<R> {
        fn from_residual(x: R) -> Self;
    }

    /// See [`std::ops::Residual`]
    pub trait Residual<O> {
        type TryType: Try<Output = O, Residual = Self>;
    }

    /// See [`std::ops::Try`]
    pub trait Try {
        type Output;
        type Residual;
        fn from_output(x: Self::Output) -> Self;
        fn branch(self) -> super::control_flow::ControlFlow<Self::Residual, Self::Output>;
    }

    /// See [`std::ops::Residual`]
    pub trait Residual<O> {
        /// See [`std::ops::Residual::TryType`]
        type TryType: Try<Output = O, Residual = Self>;
    }

    /// See [`std::ops::Yeet`]
    pub struct Yeet<T>(pub T);
}

mod deref {
    /// See [`std::ops::Deref`]
    pub trait Deref {
        type Target: ?Sized;

        fn deref(&self) -> &Self::Target;
    }

    impl<T> Deref for &T {
        type Target = T;
        fn deref(&self) -> &T {
            &self
        }
    }

    /// See [`std::ops::DerefMut`]
    pub trait DerefMut: Deref {
        // `&mut` returns are unsupported in the F* backend, as for
        // `slice::index::SliceIndex::get_mut`.
        /// See [`std::ops::DerefMut::deref_mut`]
        #[cfg(not(hax_backend_fstar))]
        fn deref_mut(&mut self) -> &mut Self::Target;
    }

    // `unsafe` in real core: implementing it asserts that `deref` is pure. The
    // model has no notion of unsafe obligations, so it is a plain marker trait.
    /// See [`std::ops::DerefPure`]
    pub trait DerefPure {}

    /// See [`std::ops::Receiver`]
    pub trait Receiver {
        /// See [`std::ops::Receiver::Target`]
        type Target: ?Sized;
    }
}

/// Marker traits driving unsize/`dyn` coercions. They are compiler lang items
/// with no methods, so the model provides them exactly as real core does — as
/// empty traits, without the (pointer-based) impls, which the model cannot
/// express.
mod unsize {
    /// See [`std::ops::CoerceUnsized`]
    pub trait CoerceUnsized<T: ?Sized> {}

    /// See [`std::ops::DispatchFromDyn`]
    pub trait DispatchFromDyn<T> {}
}

mod reborrow {
    /// See [`std::ops::Reborrow`]
    pub trait Reborrow {}

    /// See [`std::ops::CoerceShared`]
    pub trait CoerceShared: Reborrow {
        /// See [`std::ops::CoerceShared::Target`]
        type Target: crate::marker::Copy;
    }
}

mod drop {
    /// See [`std::ops::Drop`]
    trait Drop {
        fn drop(&mut self);
    }
}

pub mod range {
    use crate::cmp::{Ordering, PartialOrd};
    use crate::option::Option;

    /// See [`std::ops::RangeTo`]
    pub struct RangeTo<T> {
        pub end: T,
    }
    /// See [`std::ops::RangeFrom`]
    pub struct RangeFrom<T> {
        pub start: T,
    }
    /// See [`std::ops::Range`]
    pub struct Range<T> {
        pub start: T,
        pub end: T,
    }
    /// See [`std::ops::RangeFull`]
    pub struct RangeFull;
    /// See [`std::ops::RangeInclusive`]
    ///
    /// Real core also carries an `exhausted` flag, set once the range has been
    /// iterated to its end, which makes a drained range report itself empty.
    /// The model does not implement `Iterator` for `RangeInclusive`, so there
    /// is nothing to observe it with; `is_empty`/`end_bound` below behave as if
    /// the flag were always `false`.
    pub struct RangeInclusive<T> {
        pub start: T,
        pub end: T,
    }
    /// See [`std::ops::RangeToInclusive`]
    pub struct RangeToInclusive<T> {
        pub end: T,
    }

    /// See [`std::ops::Bound`]
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub enum Bound<T> {
        /// See [`std::ops::Bound::Included`]
        Included(T),
        /// See [`std::ops::Bound::Excluded`]
        Excluded(T),
        /// See [`std::ops::Bound::Unbounded`]
        Unbounded,
    }

    impl<T> Bound<T> {
        /// See [`std::ops::Bound::as_ref`]
        pub fn as_ref(&self) -> Bound<&T> {
            match *self {
                Bound::Included(ref x) => Bound::Included(x),
                Bound::Excluded(ref x) => Bound::Excluded(x),
                Bound::Unbounded => Bound::Unbounded,
            }
        }

        // `&mut` returns are unsupported in the F* backend, as for
        // `slice::index::SliceIndex::get_mut`.
        /// See [`std::ops::Bound::as_mut`]
        #[cfg(not(hax_backend_fstar))]
        pub fn as_mut(&mut self) -> Bound<&mut T> {
            match *self {
                Bound::Included(ref mut x) => Bound::Included(x),
                Bound::Excluded(ref mut x) => Bound::Excluded(x),
                Bound::Unbounded => Bound::Unbounded,
            }
        }

        /// See [`std::ops::Bound::map`]
        pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Bound<U> {
            match self {
                Bound::Included(x) => Bound::Included(f(x)),
                Bound::Excluded(x) => Bound::Excluded(f(x)),
                Bound::Unbounded => Bound::Unbounded,
            }
        }
    }

    // The model's `Clone::clone` consumes `self` (see `crate::clone`), so
    // `cloned`/`copied` cannot start from a `Bound<&T>` the way real core does;
    // they take a `Bound<T>` instead. Same deviation as `Result::cloned`.
    #[cfg_attr(charon, aeneas::exclude)]
    impl<T: crate::clone::Clone> Bound<T> {
        /// See [`std::ops::Bound::cloned`]
        pub fn cloned(self) -> Bound<T> {
            match self {
                Bound::Included(x) => Bound::Included(x.clone()),
                Bound::Excluded(x) => Bound::Excluded(x.clone()),
                Bound::Unbounded => Bound::Unbounded,
            }
        }
    }

    // Same deviation, plus: the model has no primitive copy, so `copied` goes
    // through `Clone` (`marker::Copy: clone::Clone`).
    #[cfg_attr(charon, aeneas::exclude)]
    impl<T: crate::marker::Copy> Bound<T> {
        /// See [`std::ops::Bound::copied`]
        pub fn copied(self) -> Bound<T> {
            match self {
                Bound::Included(x) => Bound::Included(x.clone()),
                Bound::Excluded(x) => Bound::Excluded(x.clone()),
                Bound::Unbounded => Bound::Unbounded,
            }
        }
    }

    // The `requires(true)` on each method is what lets the blanket impls below
    // call it on an abstract instance: without it hax leaves the F* class's
    // `f_*_pre` field unconstrained, and the caller cannot discharge it.
    /// See [`std::ops::RangeBounds`]
    #[hax_lib::attributes]
    pub trait RangeBounds<T: ?Sized> {
        /// See [`std::ops::RangeBounds::start_bound`]
        #[hax_lib::requires(true)]
        fn start_bound(&self) -> Bound<&T>;
        /// See [`std::ops::RangeBounds::end_bound`]
        #[hax_lib::requires(true)]
        fn end_bound(&self) -> Bound<&T>;
    }

    // `contains` and `is_empty` are trait *defaults* in real core, which hax
    // does not support; they live in a blanket-implemented companion trait, as
    // `cmp::PartialOrdDefaults` does for `PartialOrd`'s comparison operators.
    #[hax_lib::attributes]
    pub(crate) trait RangeBoundsDefaults<T: ?Sized>: RangeBounds<T> {
        /// See [`std::ops::RangeBounds::contains`]
        #[hax_lib::requires(true)]
        fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            T: PartialOrd<U>,
            U: PartialOrd<T>;
        /// See [`std::ops::RangeBounds::is_empty`]
        #[hax_lib::requires(true)]
        fn is_empty(&self) -> bool
        where
            T: PartialOrd<T>;
    }

    impl<T: ?Sized, R: RangeBounds<T>> RangeBoundsDefaults<T> for R {
        fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            T: PartialOrd<U>,
            U: PartialOrd<T>,
        {
            bounds_contain(self.start_bound(), self.end_bound(), item)
        }

        fn is_empty(&self) -> bool
        where
            T: PartialOrd<T>,
        {
            bounds_are_empty(self.start_bound(), self.end_bound())
        }
    }

    /// See [`std::ops::IntoBounds`]
    #[hax_lib::attributes]
    pub trait IntoBounds<T>: RangeBounds<T> {
        /// See [`std::ops::IntoBounds::into_bounds`]
        #[hax_lib::requires(true)]
        fn into_bounds(self) -> (Bound<T>, Bound<T>);
    }

    // `intersect` is a trait *default* in real core; same treatment as
    // `RangeBoundsDefaults` above.
    #[hax_lib::attributes]
    pub(crate) trait IntoBoundsDefaults<T>: IntoBounds<T> {
        /// See [`std::ops::IntoBounds::intersect`]
        #[hax_lib::requires(true)]
        fn intersect<R: IntoBounds<T>>(self, other: R) -> (Bound<T>, Bound<T>)
        where
            T: crate::cmp::Ord;
    }

    impl<T, S: IntoBounds<T>> IntoBoundsDefaults<T> for S {
        fn intersect<R: IntoBounds<T>>(self, other: R) -> (Bound<T>, Bound<T>)
        where
            T: crate::cmp::Ord,
        {
            bounds_intersect(self.into_bounds(), other.into_bounds())
        }
    }

    /// See [`std::ops::OneSidedRangeBound`]
    #[cfg_attr(test, derive(PartialEq, Debug))]
    pub enum OneSidedRangeBound {
        /// See [`std::ops::OneSidedRangeBound::StartInclusive`]
        StartInclusive,
        /// See [`std::ops::OneSidedRangeBound::End`]
        End,
        /// See [`std::ops::OneSidedRangeBound::EndInclusive`]
        EndInclusive,
    }

    /// See [`std::ops::OneSidedRange`]
    #[hax_lib::attributes]
    pub trait OneSidedRange<T>: RangeBounds<T> {
        /// See [`std::ops::OneSidedRange::bound`]
        #[hax_lib::requires(true)]
        fn bound(self) -> (OneSidedRangeBound, T);
    }

    // `<` and `<=` are trait defaults on real core's `PartialOrd` (and live in
    // `cmp`'s private `PartialOrdDefaults` here), so the range predicates below
    // spell them out on top of `partial_cmp`.
    fn is_lt<T: ?Sized + PartialOrd<U>, U: ?Sized>(a: &T, b: &U) -> bool {
        matches!(a.partial_cmp(b), Option::Some(Ordering::Less))
    }

    fn is_le<T: ?Sized + PartialOrd<U>, U: ?Sized>(a: &T, b: &U) -> bool {
        matches!(
            a.partial_cmp(b),
            Option::Some(Ordering::Less | Ordering::Equal)
        )
    }

    fn bounds_contain<T: ?Sized, U: ?Sized>(start: Bound<&T>, end: Bound<&T>, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: PartialOrd<T>,
    {
        let above_start = match start {
            Bound::Included(s) => is_le(s, item),
            Bound::Excluded(s) => is_lt(s, item),
            Bound::Unbounded => true,
        };
        let below_end = match end {
            Bound::Included(e) => is_le(item, e),
            Bound::Excluded(e) => is_lt(item, e),
            Bound::Unbounded => true,
        };
        above_start && below_end
    }

    fn bounds_are_empty<T: ?Sized + PartialOrd<T>>(start: Bound<&T>, end: Bound<&T>) -> bool {
        let non_empty = match (start, end) {
            (Bound::Unbounded, _) => true,
            (_, Bound::Unbounded) => true,
            (Bound::Included(s), Bound::Included(e)) => is_le(s, e),
            (Bound::Included(s), Bound::Excluded(e)) => is_lt(s, e),
            (Bound::Excluded(s), Bound::Included(e)) => is_lt(s, e),
            (Bound::Excluded(s), Bound::Excluded(e)) => is_lt(s, e),
        };
        non_empty == false
    }

    fn bounds_intersect<T: crate::cmp::Ord>(
        a: (Bound<T>, Bound<T>),
        b: (Bound<T>, Bound<T>),
    ) -> (Bound<T>, Bound<T>) {
        let (a_start, a_end) = a;
        let (b_start, b_end) = b;
        let start = match (a_start, b_start) {
            (Bound::Unbounded, y) => y,
            (x, Bound::Unbounded) => x,
            (Bound::Included(x), Bound::Included(y)) => Bound::Included(crate::cmp::max(x, y)),
            (Bound::Excluded(x), Bound::Excluded(y)) => Bound::Excluded(crate::cmp::max(x, y)),
            (Bound::Included(i), Bound::Excluded(e)) | (Bound::Excluded(e), Bound::Included(i)) => {
                if is_lt(&e, &i) {
                    Bound::Included(i)
                } else {
                    Bound::Excluded(e)
                }
            }
        };
        let end = match (a_end, b_end) {
            (Bound::Unbounded, y) => y,
            (x, Bound::Unbounded) => x,
            (Bound::Included(x), Bound::Included(y)) => Bound::Included(crate::cmp::min(x, y)),
            (Bound::Excluded(x), Bound::Excluded(y)) => Bound::Excluded(crate::cmp::min(x, y)),
            (Bound::Included(i), Bound::Excluded(e)) | (Bound::Excluded(e), Bound::Included(i)) => {
                if is_lt(&i, &e) {
                    Bound::Included(i)
                } else {
                    Bound::Excluded(e)
                }
            }
        };
        (start, end)
    }

    impl<T> RangeBounds<T> for Range<T> {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Included(&self.start)
        }
        fn end_bound(&self) -> Bound<&T> {
            Bound::Excluded(&self.end)
        }
    }

    impl<T> RangeBounds<T> for RangeFrom<T> {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Included(&self.start)
        }
        fn end_bound(&self) -> Bound<&T> {
            Bound::Unbounded
        }
    }

    impl<T> RangeBounds<T> for RangeTo<T> {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Unbounded
        }
        fn end_bound(&self) -> Bound<&T> {
            Bound::Excluded(&self.end)
        }
    }

    impl<T: ?Sized> RangeBounds<T> for RangeFull {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Unbounded
        }
        fn end_bound(&self) -> Bound<&T> {
            Bound::Unbounded
        }
    }

    impl<T> RangeBounds<T> for RangeInclusive<T> {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Included(&self.start)
        }
        fn end_bound(&self) -> Bound<&T> {
            Bound::Included(&self.end)
        }
    }

    impl<T> RangeBounds<T> for RangeToInclusive<T> {
        fn start_bound(&self) -> Bound<&T> {
            Bound::Unbounded
        }
        fn end_bound(&self) -> Bound<&T> {
            Bound::Included(&self.end)
        }
    }

    impl<T> IntoBounds<T> for Range<T> {
        fn into_bounds(self) -> (Bound<T>, Bound<T>) {
            (Bound::Included(self.start), Bound::Excluded(self.end))
        }
    }

    impl<T> IntoBounds<T> for RangeFrom<T> {
        fn into_bounds(self) -> (Bound<T>, Bound<T>) {
            (Bound::Included(self.start), Bound::Unbounded)
        }
    }

    impl<T> IntoBounds<T> for RangeTo<T> {
        fn into_bounds(self) -> (Bound<T>, Bound<T>) {
            (Bound::Unbounded, Bound::Excluded(self.end))
        }
    }

    impl<T> IntoBounds<T> for RangeFull {
        fn into_bounds(self) -> (Bound<T>, Bound<T>) {
            (Bound::Unbounded, Bound::Unbounded)
        }
    }

    impl<T> IntoBounds<T> for RangeInclusive<T> {
        fn into_bounds(self) -> (Bound<T>, Bound<T>) {
            (Bound::Included(self.start), Bound::Included(self.end))
        }
    }

    impl<T> IntoBounds<T> for RangeToInclusive<T> {
        fn into_bounds(self) -> (Bound<T>, Bound<T>) {
            (Bound::Unbounded, Bound::Included(self.end))
        }
    }

    impl<T> OneSidedRange<T> for RangeFrom<T> {
        fn bound(self) -> (OneSidedRangeBound, T) {
            (OneSidedRangeBound::StartInclusive, self.start)
        }
    }

    impl<T> OneSidedRange<T> for RangeTo<T> {
        fn bound(self) -> (OneSidedRangeBound, T) {
            (OneSidedRangeBound::End, self.end)
        }
    }

    impl<T> OneSidedRange<T> for RangeToInclusive<T> {
        fn bound(self) -> (OneSidedRangeBound, T) {
            (OneSidedRangeBound::EndInclusive, self.end)
        }
    }

    impl<Idx: PartialOrd<Idx>> Range<Idx> {
        /// See [`std::ops::Range::contains`]
        pub fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            Idx: PartialOrd<U>,
            U: PartialOrd<Idx>,
        {
            bounds_contain(
                RangeBounds::start_bound(self),
                RangeBounds::end_bound(self),
                item,
            )
        }

        // The `where` repeats the impl's bound because real core spells it that
        // way too; dropping it would leave the extraction one trait dictionary
        // short of what a call site passes.
        /// See [`std::ops::Range::is_empty`]
        pub fn is_empty(&self) -> bool
        where
            Idx: PartialOrd<Idx>,
        {
            is_lt(&self.start, &self.end) == false
        }
    }

    impl<Idx: PartialOrd<Idx>> RangeFrom<Idx> {
        /// See [`std::ops::RangeFrom::contains`]
        pub fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            Idx: PartialOrd<U>,
            U: PartialOrd<Idx>,
        {
            bounds_contain(
                RangeBounds::start_bound(self),
                RangeBounds::end_bound(self),
                item,
            )
        }
    }

    impl<Idx: PartialOrd<Idx>> RangeTo<Idx> {
        /// See [`std::ops::RangeTo::contains`]
        pub fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            Idx: PartialOrd<U>,
            U: PartialOrd<Idx>,
        {
            bounds_contain(
                RangeBounds::start_bound(self),
                RangeBounds::end_bound(self),
                item,
            )
        }
    }

    impl<Idx: PartialOrd<Idx>> RangeToInclusive<Idx> {
        /// See [`std::ops::RangeToInclusive::contains`]
        pub fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            Idx: PartialOrd<U>,
            U: PartialOrd<Idx>,
        {
            bounds_contain(
                RangeBounds::start_bound(self),
                RangeBounds::end_bound(self),
                item,
            )
        }
    }

    impl<Idx> RangeInclusive<Idx> {
        /// See [`std::ops::RangeInclusive::new`]
        pub fn new(start: Idx, end: Idx) -> Self {
            RangeInclusive { start, end }
        }

        /// See [`std::ops::RangeInclusive::into_inner`]
        pub fn into_inner(self) -> (Idx, Idx) {
            (self.start, self.end)
        }
    }

    // Aeneas names these `RangeInclusive.start` / `RangeInclusive.«end»`, which
    // are already taken by the extracted structure's field projections, so the
    // Lean side keeps using the fields directly and only F* gets the accessors.
    #[cfg_attr(charon, aeneas::exclude)]
    impl<Idx> RangeInclusive<Idx> {
        /// See [`std::ops::RangeInclusive::start`]
        pub fn start(&self) -> &Idx {
            &self.start
        }

        /// See [`std::ops::RangeInclusive::end`]
        pub fn end(&self) -> &Idx {
            &self.end
        }
    }

    impl<Idx: PartialOrd<Idx>> RangeInclusive<Idx> {
        /// See [`std::ops::RangeInclusive::contains`]
        pub fn contains<U: ?Sized>(&self, item: &U) -> bool
        where
            Idx: PartialOrd<U>,
            U: PartialOrd<Idx>,
        {
            bounds_contain(
                RangeBounds::start_bound(self),
                RangeBounds::end_bound(self),
                item,
            )
        }

        /// See [`std::ops::RangeInclusive::is_empty`]
        pub fn is_empty(&self) -> bool
        where
            Idx: PartialOrd<Idx>,
        {
            is_le(&self.start, &self.end) == false
        }
    }

    macro_rules! impl_iterator_range_int {
        ($($int_type: ident)*) => {
            $(
                #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
                impl crate::iter::traits::iterator::Iterator for Range<$int_type> {
                    type Item = $int_type;
                    fn next(&mut self) -> Option<$int_type> {
                        if self.start >= self.end {
                            Option::None
                        } else {
                            let res = self.start;
                            self.start += 1;
                            Option::Some(res)
                        }
                    }
                }
            )*
        }
    }

    impl_iterator_range_int!(u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize);

    // The range *types* only ever produce an `Included` start and an
    // `Excluded`/`Included`/`Unbounded` end, so going through them leaves the
    // `Excluded`-start and mixed arms of the three helpers below unreached.
    // std implements `RangeBounds`/`IntoBounds` for `(Bound, Bound)`, which the
    // model does not, so the helpers are driven directly and compared against
    // that tuple form.
    #[cfg(test)]
    mod bounds {
        use super::{Bound, RangeBoundsDefaults};
        use crate::testing::Inject;
        use proptest::prelude::*;

        /// Every `Bound<u8>` shape, model and std side by side.
        fn pair(tag: u8, v: u8) -> (Bound<u8>, std::ops::Bound<u8>) {
            match tag % 3 {
                0 => (Bound::Included(v), std::ops::Bound::Included(v)),
                1 => (Bound::Excluded(v), std::ops::Bound::Excluded(v)),
                _ => (Bound::Unbounded, std::ops::Bound::Unbounded),
            }
        }

        fn as_ref(b: &Bound<u8>) -> Bound<&u8> {
            match b {
                Bound::Included(v) => Bound::Included(v),
                Bound::Excluded(v) => Bound::Excluded(v),
                Bound::Unbounded => Bound::Unbounded,
            }
        }

        proptest! {
            #[test]
            fn test_bounds_contain(st in 0u8..3, sv in any::<u8>(), et in 0u8..3,
                                   ev in any::<u8>(), item in any::<u8>()) {
                let (ms, ss) = pair(st, sv);
                let (me, se) = pair(et, ev);
                prop_assert_eq!(
                    super::bounds_contain(as_ref(&ms), as_ref(&me), &item),
                    std::ops::RangeBounds::contains(&(ss, se), &item)
                );
            }

            #[test]
            fn test_bounds_are_empty(st in 0u8..3, sv in any::<u8>(), et in 0u8..3,
                                     ev in any::<u8>()) {
                let (ms, ss) = pair(st, sv);
                let (me, se) = pair(et, ev);
                prop_assert_eq!(
                    super::bounds_are_empty(as_ref(&ms), as_ref(&me)),
                    std::ops::RangeBounds::<u8>::is_empty(&(ss, se))
                );
            }

            #[test]
            fn test_bounds_intersect(ast in 0u8..3, asv in any::<u8>(), aet in 0u8..3,
                                     aev in any::<u8>(), bst in 0u8..3, bsv in any::<u8>(),
                                     bet in 0u8..3, bev in any::<u8>()) {
                let (mas, sas) = pair(ast, asv);
                let (mae, sae) = pair(aet, aev);
                let (mbs, sbs) = pair(bst, bsv);
                let (mbe, sbe) = pair(bet, bev);
                prop_assert_eq!(
                    super::bounds_intersect((mas, mae), (mbs, mbe)),
                    std::ops::IntoBounds::intersect((sas, sae), (sbs, sbe)).inject()
                );
            }

            // `RangeBoundsDefaults` is what routes a range type into the two
            // predicates above; this keeps that path exercised too.
            #[test]
            fn test_defaults_agree_with_helpers(a in any::<u8>(), b in any::<u8>(),
                                                item in any::<u8>()) {
                let r = super::Range { start: a, end: b };
                prop_assert_eq!(
                    RangeBoundsDefaults::contains(&r, &item),
                    super::bounds_contain(Bound::Included(&a), Bound::Excluded(&b), &item)
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use pastey::paste;
    use proptest::prelude::*;

    // `int_trait_impls!` covers u8..u64. The `requires` rules out wrapping, so
    // the domain is every non-overflowing pair, edges included.
    macro_rules! assign_test {
        ($($t:ty)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_ $t _add_assign>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_add(y).is_some());
                            let mut model = x.inject();
                            super::arith::AddAssign::add_assign(&mut model, y.inject());
                            let mut std_value = x;
                            std::ops::AddAssign::add_assign(&mut std_value, y);
                            prop_assert_eq!(model, std_value);
                        }

                        #[test]
                        fn [<test_ $t _sub_assign>](x in any::<$t>(), y in any::<$t>()) {
                            prop_assume!(x.checked_sub(y).is_some());
                            let mut model = x.inject();
                            super::arith::SubAssign::sub_assign(&mut model, y.inject());
                            let mut std_value = x;
                            std::ops::SubAssign::sub_assign(&mut std_value, y);
                            prop_assert_eq!(model, std_value);
                        }

                        #[test]
                        fn [<test_ $t _add_assign_at_max>](x in any::<$t>()) {
                            let y = <$t>::MAX - x;
                            let mut model = x.inject();
                            super::arith::AddAssign::add_assign(&mut model, y.inject());
                            let mut std_value = x;
                            std::ops::AddAssign::add_assign(&mut std_value, y);
                            prop_assert_eq!(model, std_value);
                        }
                    }
                )*
            }
        }
    }

    assign_test! { u8 u16 u32 u64 }

    macro_rules! range_iter_test {
        ($($t:ident)*) => {
            paste! {
                $(
                    proptest! {
                        // `len` is kept small and added saturatingly so the range
                        // stays inside `$t` for every type.
                        #[test]
                        fn [<test_ $t _range_iter>](start in any::<$t>(), len in 0u8..=20) {
                            let end = start.saturating_add(len as $t);
                            let mut model = super::range::Range { start, end };
                            let mut collected = std::vec::Vec::new();
                            while let crate::option::Option::Some(x) =
                                crate::iter::traits::iterator::Iterator::next(&mut model)
                            {
                                collected.push(x);
                            }
                            prop_assert_eq!(collected, (start..end).collect::<std::vec::Vec<$t>>());
                        }
                    }
                )*
            }
        }
    }

    range_iter_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    proptest! {
        #[test]
        fn test_deref_ref(x in any::<u8>()) {
            let r = &x;
            prop_assert_eq!(
                *super::deref::Deref::deref(&r),
                *core::ops::Deref::deref(&r)
            );
        }
    }
    // ----- ControlFlow ------------------------------------------------------

    use super::control_flow::ControlFlow;

    // `which == true` builds a `Break`, `false` a `Continue`, so every test
    // below covers both variants over the whole `u8` range.
    macro_rules! model_cf {
        ($which:expr, $b:expr, $c:expr) => {
            if $which {
                ControlFlow::Break($b)
            } else {
                ControlFlow::Continue($c)
            }
        };
    }

    macro_rules! std_cf {
        ($which:expr, $b:expr, $c:expr) => {
            if $which {
                std::ops::ControlFlow::Break($b)
            } else {
                std::ops::ControlFlow::Continue($c)
            }
        };
    }

    proptest! {
        #[test]
        fn test_control_flow_is_break(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).is_break(),
                std_cf!(which, b, c).is_break()
            );
        }

        #[test]
        fn test_control_flow_is_continue(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).is_continue(),
                std_cf!(which, b, c).is_continue()
            );
        }

        #[test]
        fn test_control_flow_break_value(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).break_value(),
                std_cf!(which, b, c).break_value().inject()
            );
        }

        #[test]
        fn test_control_flow_continue_value(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).continue_value(),
                std_cf!(which, b, c).continue_value().inject()
            );
        }

        #[test]
        fn test_control_flow_break_ok(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).break_ok(),
                std_cf!(which, b, c).break_ok().inject()
            );
        }

        #[test]
        fn test_control_flow_continue_ok(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).continue_ok(),
                std_cf!(which, b, c).continue_ok().inject()
            );
        }

        #[test]
        fn test_control_flow_map_break(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).map_break(|x: u8| x.wrapping_add(1)),
                std_cf!(which, b, c).map_break(|x: u8| x.wrapping_add(1)).inject()
            );
        }

        #[test]
        fn test_control_flow_map_continue(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).map_continue(|x: u8| x.wrapping_add(1)),
                std_cf!(which, b, c).map_continue(|x: u8| x.wrapping_add(1)).inject()
            );
        }

        #[test]
        fn test_control_flow_into_value(which in any::<bool>(), b in any::<u8>(), c in any::<u8>()) {
            prop_assert_eq!(
                model_cf!(which, b, c).into_value(),
                std_cf!(which, b, c).into_value()
            );
        }
    }

    // ----- Bound ------------------------------------------------------------

    use super::range::Bound;

    // `which` selects `Included` / `Excluded` / `Unbounded`, so each test below
    // covers all three variants.
    macro_rules! model_bound {
        ($which:expr, $x:expr) => {
            match $which {
                0u8 => Bound::Included($x),
                1u8 => Bound::Excluded($x),
                _ => Bound::Unbounded,
            }
        };
    }

    macro_rules! std_bound {
        ($which:expr, $x:expr) => {
            match $which {
                0u8 => std::ops::Bound::Included($x),
                1u8 => std::ops::Bound::Excluded($x),
                _ => std::ops::Bound::Unbounded,
            }
        };
    }

    /// `u8`'s model `Clone` is the identity, so a `cloned` that dropped the
    /// `Clone` dictionary would still look correct; `Bumped` makes the
    /// application observable. It carries both `Clone`s so the model and std
    /// sides can be built from the same type. Under `hax_backend_fstar` the
    /// model's `Clone` is a blanket identity impl, which a second impl would
    /// conflict with — hence the `cfg`.
    #[cfg(not(hax_backend_fstar))]
    #[derive(Debug, PartialEq)]
    struct Bumped(u8);

    #[cfg(not(hax_backend_fstar))]
    impl crate::clone::Clone for Bumped {
        fn clone(self) -> Bumped {
            Bumped(self.0.wrapping_add(1))
        }
    }

    #[cfg(not(hax_backend_fstar))]
    impl std::clone::Clone for Bumped {
        fn clone(&self) -> Bumped {
            Bumped(self.0.wrapping_add(1))
        }
    }

    #[cfg(not(hax_backend_fstar))]
    impl Inject for Bumped {
        type Model = Bumped;
        fn inject(&self) -> Bumped {
            Bumped(self.0)
        }
    }

    proptest! {
        #[test]
        fn test_bound_as_ref(which in 0u8..3, x in any::<u8>()) {
            let model = model_bound!(which, x);
            let std_value = std_bound!(which, x);
            prop_assert_eq!(
                model.as_ref().map(|r: &u8| *r),
                std_value.as_ref().inject()
            );
        }

        #[test]
        fn test_bound_map(which in 0u8..3, x in any::<u8>()) {
            prop_assert_eq!(
                model_bound!(which, x).map(|v: u8| v.wrapping_add(1)),
                std_bound!(which, x).map(|v: u8| v.wrapping_add(1)).inject()
            );
        }

        #[test]
        fn test_bound_cloned_u8(which in 0u8..3, x in any::<u8>()) {
            // The model's `cloned` takes a `Bound<T>` rather than a
            // `Bound<&T>` (see the deviation noted on the impl).
            prop_assert_eq!(
                model_bound!(which, x).cloned(),
                std_bound!(which, &x).cloned().inject()
            );
        }

        #[test]
        fn test_bound_copied(which in 0u8..3, x in any::<u8>()) {
            prop_assert_eq!(
                model_bound!(which, x).copied(),
                std_bound!(which, &x).copied().inject()
            );
        }
    }

    #[cfg(not(hax_backend_fstar))]
    proptest! {
        #[test]
        fn test_bound_cloned_applies_the_dictionary(which in 0u8..3, x in any::<u8>()) {
            let source = Bumped(x);
            prop_assert_eq!(
                model_bound!(which, Bumped(x)).cloned(),
                std_bound!(which, &source).cloned().inject()
            );
        }

        #[test]
        fn test_bound_as_mut(which in 0u8..3, x in any::<u8>(), v in any::<u8>()) {
            let mut model = model_bound!(which, x);
            let mut std_value = std_bound!(which, x);
            if let Bound::Included(r) | Bound::Excluded(r) = model.as_mut() {
                *r = v;
            }
            if let std::ops::Bound::Included(r) | std::ops::Bound::Excluded(r) = std_value.as_mut() {
                *r = v;
            }
            prop_assert_eq!(model, std_value.inject());
        }
    }

    // ----- RangeBounds / IntoBounds / OneSidedRange -------------------------

    use super::range::{
        IntoBounds, IntoBoundsDefaults, OneSidedRange, OneSidedRangeBound, Range, RangeBounds,
        RangeBoundsDefaults, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
    };

    fn model_osb_tag(b: &OneSidedRangeBound) -> u8 {
        match b {
            OneSidedRangeBound::StartInclusive => 0,
            OneSidedRangeBound::End => 1,
            OneSidedRangeBound::EndInclusive => 2,
        }
    }

    fn std_osb_tag(b: &std::ops::OneSidedRangeBound) -> u8 {
        match b {
            std::ops::OneSidedRangeBound::StartInclusive => 0,
            std::ops::OneSidedRangeBound::End => 1,
            std::ops::OneSidedRangeBound::EndInclusive => 2,
        }
    }

    proptest! {
        #[test]
        fn test_range_bounds_range(a in any::<u8>(), b in any::<u8>()) {
            let model = Range { start: a, end: b };
            prop_assert_eq!(
                model.start_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::start_bound(&(a..b)).inject()
            );
            prop_assert_eq!(
                model.end_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::end_bound(&(a..b)).inject()
            );
        }

        #[test]
        fn test_range_bounds_range_from(a in any::<u8>()) {
            let model = RangeFrom { start: a };
            prop_assert_eq!(
                model.start_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::start_bound(&(a..)).inject()
            );
            prop_assert_eq!(
                model.end_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::end_bound(&(a..)).inject()
            );
        }

        #[test]
        fn test_range_bounds_range_to(b in any::<u8>()) {
            let model = RangeTo { end: b };
            prop_assert_eq!(
                model.start_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::start_bound(&(..b)).inject()
            );
            prop_assert_eq!(
                model.end_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::end_bound(&(..b)).inject()
            );
        }

        #[test]
        fn test_range_bounds_range_inclusive(a in any::<u8>(), b in any::<u8>()) {
            let model = RangeInclusive::new(a, b);
            prop_assert_eq!(
                model.start_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::start_bound(&(a..=b)).inject()
            );
            prop_assert_eq!(
                model.end_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::end_bound(&(a..=b)).inject()
            );
        }

        #[test]
        fn test_range_bounds_range_to_inclusive(b in any::<u8>()) {
            let model = RangeToInclusive { end: b };
            prop_assert_eq!(
                model.start_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::start_bound(&(..=b)).inject()
            );
            prop_assert_eq!(
                model.end_bound().map(|r: &u8| *r),
                std::ops::RangeBounds::end_bound(&(..=b)).inject()
            );
        }

        #[test]
        fn test_range_bounds_range_full(_x in any::<u8>()) {
            let model = RangeFull;
            prop_assert_eq!(
                RangeBounds::<u8>::start_bound(&model).map(|r: &u8| *r),
                std::ops::RangeBounds::<u8>::start_bound(&(..)).inject()
            );
            prop_assert_eq!(
                RangeBounds::<u8>::end_bound(&model).map(|r: &u8| *r),
                std::ops::RangeBounds::<u8>::end_bound(&(..)).inject()
            );
        }

        #[test]
        fn test_range_bounds_contains(a in any::<u8>(), b in any::<u8>(), item in any::<u8>()) {
            prop_assert_eq!(
                RangeBoundsDefaults::contains(&Range { start: a, end: b }, &item),
                std::ops::RangeBounds::contains(&(a..b), &item)
            );
        }

        #[test]
        fn test_range_bounds_is_empty(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(
                RangeBoundsDefaults::is_empty(&Range { start: a, end: b }),
                std::ops::RangeBounds::is_empty(&(a..b))
            );
            prop_assert_eq!(
                RangeBoundsDefaults::is_empty(&RangeInclusive::new(a, b)),
                std::ops::RangeBounds::is_empty(&(a..=b))
            );
            prop_assert_eq!(
                RangeBoundsDefaults::is_empty(&RangeFrom { start: a }),
                std::ops::RangeBounds::is_empty(&(a..))
            );
            prop_assert_eq!(
                RangeBoundsDefaults::is_empty(&RangeTo { end: b }),
                std::ops::RangeBounds::is_empty(&(..b))
            );
            prop_assert_eq!(
                RangeBoundsDefaults::is_empty(&RangeToInclusive { end: b }),
                std::ops::RangeBounds::is_empty(&(..=b))
            );
        }

        #[test]
        fn test_range_contains(a in any::<u8>(), b in any::<u8>(), item in any::<u8>()) {
            prop_assert_eq!(
                Range { start: a, end: b }.contains(&item),
                (a..b).contains(&item)
            );
        }

        #[test]
        fn test_range_is_empty(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(Range { start: a, end: b }.is_empty(), (a..b).is_empty());
        }

        #[test]
        fn test_range_from_contains(a in any::<u8>(), item in any::<u8>()) {
            prop_assert_eq!(RangeFrom { start: a }.contains(&item), (a..).contains(&item));
        }

        #[test]
        fn test_range_to_contains(b in any::<u8>(), item in any::<u8>()) {
            prop_assert_eq!(RangeTo { end: b }.contains(&item), (..b).contains(&item));
        }

        #[test]
        fn test_range_to_inclusive_contains(b in any::<u8>(), item in any::<u8>()) {
            prop_assert_eq!(
                RangeToInclusive { end: b }.contains(&item),
                (..=b).contains(&item)
            );
        }

        #[test]
        fn test_range_inclusive_contains(a in any::<u8>(), b in any::<u8>(), item in any::<u8>()) {
            prop_assert_eq!(
                RangeInclusive::new(a, b).contains(&item),
                (a..=b).contains(&item)
            );
        }

        #[test]
        fn test_range_inclusive_is_empty(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(RangeInclusive::new(a, b).is_empty(), (a..=b).is_empty());
        }

        #[test]
        fn test_range_inclusive_new_start_end(a in any::<u8>(), b in any::<u8>()) {
            let model = RangeInclusive::new(a, b);
            let std_value = std::ops::RangeInclusive::new(a, b);
            prop_assert_eq!(model.start(), std_value.start());
            prop_assert_eq!(model.end(), std_value.end());
        }

        #[test]
        fn test_range_inclusive_into_inner(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(
                RangeInclusive::new(a, b).into_inner(),
                (a..=b).into_inner()
            );
        }

        #[test]
        fn test_into_bounds(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(
                Range { start: a, end: b }.into_bounds(),
                std::ops::IntoBounds::into_bounds(a..b).inject()
            );
            prop_assert_eq!(
                RangeFrom { start: a }.into_bounds(),
                std::ops::IntoBounds::into_bounds(a..).inject()
            );
            prop_assert_eq!(
                RangeTo { end: b }.into_bounds(),
                std::ops::IntoBounds::into_bounds(..b).inject()
            );
            prop_assert_eq!(
                RangeInclusive::new(a, b).into_bounds(),
                std::ops::IntoBounds::into_bounds(a..=b).inject()
            );
            prop_assert_eq!(
                RangeToInclusive { end: b }.into_bounds(),
                std::ops::IntoBounds::into_bounds(..=b).inject()
            );
            prop_assert_eq!(
                IntoBounds::<u8>::into_bounds(RangeFull),
                std::ops::IntoBounds::<u8>::into_bounds(..).inject()
            );
        }

        #[test]
        fn test_into_bounds_intersect(a in any::<u8>(), b in any::<u8>(), c in any::<u8>(), d in any::<u8>()) {
            prop_assert_eq!(
                IntoBoundsDefaults::intersect(Range { start: a, end: b }, Range { start: c, end: d }),
                std::ops::IntoBounds::intersect(a..b, c..d).inject()
            );
            prop_assert_eq!(
                IntoBoundsDefaults::intersect(RangeFrom { start: a }, RangeTo { end: b }),
                std::ops::IntoBounds::intersect(a.., ..b).inject()
            );
            prop_assert_eq!(
                IntoBoundsDefaults::intersect(RangeInclusive::new(a, b), Range { start: c, end: d }),
                std::ops::IntoBounds::intersect(a..=b, c..d).inject()
            );
            prop_assert_eq!(
                IntoBoundsDefaults::intersect(RangeFull, RangeInclusive::new(a, b)),
                std::ops::IntoBounds::intersect(.., a..=b).inject()
            );
        }

        #[test]
        fn test_one_sided_range_bound(a in any::<u8>()) {
            let (model_tag, model_v) = OneSidedRange::bound(RangeFrom { start: a });
            let (std_tag, std_v) = std::ops::OneSidedRange::bound(a..);
            prop_assert_eq!(model_osb_tag(&model_tag), std_osb_tag(&std_tag));
            prop_assert_eq!(model_v, std_v);

            let (model_tag, model_v) = OneSidedRange::bound(RangeTo { end: a });
            let (std_tag, std_v) = std::ops::OneSidedRange::bound(..a);
            prop_assert_eq!(model_osb_tag(&model_tag), std_osb_tag(&std_tag));
            prop_assert_eq!(model_v, std_v);

            let (model_tag, model_v) = OneSidedRange::bound(RangeToInclusive { end: a });
            let (std_tag, std_v) = std::ops::OneSidedRange::bound(..=a);
            prop_assert_eq!(model_osb_tag(&model_tag), std_osb_tag(&std_tag));
            prop_assert_eq!(model_v, std_v);
        }
    }

    // ----- DerefMut / IndexMut ----------------------------------------------

    // Both traits only have `&mut`-returning methods, which the F* backend does
    // not support, so the model drops them there and so do these tests.
    #[cfg(not(hax_backend_fstar))]
    mod mut_traits {
        use super::*;

        struct Cell(u8);

        impl crate::ops::deref::Deref for Cell {
            type Target = u8;
            fn deref(&self) -> &u8 {
                &self.0
            }
        }

        impl crate::ops::deref::DerefMut for Cell {
            fn deref_mut(&mut self) -> &mut u8 {
                &mut self.0
            }
        }

        impl std::ops::Deref for Cell {
            type Target = u8;
            fn deref(&self) -> &u8 {
                &self.0
            }
        }

        impl std::ops::DerefMut for Cell {
            fn deref_mut(&mut self) -> &mut u8 {
                &mut self.0
            }
        }

        struct Buf([u8; 4]);

        impl crate::ops::index::Index<usize> for Buf {
            type Output = u8;
            fn index(&self, i: usize) -> &u8 {
                &self.0[i]
            }
        }

        impl crate::ops::index::IndexMut<usize> for Buf {
            fn index_mut(&mut self, i: usize) -> &mut u8 {
                &mut self.0[i]
            }
        }

        impl std::ops::Index<usize> for Buf {
            type Output = u8;
            fn index(&self, i: usize) -> &u8 {
                &self.0[i]
            }
        }

        impl std::ops::IndexMut<usize> for Buf {
            fn index_mut(&mut self, i: usize) -> &mut u8 {
                &mut self.0[i]
            }
        }

        proptest! {
            // `Deref`/`Index` are supertraits of the `*Mut` pair, so both halves
            // are implemented here; these run the immutable ones.
            #[test]
            fn test_deref(x in any::<u8>()) {
                let model = Cell(x);
                let std_value = Cell(x);
                prop_assert_eq!(
                    *crate::ops::deref::Deref::deref(&model),
                    *std::ops::Deref::deref(&std_value)
                );
            }

            #[test]
            fn test_index(xs in prop::array::uniform4(any::<u8>()), i in 0usize..4) {
                let model = Buf(xs);
                let std_value = Buf(xs);
                prop_assert_eq!(
                    *crate::ops::index::Index::index(&model, i),
                    *std::ops::Index::index(&std_value, i)
                );
            }

            #[test]
            fn test_deref_mut(x in any::<u8>(), v in any::<u8>()) {
                let mut model = Cell(x);
                *crate::ops::deref::DerefMut::deref_mut(&mut model) = v;
                let mut std_value = Cell(x);
                *std::ops::DerefMut::deref_mut(&mut std_value) = v;
                prop_assert_eq!(model.0, std_value.0);
            }

            #[test]
            fn test_index_mut(xs in prop::array::uniform4(any::<u8>()), i in 0usize..4, v in any::<u8>()) {
                let mut model = Buf(xs);
                *crate::ops::index::IndexMut::index_mut(&mut model, i) = v;
                let mut std_value = Buf(xs);
                *std::ops::IndexMut::index_mut(&mut std_value, i) = v;
                prop_assert_eq!(model.0, std_value.0);
            }
        }
    }
}
