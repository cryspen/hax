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
    /// See [`std::ops::ControlFlow`]
    pub enum ControlFlow<B, C> {
        /// See [`std::ops::ControlFlow::Continue`]
        Continue(C),
        /// See [`std::ops::ControlFlow::Break`]
        Break(B),
    }
}

pub mod index {
    /// See [`std::ops::Index`]
    pub trait Index<Idx> {
        type Output: ?Sized;
        fn index(&self, i: Idx) -> &Self::Output;
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

    /// See [`std::ops::Try`]
    pub trait Try {
        type Output;
        type Residual;
        fn from_output(x: Self::Output) -> Self;
        fn branch(self) -> super::control_flow::ControlFlow<Self::Residual, Self::Output>;
    }
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
}

mod drop {
    /// See [`std::ops::Drop`]
    trait Drop {
        fn drop(&mut self);
    }
}

pub mod range {
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
    pub struct RangeInclusive<T> {
        pub start: T,
        pub end: T,
    }

    macro_rules! impl_iterator_range_int {
        ($($int_type: ident)*) => {
            use crate::option::Option;
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
}

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_add_assign(x in 0u8..128, y in 0u8..128) {
            let mut model = x.inject();
            super::arith::AddAssign::add_assign(&mut model, y.inject());
            prop_assert_eq!(model, x + y);
        }

        #[test]
        fn test_sub_assign(x in any::<u8>(), y in any::<u8>()) {
            if x >= y {
                let mut model = x.inject();
                super::arith::SubAssign::sub_assign(&mut model, y.inject());
                prop_assert_eq!(model, x - y);
            }
        }
    }
}
