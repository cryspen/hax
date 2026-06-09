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
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
            impl crate::ops::arith::AddAssign<$Self> for $Self {
                #[hax_lib::requires(self.to_int() + rhs.to_int() <= $Self::MAX.to_int())]
                fn add_assign(&mut self, rhs: $Self) {
                    *self = *self + rhs
                }
            }
            #[hax_lib::attributes]
            #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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
    trait Shr<Rhs = Self> {
        type Output;
        fn shr(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::Shl`]
    trait Shl<Rhs = Self> {
        type Output;
        fn shl(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::BitXor`]
    trait BitXor<Rhs = Self> {
        type Output;
        fn bitxor(self, rhs: Rhs) -> Self::Output;
    }
    /// See [`std::ops::BitAnd`]
    trait BitAnd<Rhs = Self> {
        type Output;
        fn bitand(self, rhs: Rhs) -> Self::Output;
    }
    trait BitOr<Rhs = Self> {
        type Output;
        fn bitor(self, rhs: Rhs) -> Self::Output;
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
    pub trait Fn<Args>: FnOnce<Args> {
        #[hax_lib::requires(true)]
        fn call(&self, args: Args) -> Self::Output;
    }

    /* These instances provide implementations of the F* type classes corresponding to Fn traits for anonymous functions.
    This ensures that passing a closure where something implementing Fn works when translated to F* */
    #[cfg(not(test))]
    #[hax_lib::fstar::after(
        "unfold instance fnonce_arrow_binder t u
  : t_FnOnce (_:t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }"
    )]
    impl<Arg, Out> FnOnce<Arg> for fn(Arg) -> Out {
        type Output = Out;
        fn call_once(&self, arg: Arg) -> Out {
            self(arg)
        }
    }
    impl<Arg1, Arg2, Out> FnOnce<(Arg1, Arg2)> for fn(Arg1, Arg2) -> Out {
        type Output = Out;
        fn call_once(&self, arg: (Arg1, Arg2)) -> Out {
            self(arg.0, arg.1)
        }
    }
    impl<Arg1, Arg2, Arg3, Out> FnOnce<(Arg1, Arg2, Arg3)> for fn(Arg1, Arg2, Arg3) -> Out {
        type Output = Out;
        fn call_once(&self, arg: (Arg1, Arg2, Arg3)) -> Out {
            self(arg.0, arg.1, arg.2)
        }
    }
}

mod try_trait {
    /// See [`std::ops::FromResidual`]
    trait FromResidual<R> {
        fn from_residual(x: R) -> Self;
    }

    /// See [`std::ops::Try`]
    trait Try {
        type Output;
        type Residual;
        fn from_output(x: Self::Output) -> Self;
        fn branch(&self) -> super::control_flow::ControlFlow<Self::Residual, Self::Output>;
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

    macro_rules! impl_iterator_range_int {
        ($($int_type: ident)*) => {
            use crate::option::Option;
            $(
                #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
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
