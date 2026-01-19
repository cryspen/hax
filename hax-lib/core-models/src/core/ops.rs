pub mod arith {
    pub trait Add<Rhs = Self> {
        type Output;
        fn add(self, rhs: Rhs) -> Self::Output;
    }
    pub trait Sub<Rhs = Self> {
        type Output;
        fn sub(self, rhs: Rhs) -> Self::Output;
    }
    pub trait Mul<Rhs = Self> {
        type Output;
        fn mul(self, rhs: Rhs) -> Self::Output;
    }
    pub trait Div<Rhs = Self> {
        type Output;
        fn div(self, rhs: Rhs) -> Self::Output;
    }
    pub trait Neg {
        type Output;
        fn neg(self) -> Self::Output;
    }
    pub trait Rem<Rhs = Self> {
        type Output;
        fn rem(self, rhs: Rhs) -> Self::Output;
    }
    pub trait AddAssign<Rhs = Self> {
        type Output;
        fn add_assign(self, rhs: Rhs) -> Self::Output;
    }
    pub trait SubAssign<Rhs = Self> {
        type Output;
        fn sub_assign(self, rhs: Rhs) -> Self::Output;
    }
    pub trait MulAssign<Rhs = Self> {
        type Output;
        fn mul_assign(self, rhs: Rhs) -> Self::Output;
    }
    pub trait DivAssign<Rhs = Self> {
        type Output;
        fn div_assign(self, rhs: Rhs) -> Self::Output;
    }
    pub trait RemAssign<Rhs = Self> {
        type Output;
        fn rem_assign(self, rhs: Rhs) -> Self::Output;
    }
}

pub mod bit {
    trait Shr<Rhs = Self> {
        type Output;
        fn shr(self, rhs: Rhs) -> Self::Output;
    }
    trait Shl<Rhs = Self> {
        type Output;
        fn shl(self, rhs: Rhs) -> Self::Output;
    }
    trait BitXor<Rhs = Self> {
        type Output;
        fn bitxor(self, rhs: Rhs) -> Self::Output;
    }
    trait BitAnd<Rhs = Self> {
        type Output;
        fn bitand(self, rhs: Rhs) -> Self::Output;
    }
}

pub mod control_flow {
    pub enum ControlFlow<B, C> {
        Continue(C),
        Break(B),
    }
}

pub mod index {
    // TODO remove
    #[hax_lib::fstar::before("open Rust_primitives.Integers")]
    trait Index<Idx> {
        type Output;
        fn index(&self, i: Idx) -> &Self::Output;
    }
}

pub mod function {
    /* These instances provide implementations of the F* type classes corresponding to Fn traits for anonymous functions.
    This ensures that passing a closure where something implementing Fn works when translated to F* */
    #[hax_lib::fstar::after(
        "unfold instance fnonce_arrow t u
  : t_FnOnce (t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: t -> u) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: t -> u) (x1: t) -> x0 x1);
  } 
unfold instance fnonce_arrow_binder t u
  : t_FnOnce (_:t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }
"
    )]
    #[hax_lib::attributes]
    pub trait FnOnce<Args> {
        type Output;
        #[hax_lib::requires(true)]
        fn call_once(&self, args: Args) -> Self::Output;
    }
    #[hax_lib::attributes]
    pub trait Fn<Args>: FnOnce<Args> {
        #[hax_lib::requires(true)]
        fn call(&self, args: Args) -> Self::Output;
    }
}

mod try_trait {
    trait FromResidual<R> {
        fn from_residual(x: R) -> Self;
    }

    trait Try {
        type Output;
        type Residual;
        fn from_output(x: Self::Output) -> Self;
        fn branch(&self) -> super::control_flow::ControlFlow<Self::Residual, Self::Output>;
    }
}
