pub mod control_flow {
    pub enum ControlFlow<C, B> {
        Continue(C),
        Break(B),
    }
}

pub mod index {

    trait Index {
        type Output;
        fn index(&self, i: usize) -> &Self::Output;
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
  } "
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
