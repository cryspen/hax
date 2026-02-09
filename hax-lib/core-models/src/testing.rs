pub trait Inject {
    type Model;
    fn inject(&self) -> Self::Model;
}

impl<Args, Out, F: Fn(Args) -> Out> crate::ops::function::FnOnce<Args> for F {
    type Output = Out;
    fn call_once(&self, args: Args) -> Out {
        self(args)
    }
}

impl <T: Inject> Inject for &T {
    type Model = T::Model;

    fn inject(&self) -> Self::Model {
        (*self).inject()
    }
}

macro_rules! inject_as_self {
    ($($t:ty)*) => {
        $(
            impl Inject for $t {
                type Model = $t;
                fn inject(&self) -> $t {
                    *self
                }
            }
        )*
    }
}

inject_as_self! {u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize bool}
