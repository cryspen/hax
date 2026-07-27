pub trait Inject {
    type Model;
    fn inject(&self) -> Self::Model;
}

impl<T: Inject> Inject for &T {
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

impl<T: Inject> Inject for Option<T> {
    type Model = crate::option::Option<T::Model>;
    fn inject(&self) -> Self::Model {
        match self {
            Some(v) => crate::option::Option::Some(v.inject()),
            None => crate::option::Option::None,
        }
    }
}

impl<T: Inject, E: Inject> Inject for Result<T, E> {
    type Model = crate::result::Result<T::Model, E::Model>;
    fn inject(&self) -> Self::Model {
        match self {
            Ok(v) => crate::result::Result::Ok(v.inject()),
            Err(e) => crate::result::Result::Err(e.inject()),
        }
    }
}

impl Inject for std::cmp::Ordering {
    type Model = crate::cmp::Ordering;
    fn inject(&self) -> Self::Model {
        match self {
            std::cmp::Ordering::Less => crate::cmp::Ordering::Less,
            std::cmp::Ordering::Equal => crate::cmp::Ordering::Equal,
            std::cmp::Ordering::Greater => crate::cmp::Ordering::Greater,
        }
    }
}

impl<T: Inject> Inject for std::cmp::Reverse<T> {
    type Model = crate::cmp::Reverse<T::Model>;
    fn inject(&self) -> Self::Model {
        crate::cmp::Reverse(self.0.inject())
    }
}

impl Inject for std::num::TryFromIntError {
    type Model = crate::num::error::TryFromIntError;
    fn inject(&self) -> Self::Model {
        crate::num::error::TryFromIntError(())
    }
}

impl<'a, T> Inject for &'a [T] {
    type Model = &'a [T];
    fn inject(&self) -> Self::Model {
        self
    }
}

impl<A: Inject, B: Inject> Inject for (A, B) {
    type Model = (A::Model, B::Model);
    fn inject(&self) -> Self::Model {
        (self.0.inject(), self.1.inject())
    }
}
