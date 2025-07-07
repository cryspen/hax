use std::marker::PhantomData;
pub trait RefKind {
    type Ref<U: 'static + ?Sized>: Sized;
}

pub struct Borrow<'a>(PhantomData<&'a ()>);
pub struct MutBorrow<'a>(PhantomData<&'a ()>);
// pub struct Own;

impl<'a> RefKind for Borrow<'a> {
    type Ref<T: 'static + ?Sized> = &'a T;
}
impl<'a> RefKind for MutBorrow<'a> {
    type Ref<T: 'static + ?Sized> = &'a mut T;
}
// impl<'a> RefKind for Own {
//     type Ref<T: 'static + ?Sized> = T;
// }
