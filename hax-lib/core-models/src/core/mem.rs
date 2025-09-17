#![allow(unused_variables)]

#[hax_lib::opaque]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    panic!()
}

mod manually_drop {
    pub struct ManuallyDrop<T: ?Sized> {
        value: T,
    }
}
