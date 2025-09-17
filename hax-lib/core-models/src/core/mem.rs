#![allow(unused_variables)]

#[hax_lib::fstar::before("open Rust_primitives.Integers")]
#[hax_lib::opaque]
pub fn forget<T>(t: T) {
    panic!()
}

#[hax_lib::opaque]
pub fn forget_unsized<T>(t: T) {
    panic!()
}

#[hax_lib::opaque]
pub fn size_of<T>() -> usize {
    panic!()
}

#[hax_lib::opaque]
pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

#[hax_lib::opaque]
pub fn min_align_of<T>() -> usize {
    panic!()
}

#[hax_lib::opaque]
pub fn min_align_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

#[hax_lib::opaque]
pub fn align_of<T>() -> usize {
    panic!()
}

#[hax_lib::opaque]
pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

#[hax_lib::opaque]
pub unsafe fn align_of_val_raw<T>(val: T) -> usize {
    panic!()
}

#[hax_lib::opaque]
pub fn needs_drop<T: ?Sized>() -> bool {
    panic!()
}

#[hax_lib::opaque]
pub unsafe fn uninitialized<T>() -> T {
    panic!()
}

#[hax_lib::opaque]
pub fn swap<T>(x: &mut T, y: &mut T) {
    panic!()
}

#[hax_lib::opaque]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    panic!()
}

#[hax_lib::opaque]
pub fn drop<T>(_x: T) {}

#[hax_lib::opaque]
pub fn copy<T: Copy>(x: &T) -> T {
    *x
}

#[hax_lib::opaque]
pub unsafe fn transmute_copy<Src, Dst>(src: &Src) -> Dst {
    panic!()
}

#[hax_lib::opaque]
pub fn variant_count<T>() -> usize {
    panic!()
}

#[hax_lib::opaque]
pub unsafe fn zeroed<T>() -> T {
    panic!()
}

mod manually_drop {
    pub struct ManuallyDrop<T: ?Sized> {
        value: T,
    }
}
