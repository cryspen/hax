#![allow(unused_variables)]

use super::marker::Copy;

/// See [`std::mem::forget`]
#[hax_lib::opaque]
pub fn forget<T>(t: T) {
    panic!()
}

/// See [`std::mem::forget_unsized`]
#[hax_lib::opaque]
pub fn forget_unsized<T>(t: T) {
    panic!()
}

/// See [`std::mem::size_of`]
#[hax_lib::opaque]
pub fn size_of<T>() -> usize {
    panic!()
}

/// See [`std::mem::size_of_val`]
#[hax_lib::opaque]
pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

/// See [`std::mem::min_align_of`]
#[hax_lib::opaque]
pub fn min_align_of<T>() -> usize {
    panic!()
}

/// See [`std::mem::min_align_of_val`]
#[hax_lib::opaque]
pub fn min_align_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

/// See [`std::mem::align_of`]
#[hax_lib::opaque]
pub fn align_of<T>() -> usize {
    panic!()
}

/// See [`std::mem::align_of_val`]
#[hax_lib::opaque]
pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

/// See [`std::mem::align_of_val_raw`]
#[hax_lib::opaque]
pub unsafe fn align_of_val_raw<T>(val: T) -> usize {
    panic!()
}

/// See [`std::mem::needs_drop`]
#[hax_lib::opaque]
pub fn needs_drop<T: ?Sized>() -> bool {
    panic!()
}

/// See [`std::mem::uninitialized`]
#[hax_lib::opaque]
pub unsafe fn uninitialized<T>() -> T {
    panic!()
}

/// See [`std::mem::swap`]
#[hax_lib::opaque]
pub fn swap<T>(x: &mut T, y: &mut T) {
    panic!()
}

/// See [`std::mem::replace`]
#[hax_lib::opaque]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    panic!()
}

/// See [`std::mem::drop`]
#[hax_lib::opaque]
pub fn drop<T>(_x: T) {}

/// See [`std::mem::take`]
#[hax_lib::opaque]
pub unsafe fn take<T>(x: &mut T) -> T {
    panic!()
}

/// See [`std::mem::transmute_copy`]
#[hax_lib::opaque]
pub unsafe fn transmute_copy<Src, Dst>(src: &Src) -> Dst {
    panic!()
}

/// See [`std::mem::variant_count`]
#[hax_lib::opaque]
pub fn variant_count<T>() -> usize {
    panic!()
}

/// See [`std::mem::zeroed`]
#[hax_lib::opaque]
pub unsafe fn zeroed<T>() -> T {
    panic!()
}

/// See [`std::mem::transmute`]
#[hax_lib::opaque]
pub unsafe fn transmute<Src, Dst>(src: Src) -> Dst {
    panic!()
}

mod manually_drop {
    pub struct ManuallyDrop<T: ?Sized> {
        value: T,
    }
}
