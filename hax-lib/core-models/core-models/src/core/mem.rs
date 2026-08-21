#![allow(unused_variables)]

use super::marker::Copy;

/// See [`std::mem::forget`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn forget<T>(t: T) {
    panic!()
}

/// See [`std::mem::forget_unsized`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn forget_unsized<T>(t: T) {
    panic!()
}

/// See [`std::mem::size_of`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn size_of<T>() -> usize {
    panic!()
}

/// See [`std::mem::size_of_val`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

/// See [`std::mem::min_align_of`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn min_align_of<T>() -> usize {
    panic!()
}

/// See [`std::mem::min_align_of_val`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn min_align_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

/// See [`std::mem::align_of`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn align_of<T>() -> usize {
    panic!()
}

/// See [`std::mem::align_of_val`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
    panic!()
}

/// See [`std::mem::align_of_val_raw`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub unsafe fn align_of_val_raw<T>(val: T) -> usize {
    panic!()
}

/// See [`std::mem::needs_drop`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn needs_drop<T: ?Sized>() -> bool {
    panic!()
}

/// See [`std::mem::uninitialized`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub unsafe fn uninitialized<T>() -> T {
    panic!()
}

/// See [`std::mem::swap`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn swap<T>(x: &mut T, y: &mut T) {
    panic!()
}

/// See [`std::mem::replace`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn replace<T>(dest: &mut T, src: T) -> T {
    panic!()
}

/// See [`std::mem::drop`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn drop<T>(_x: T) {}

/// See [`std::mem::take`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub unsafe fn take<T>(x: &mut T) -> T {
    panic!()
}

/// See [`std::mem::transmute_copy`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub unsafe fn transmute_copy<Src, Dst>(src: &Src) -> Dst {
    panic!()
}

/// See [`std::mem::variant_count`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn variant_count<T>() -> usize {
    panic!()
}

/// See [`std::mem::zeroed`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub unsafe fn zeroed<T>() -> T {
    panic!()
}

/// See [`std::mem::transmute`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub unsafe fn transmute<Src, Dst>(src: Src) -> Dst {
    panic!()
}

mod manually_drop {
    pub struct ManuallyDrop<T: ?Sized> {
        value: T,
    }
}
