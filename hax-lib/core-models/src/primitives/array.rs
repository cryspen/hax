use crate::base::seq::*;

pub struct Slice<T: Clone>(Seq<T>);

pub struct Array<T, const N: usize>(FSeq<T, N>);

/// Length of a slice
pub fn slice_length<T: Clone>(s: &Slice<T>) -> usize {
    length(&s.0)
}

/// Index of a slice
pub fn slice_index<T: Clone>(s: &Slice<T>, i: usize) -> &T {
    index(&s.0, i)
}
