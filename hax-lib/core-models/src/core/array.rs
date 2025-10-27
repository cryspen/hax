struct TryFromSliceError;

// Dummy type to allow impls
#[hax_lib::exclude]
struct Array<T, const N: usize>([T; N]);

// Dummy impls to get the right disambiguator
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}
impl<T> Array<T, 0> {}

impl<T, const N: usize> Array<T, N> {
    pub fn map<U, F>(s: [T; N], f: F) -> [U; N]
    where
        F: crate::ops::function::FnOnce<T, Output = U>,
    {
        rust_primitives::slice::array_map(s, f)
    }
    pub fn as_slice(s: [T; N]) -> &'static [T] {
        rust_primitives::slice::array_as_slice(s)
    }
}

fn from_fn<T, const N: usize, F: crate::ops::function::FnOnce<usize, Output = T>>(f: F) -> [T; N] {
    rust_primitives::slice::array_from_fn(f)
}
