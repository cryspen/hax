/// Immutable clonable sequences

#[hax_lib::opaque]
#[derive(Clone)]
pub struct Seq<T: Clone>(Vec<T>);

/// Length of a sequence
#[hax_lib::opaque]
pub fn length<T: Clone>(s: &Seq<T>) -> usize {
    s.0.len()
}

pub struct FSeq<T, const SZ: usize>([T; SZ]);

/// Create a sequence with a constant
#[hax_lib::opaque]
/* #[hax_lib::ensures(|result| length(&result) == n)] */
pub fn seq_from_elem<T: Clone>(n: usize, constant: T) -> Seq<T> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v[i] = constant.clone()
    }
    Seq(v)
}

/// Create a sequence with a function
#[hax_lib::opaque]
/* #[hax_lib::ensures(|result| length(&result) == n)] */
pub fn seq_from_fn<T: Clone, F: Fn(usize) -> T>(n: usize, f: F) -> Seq<T> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v[i] = f(i)
    }
    Seq(v)
}

/// Index into a sequence
#[hax_lib::opaque]
pub fn index<T: Clone>(s: &Seq<T>, i: usize) -> &T {
    &s.0[i]
}

/// Update a sequence
#[hax_lib::opaque]
#[hax_lib::requires(i < length(&s))]
pub fn update<T: Clone>(s: Seq<T>, i: usize, v: T) -> Seq<T> {
    let mut r = s.clone();
    r.0[i] = v;
    r
}
