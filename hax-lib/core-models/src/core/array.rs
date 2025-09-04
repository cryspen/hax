use super::primitives::array::*;

struct TryFromSliceError;

// Putting this in an impl raises 2 issues:
// - Rust refuses this because the const N would be unconstrained (it is unused in the definition of Array)
// - We would have a different impl disambiguator than the one in real core (or have to define exactly the same number of impls)
// We also have the issue of function types (that is made worse by https://github.com/cryspen/hax/issues/785)
#[hax_lib::fstar::replace("
let impl_23__map #a n #b (arr: t_Array a n) (f: a -> b): t_Array b n 
  = map_array arr f

let impl_23__as_slice #a len (arr: t_Array a len): t_Slice a = arr

assume val from_fn #a len (f: (x:usize{x <. len}) -> a): Pure (t_Array a len) (requires True) (ensures (fun a -> forall i. Seq.index a i == f (sz i)))
")]
pub fn map<T: Clone, const N: usize, F, U: Clone>(_s: Array<T, N>, _f: F) -> Array<U, N>
where
    F: FnMut(T) -> U,
{
    todo!()
}
