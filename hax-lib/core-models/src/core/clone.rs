// In F* we replace the definition to have the equality a value
// and its clone.
// We need to consume self, instead of taking a reference, otherwise Rust would
// not allow returning an owned Self. This is the same after going through hax.
#[hax_lib::fstar::replace(
    "class t_Clone self = {
  f_clone_pre: self -> Type0;
  f_clone_post: self -> self -> Type0;
  f_clone: x:self -> r:self {x == r}
}"
)]
trait Clone {
    fn clone(self) -> Self;
}

// In our model, everything is clonable
impl<T> Clone for T {
    fn clone(self) -> Self {
        self
    }
}
