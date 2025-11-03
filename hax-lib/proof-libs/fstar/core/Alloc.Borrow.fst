module Alloc.Borrow
open Core_models.TypeClassPlaceHolder

type t_Cow t = t

// the second argument is a hack for typeclasses resolution
let f_to_owned (#t : Type0) {| t_Placeholder |} (x:t) : t = x
