module Core_models.TypeClassPlaceHolder
(* This module defines a dummy type-class that acts as a placeholder for
resolution, when an argument is useless. See Core_models.Alloc.Borrow for example. *)

class t_Placeholder = {
  content : unit
}

instance placeholder : t_Placeholder = {
  content = ()
}
