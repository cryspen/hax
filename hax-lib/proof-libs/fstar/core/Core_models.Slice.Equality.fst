module Core_models.Slice.Equality
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': #v_T: Type0 -> #v_U: Type0 -> v_N: usize -> {| i0: Core_models.Cmp.t_PartialEq v_T v_U |}
  -> Core_models.Cmp.t_PartialEq (t_Slice v_T) (t_Array v_U v_N)

unfold
let impl
      (#v_T #v_U: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_U)
     = impl' #v_T #v_U v_N #i0
