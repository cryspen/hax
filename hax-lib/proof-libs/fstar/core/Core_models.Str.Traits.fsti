module Core_models.Str.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_FromStr (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Err:Type0;
  f_from_str_pre:string -> Type0;
  f_from_str_post:string -> Core_models.Result.t_Result v_Self f_Err -> Type0;
  f_from_str:x0: string
    -> Prims.Pure (Core_models.Result.t_Result v_Self f_Err)
        (f_from_str_pre x0)
        (fun result -> f_from_str_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_FromStr u64
