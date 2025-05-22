module Core.Str.Traits

open Core.Result_Option_bundle

class t_FromStr (v_Self: Type) = {
  f_Err : Type ;
  f_from_str_pre : string -> Type0;
  f_from_str_post : string -> (t_Result v_Self f_Err) -> Type0;
  f_from_str : string -> t_Result v_Self f_Err
}

/// Typeclass implementations
[@FStar.Tactics.Typeclasses.tcinstance]
val impl_t_FromStr_u64 : t_FromStr Rust_primitives.Integers.u64
