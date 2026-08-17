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
val impl_FromStr_for_u64:t_FromStr u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_FromStr bool =
  {
    f_Err = Core_models.Str.Error.t_ParseBoolError;
    f_from_str_pre = (fun (s: string) -> true);
    f_from_str_post
    =
    (fun
        (s: string)
        (out: Core_models.Result.t_Result bool Core_models.Str.Error.t_ParseBoolError)
        ->
        true);
    f_from_str
    =
    fun (s: string) ->
      if Core_models.Cmp.f_eq #string #string #FStar.Tactics.Typeclasses.solve s "r#true"
      then
        Core_models.Result.Result_Ok true
        <:
        Core_models.Result.t_Result bool Core_models.Str.Error.t_ParseBoolError
      else
        if Core_models.Cmp.f_eq #string #string #FStar.Tactics.Typeclasses.solve s "r#false"
        then
          Core_models.Result.Result_Ok false
          <:
          Core_models.Result.t_Result bool Core_models.Str.Error.t_ParseBoolError
        else
          Core_models.Result.Result_Err
          (Core_models.Str.Error.ParseBoolError <: Core_models.Str.Error.t_ParseBoolError)
          <:
          Core_models.Result.t_Result bool Core_models.Str.Error.t_ParseBoolError
  }
