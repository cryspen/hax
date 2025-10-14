module Core_models.Ops.Function
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_FnOnce (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_call_once_pre:self_: v_Self -> args: v_Args -> pred: Type0{true ==> pred};
  f_call_once_post:v_Self -> v_Args -> f_Output -> Type0;
  f_call_once:x0: v_Self -> x1: v_Args
    -> Prims.Pure f_Output (f_call_once_pre x0 x1) (fun result -> f_call_once_post x0 x1 result)
}

class t_Fn (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_FnOnce v_Self v_Args;
  f_call_pre:self_: v_Self -> args: v_Args -> pred: Type0{true ==> pred};
  f_call_post:v_Self -> v_Args -> (_super_i0).f_Output -> Type0;
  f_call:x0: v_Self -> x1: v_Args
    -> Prims.Pure (_super_i0).f_Output (f_call_pre x0 x1) (fun result -> f_call_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_Args:Type0) {|i: t_Fn v_Self v_Args|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_Args #v_Out: Type0) : t_FnOnce (v_Args -> v_Out) v_Args =
  {
    f_Output = v_Out;
    f_call_once_pre = (fun (self: (v_Args -> v_Out)) (args: v_Args) -> true);
    f_call_once_post = (fun (self: (v_Args -> v_Out)) (args: v_Args) (out: v_Out) -> true);
    f_call_once = fun (self: (v_Args -> v_Out)) (args: v_Args) -> self args
  }

unfold instance fnonce_arrow_binder t u
  : t_FnOnce (_:t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }
