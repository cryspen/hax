module Core_models.Ops.Function
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::FnOnce`]
class t_FnOnce (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_call_once_pre:self_: v_Self -> args: v_Args -> pred: Type0{true ==> pred};
  f_call_once_post:v_Self -> v_Args -> f_Output -> Type0;
  f_call_once:x0: v_Self -> x1: v_Args
    -> Prims.Pure f_Output (f_call_once_pre x0 x1) (fun result -> f_call_once_post x0 x1 result)
}

/// See [`std::ops::Fn`]
class t_FnMut (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_FnOnce v_Self v_Args;
  f_call_mut_pre:self_: v_Self -> args: v_Args -> pred: Type0{true ==> pred};
  f_call_mut_post:v_Self -> v_Args -> (_super_i0).f_Output -> Type0;
  f_call_mut:x0: v_Self -> x1: v_Args
    -> Prims.Pure (_super_i0).f_Output
        (f_call_mut_pre x0 x1)
        (fun result -> f_call_mut_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_Args:Type0) {|i: t_FnMut v_Self v_Args|} -> i._super_i0

/// See [`std::ops::Fn`]
class t_Fn (v_Self: Type0) (v_Args: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_FnMut v_Self v_Args;
  f_call_pre:self_: v_Self -> args: v_Args -> pred: Type0{true ==> pred};
  f_call_post:v_Self -> v_Args -> (_super_i0)._super_i0.f_Output -> Type0;
  f_call:x0: v_Self -> x1: v_Args
    -> Prims.Pure (_super_i0)._super_i0.f_Output
        (f_call_pre x0 x1)
        (fun result -> f_call_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_Args:Type0) {|i: t_Fn v_Self v_Args|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_Arg #v_Out: Type0) : t_FnOnce (v_Arg -> v_Out) v_Arg =
  {
    f_Output = v_Out;
    f_call_once_pre = (fun (self: (v_Arg -> v_Out)) (arg: v_Arg) -> true);
    f_call_once_post = (fun (self: (v_Arg -> v_Out)) (arg: v_Arg) (out: v_Out) -> true);
    f_call_once = fun (self: (v_Arg -> v_Out)) (arg: v_Arg) -> self arg
  }

unfold instance fnonce_arrow_binder t u
  : t_FnOnce (_:t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_Arg1 #v_Arg2 #v_Out: Type0) : t_FnOnce (v_Arg1 -> v_Arg2 -> v_Out) (v_Arg1 & v_Arg2) =
  {
    f_Output = v_Out;
    f_call_once_pre = (fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) -> true);
    f_call_once_post
    =
    (fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) (out: v_Out) -> true);
    f_call_once
    =
    fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) -> self arg._1 arg._2
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_Arg1 #v_Arg2 #v_Arg3 #v_Out: Type0)
    : t_FnOnce (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out) (v_Arg1 & v_Arg2 & v_Arg3) =
  {
    f_Output = v_Out;
    f_call_once_pre
    =
    (fun (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out)) (arg: (v_Arg1 & v_Arg2 & v_Arg3)) -> true);
    f_call_once_post
    =
    (fun
        (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out))
        (arg: (v_Arg1 & v_Arg2 & v_Arg3))
        (out: v_Out)
        ->
        true);
    f_call_once
    =
    fun (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out)) (arg: (v_Arg1 & v_Arg2 & v_Arg3)) ->
      self arg._1 arg._2 arg._3
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (#v_Arg #v_Out: Type0) : t_FnMut (v_Arg -> v_Out) v_Arg =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_call_mut_pre = (fun (self: (v_Arg -> v_Out)) (arg: v_Arg) -> true);
    f_call_mut_post = (fun (self: (v_Arg -> v_Out)) (arg: v_Arg) (out: v_Out) -> true);
    f_call_mut = fun (self: (v_Arg -> v_Out)) (arg: v_Arg) -> self arg
  }

unfold instance fnmut_arrow_binder t u
  : t_FnMut (_:t -> u) t = {
    f_Output = u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_mut = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_Arg1 #v_Arg2 #v_Out: Type0) : t_FnMut (v_Arg1 -> v_Arg2 -> v_Out) (v_Arg1 & v_Arg2) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_call_mut_pre = (fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) -> true);
    f_call_mut_post
    =
    (fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) (out: v_Out) -> true);
    f_call_mut
    =
    fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) -> self arg._1 arg._2
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_Arg1 #v_Arg2 #v_Arg3 #v_Out: Type0)
    : t_FnMut (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out) (v_Arg1 & v_Arg2 & v_Arg3) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_call_mut_pre
    =
    (fun (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out)) (arg: (v_Arg1 & v_Arg2 & v_Arg3)) -> true);
    f_call_mut_post
    =
    (fun
        (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out))
        (arg: (v_Arg1 & v_Arg2 & v_Arg3))
        (out: v_Out)
        ->
        true);
    f_call_mut
    =
    fun (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out)) (arg: (v_Arg1 & v_Arg2 & v_Arg3)) ->
      self arg._1 arg._2 arg._3
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (#v_Arg #v_Out: Type0) : t_Fn (v_Arg -> v_Out) v_Arg =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_call_pre = (fun (self: (v_Arg -> v_Out)) (arg: v_Arg) -> true);
    f_call_post = (fun (self: (v_Arg -> v_Out)) (arg: v_Arg) (out: v_Out) -> true);
    f_call = fun (self: (v_Arg -> v_Out)) (arg: v_Arg) -> self arg
  }

unfold instance fn_arrow_binder t u
  : t_Fn (_:t -> u) t = {
    f_Output = u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_Arg1 #v_Arg2 #v_Out: Type0) : t_Fn (v_Arg1 -> v_Arg2 -> v_Out) (v_Arg1 & v_Arg2) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_call_pre = (fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) -> true);
    f_call_post
    =
    (fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) (out: v_Out) -> true);
    f_call = fun (self: (v_Arg1 -> v_Arg2 -> v_Out)) (arg: (v_Arg1 & v_Arg2)) -> self arg._1 arg._2
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_Arg1 #v_Arg2 #v_Arg3 #v_Out: Type0)
    : t_Fn (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out) (v_Arg1 & v_Arg2 & v_Arg3) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_call_pre
    =
    (fun (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out)) (arg: (v_Arg1 & v_Arg2 & v_Arg3)) -> true);
    f_call_post
    =
    (fun
        (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out))
        (arg: (v_Arg1 & v_Arg2 & v_Arg3))
        (out: v_Out)
        ->
        true);
    f_call
    =
    fun (self: (v_Arg1 -> v_Arg2 -> v_Arg3 -> v_Out)) (arg: (v_Arg1 & v_Arg2 & v_Arg3)) ->
      self arg._1 arg._2 arg._3
  }
