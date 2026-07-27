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

unfold instance fnonce_arrow_binder t u
  : t_FnOnce (_:t -> u) t = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_once = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

unfold instance fnmut_arrow_binder t u
  : t_FnMut (_:t -> u) t = {
    _super_i0 = fnonce_arrow_binder t u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call_mut = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

unfold instance fn_arrow_binder t u
  : t_Fn (_:t -> u) t = {
    _super_i0 = fnmut_arrow_binder t u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (_:t -> u)) (x1: t) (res: u) -> res == x0 x1);
    f_call = (fun (x0: (_:t -> u)) (x1: t) -> x0 x1);
  }

unfold instance fnonce_arrow_binder2 t1 t2 u
  : t_FnOnce (t1 -> t2 -> u) (t1 & t2) = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) (res: u) -> res == x0 x1._1 x1._2);
    f_call_once = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) -> x0 x1._1 x1._2);
  }

unfold instance fnmut_arrow_binder2 t1 t2 u
  : t_FnMut (t1 -> t2 -> u) (t1 & t2) = {
    _super_i0 = fnonce_arrow_binder2 t1 t2 u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) (res: u) -> res == x0 x1._1 x1._2);
    f_call_mut = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) -> x0 x1._1 x1._2);
  }

unfold instance fn_arrow_binder2 t1 t2 u
  : t_Fn (t1 -> t2 -> u) (t1 & t2) = {
    _super_i0 = fnmut_arrow_binder2 t1 t2 u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) (res: u) -> res == x0 x1._1 x1._2);
    f_call = (fun (x0: (t1 -> t2 -> u)) (x1: (t1 & t2)) -> x0 x1._1 x1._2);
  }

unfold instance fnonce_arrow_binder3 t1 t2 t3 u
  : t_FnOnce (t1 -> t2 -> t3 -> u) (t1 & t2 & t3) = {
    f_Output = u;
    f_call_once_pre = (fun _ _ -> true);
    f_call_once_post = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) (res: u) -> res == x0 x1._1 x1._2 x1._3);
    f_call_once = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) -> x0 x1._1 x1._2 x1._3);
  }

unfold instance fnmut_arrow_binder3 t1 t2 t3 u
  : t_FnMut (t1 -> t2 -> t3 -> u) (t1 & t2 & t3) = {
    _super_i0 = fnonce_arrow_binder3 t1 t2 t3 u;
    f_call_mut_pre = (fun _ _ -> true);
    f_call_mut_post = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) (res: u) -> res == x0 x1._1 x1._2 x1._3);
    f_call_mut = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) -> x0 x1._1 x1._2 x1._3);
  }

unfold instance fn_arrow_binder3 t1 t2 t3 u
  : t_Fn (t1 -> t2 -> t3 -> u) (t1 & t2 & t3) = {
    _super_i0 = fnmut_arrow_binder3 t1 t2 t3 u;
    f_call_pre = (fun _ _ -> true);
    f_call_post = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) (res: u) -> res == x0 x1._1 x1._2 x1._3);
    f_call = (fun (x0: (t1 -> t2 -> t3 -> u)) (x1: (t1 & t2 & t3)) -> x0 x1._1 x1._2 x1._3);
  }
