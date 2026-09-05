module Alloc.Boxed
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

type t_Box (v_T: Type0) = | Box : v_T -> t_Box v_T

let impl__new (#v_T: Type0) (v: v_T) : v_T = v

/// See [`std::ops::Deref`] for `Box<T>`
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Core_models.Ops.Deref.t_Deref (t_Box v_T) =
  {
    f_Target = v_T;
    f_deref_pre = (fun (self: t_Box v_T) -> true);
    f_deref_post = (fun (self: t_Box v_T) (out: v_T) -> true);
    f_deref = fun (self: t_Box v_T) -> self._0
  }

/// See [`std::clone::Clone`] for `Box<T>`
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
    : Core_models.Clone.t_Clone (t_Box v_T) =
  {
    f_clone_pre = (fun (self: t_Box v_T) -> true);
    f_clone_post = (fun (self: t_Box v_T) (out: t_Box v_T) -> true);
    f_clone
    =
    fun (self: t_Box v_T) ->
      Box (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve self._0) <: t_Box v_T
  }
