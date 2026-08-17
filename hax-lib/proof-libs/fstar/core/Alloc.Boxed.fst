module Alloc.Boxed
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Box (v_T: Type0) = | Box : v_T -> t_Box v_T

let impl__new (#v_T: Type0) (v: v_T) : v_T = v

/// See [`std::boxed::Box::new_in`]. The model has a single heap, so the
/// allocator argument is ignored. The `A: Allocator` bound is omitted
/// on purpose: extraction erases `Box`'s allocator clause at call
/// sites, so a model that kept the bound would expect a dictionary
/// nobody passes.
let impl__new_in (#v_T #v_A: Type0) (x: v_T) (e_alloc: v_A) : v_T = x

/// See [`std::boxed::Box::into_inner`]. With boxes erased this is the
/// identity, exactly like `new` in the other direction.
let impl__into_inner (#v_T: Type0) (boxed: v_T) : v_T = boxed

/// See [`std::boxed::Box::map`]. Real `map` reuses the allocation when
/// the layouts match; with boxes erased only the value transformation
/// is observable.
let impl__map
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (this: v_T)
      (f: v_F)
    : v_U =
  Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (this <: v_T)

/// See [`std::boxed::Box::into_boxed_slice`]: the one-element slice
/// holding `boxed`.
let impl__into_boxed_slice (#v_T: Type0) (boxed: v_T) : t_Slice v_T =
  (let list = [boxed] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list)
  <:
  t_Slice v_T
