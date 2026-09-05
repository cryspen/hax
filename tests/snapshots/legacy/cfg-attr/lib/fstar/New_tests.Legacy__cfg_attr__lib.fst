module New_tests.Legacy__cfg_attr__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

type t_Counter = { f_n:usize }

let impl_Counter__get (self: t_Counter)
    : Prims.Pure usize (requires self.f_n <. mk_usize 5) (fun _ -> Prims.l_True) = self.f_n

let impl_Counter__get_ensures (self: t_Counter)
    : Prims.Pure usize
      Prims.l_True
      (ensures
        fun result ->
          let result:usize = result in
          result =. self.f_n) = self.f_n

/// The `cfg_attr` predicate is preserved, not inlined: this
/// precondition shows up in the F\\* extraction only.
let impl_Counter__get_fstar_only (self: t_Counter)
    : Prims.Pure usize (requires self.f_n <. mk_usize 5) (fun _ -> Prims.l_True) = self.f_n

/// A `cfg_attr` may carry several attributes: only the hax ones are
/// rewritten.
let impl_Counter__get_inline (self: t_Counter)
    : Prims.Pure usize (requires self.f_n <. mk_usize 5) (fun _ -> Prims.l_True) = self.f_n

class t_Double (v_Self: Type0) = {
  f_double_pre:self_: v_Self -> x: u8 -> pred: prop{x <. mk_u8 100 ==> pred};
  f_double_post:self_: v_Self -> x: u8 -> result: u8 -> pred: prop{pred ==> result >=. x};
  f_double:x0: v_Self -> x1: u8
    -> Prims.Pure u8 (f_double_pre x0 x1) (fun result -> f_double_post x0 x1 result);
  f_double_fstar_only_pre:self_: v_Self -> x: u8 -> pred: prop{x <. mk_u8 100 ==> pred};
  f_double_fstar_only_post:v_Self -> u8 -> u8 -> prop;
  f_double_fstar_only:x0: v_Self -> x1: u8
    -> Prims.Pure u8
        (f_double_fstar_only_pre x0 x1)
        (fun result -> f_double_fstar_only_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Double_for_Counter: t_Double t_Counter =
  {
    f_double_pre = (fun (self_: t_Counter) (x: u8) -> x <. mk_u8 100);
    f_double_post = (fun (self_: t_Counter) (x: u8) (result: u8) -> result >=. x);
    f_double = (fun (self: t_Counter) (x: u8) -> x +! x);
    f_double_fstar_only_pre = (fun (self_: t_Counter) (x: u8) -> x <. mk_u8 100);
    f_double_fstar_only_post = (fun (self: t_Counter) (x: u8) (out: u8) -> true);
    f_double_fstar_only = fun (self: t_Counter) (x: u8) -> x +! x
  }
