module Test_driver
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

///\n\nThis is an extension trait for the following impl:\n```rust ,ignore\n#[extension(pub trait ExtIntoIterator)]\nimpl< T, U : Iterator < Item = T > > for U\n\n```
class t_ExtIntoIterator (v_Self: Type0) (v_T: Type0) (v_U: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9794153458006678696:Core.Iter.Traits.Iterator.t_Iterator
  v_U;
  f_expect_le_one_pre:v_Self -> Type0;
  f_expect_le_one_post:v_Self -> Core.Result.t_Result (Core.Option.t_Option v_T) Anyhow.t_Error
    -> Type0;
  f_expect_le_one:x0: v_Self
    -> Prims.Pure (Core.Result.t_Result (Core.Option.t_Option v_T) Anyhow.t_Error)
        (f_expect_le_one_pre x0)
        (fun result -> f_expect_le_one_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) (v_U:Type0) {|i: t_ExtIntoIterator v_Self v_T v_U|} -> i._super_9794153458006678696
