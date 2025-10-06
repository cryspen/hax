module Tests.Legacy__attributes.Issue_1276_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_S = | S : u8 -> t_S

let impl_S__f (self: t_S) (self_ self_0_ self_1_ self_2_: u8)
    : Prims.Pure Prims.unit
      (requires self._0 =. mk_u8 0 && self_ =. self_1_ && self_2_ =. mk_u8 9)
      (fun _ -> Prims.l_True) = ()
