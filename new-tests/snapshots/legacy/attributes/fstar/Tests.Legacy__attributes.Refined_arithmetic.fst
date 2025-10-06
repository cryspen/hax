module Tests.Legacy__attributes.Refined_arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Foo = | Foo : u8 -> t_Foo

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Arith.t_Add t_Foo t_Foo =
  {
    f_Output = t_Foo;
    f_add_pre = (fun (self_: t_Foo) (rhs: t_Foo) -> self_._0 <. (mk_u8 255 -! rhs._0 <: u8));
    f_add_post = (fun (self: t_Foo) (rhs: t_Foo) (out: t_Foo) -> true);
    f_add = fun (self: t_Foo) (rhs: t_Foo) -> Foo (self._0 +! rhs._0) <: t_Foo
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Arith.t_Mul t_Foo t_Foo =
  {
    f_Output = t_Foo;
    f_mul_pre
    =
    (fun (self_: t_Foo) (rhs: t_Foo) -> rhs._0 =. mk_u8 0 || self_._0 <. (mk_u8 255 /! rhs._0 <: u8)
    );
    f_mul_post = (fun (self: t_Foo) (rhs: t_Foo) (out: t_Foo) -> true);
    f_mul = fun (self: t_Foo) (rhs: t_Foo) -> Foo (self._0 *! rhs._0) <: t_Foo
  }
