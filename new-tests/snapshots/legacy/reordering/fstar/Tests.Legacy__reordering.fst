module Tests.Legacy__reordering
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let no_dependency_1_ (_: Prims.unit) : Prims.unit = ()

let no_dependency_2_ (_: Prims.unit) : Prims.unit = ()

type t_Foo =
  | Foo_A : t_Foo
  | Foo_B : t_Foo

let f (_: u32) : t_Foo = Foo_A <: t_Foo

type t_Bar = | Bar : t_Foo -> t_Bar

let g (_: Prims.unit) : t_Bar = Bar (f (mk_u32 32)) <: t_Bar

let t_Foo_cast_to_repr (x: t_Foo) : isize =
  match x <: t_Foo with
  | Foo_A  -> mk_isize 0
  | Foo_B  -> mk_isize 1
