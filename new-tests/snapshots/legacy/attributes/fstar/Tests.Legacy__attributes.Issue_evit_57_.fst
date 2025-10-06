module Tests.Legacy__attributes.Issue_evit_57_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Foo = | Foo : t_Foo

let impl_Foo__f (self: t_Foo) : Prims.Pure Prims.unit (requires true) (fun _ -> Prims.l_True) = ()
