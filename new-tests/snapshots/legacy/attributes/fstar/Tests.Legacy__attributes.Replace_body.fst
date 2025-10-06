module Tests.Legacy__attributes.Replace_body
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let f (x y: u8) : u8 = magic x

type t_Foo = | Foo : t_Foo

let impl_Foo__assoc_fn (self: t_Foo) (x: u8) : Prims.unit = (magic (self <: t_Foo)) x

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Alloc.String.t_ToString t_Foo =
  {
    f_to_string_pre = (fun (self: t_Foo) -> true);
    f_to_string_post = (fun (self: t_Foo) (out: Alloc.String.t_String) -> true);
    f_to_string = fun (self: t_Foo) -> "The type was t_Foo"
  }
