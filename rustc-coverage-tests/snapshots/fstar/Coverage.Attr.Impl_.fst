module Coverage.Attr.Impl_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_MyStruct = | MyStruct : t_MyStruct

let impl_MyStruct__off_inherit (_: Prims.unit) : Prims.unit = ()

let impl_MyStruct__off_on (_: Prims.unit) : Prims.unit = ()

let impl_MyStruct__off_off (_: Prims.unit) : Prims.unit = ()

let impl_MyStruct__on_inherit (_: Prims.unit) : Prims.unit = ()

let impl_MyStruct__on_on (_: Prims.unit) : Prims.unit = ()

let impl_MyStruct__on_off (_: Prims.unit) : Prims.unit = ()

class t_MyTrait (v_Self: Type0) = {
  f_method_pre:Prims.unit -> Type0;
  f_method_post:Prims.unit -> Prims.unit -> Type0;
  f_method:x0: Prims.unit
    -> Prims.Pure Prims.unit (f_method_pre x0) (fun result -> f_method_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_MyTrait_for_MyStruct: t_MyTrait t_MyStruct =
  {
    f_method_pre = (fun (_: Prims.unit) -> true);
    f_method_post = (fun (_: Prims.unit) (out: Prims.unit) -> true);
    f_method = fun (_: Prims.unit) -> ()
  }

let main (_: Prims.unit) : Prims.unit = ()
