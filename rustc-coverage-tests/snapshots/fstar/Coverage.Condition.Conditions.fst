module Coverage.Condition.Conditions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let simple_assign (a: bool) : Prims.unit =
  let x:bool = a in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_and (a b: bool) : Prims.unit =
  let x:bool = a && b in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_or (a b: bool) : Prims.unit =
  let x:bool = a || b in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_3_or_and (a b c: bool) : Prims.unit =
  let x:bool = a || b && c in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_3_and_or (a b c: bool) : Prims.unit =
  let x:bool = a && b || c in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let foo (a: bool) : bool = Core.Hint.black_box #bool a

let func_call (a b: bool) : Prims.unit =
  let _:bool = foo (a && b) in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = simple_assign true in
  let _:Prims.unit = simple_assign false in
  let _:Prims.unit = assign_and true false in
  let _:Prims.unit = assign_and true true in
  let _:Prims.unit = assign_and false false in
  let _:Prims.unit = assign_or true false in
  let _:Prims.unit = assign_or true true in
  let _:Prims.unit = assign_or false false in
  let _:Prims.unit = assign_3_or_and true false false in
  let _:Prims.unit = assign_3_or_and true true false in
  let _:Prims.unit = assign_3_or_and false false true in
  let _:Prims.unit = assign_3_or_and false true true in
  let _:Prims.unit = assign_3_and_or true false false in
  let _:Prims.unit = assign_3_and_or true true false in
  let _:Prims.unit = assign_3_and_or false false true in
  let _:Prims.unit = assign_3_and_or false true true in
  let _:Prims.unit = func_call true false in
  let _:Prims.unit = func_call true true in
  let _:Prims.unit = func_call false false in
  ()
