module Coverage.Mcdc.Non_control_flow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let assign_and (a b: bool) : Prims.unit =
  let x:bool = a && b in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_or (a b: bool) : Prims.unit =
  let x:bool = a || b in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_3_ (a b c: bool) : Prims.unit =
  let x:bool = a || b && c in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let assign_3_bis (a b c: bool) : Prims.unit =
  let x:bool = a && b || c in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let right_comb_tree (a b c d e: bool) : Prims.unit =
  let x:bool = a && (b && (c && (d && e))) in
  let _:bool = Core.Hint.black_box #bool x in
  ()

let foo (a: bool) : bool = Core.Hint.black_box #bool a

let func_call (a b: bool) : Prims.unit =
  let _:bool = foo (a && b) in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = assign_and true false in
  let _:Prims.unit = assign_and true true in
  let _:Prims.unit = assign_and false false in
  let _:Prims.unit = assign_or true false in
  let _:Prims.unit = assign_or true true in
  let _:Prims.unit = assign_or false false in
  let _:Prims.unit = assign_3_ true false false in
  let _:Prims.unit = assign_3_ true true false in
  let _:Prims.unit = assign_3_ false false true in
  let _:Prims.unit = assign_3_ false true true in
  let _:Prims.unit = assign_3_bis true false false in
  let _:Prims.unit = assign_3_bis true true false in
  let _:Prims.unit = assign_3_bis false false true in
  let _:Prims.unit = assign_3_bis false true true in
  let _:Prims.unit = right_comb_tree false false false true true in
  let _:Prims.unit = right_comb_tree true false false true true in
  let _:Prims.unit = right_comb_tree true true true true true in
  let _:Prims.unit = func_call true false in
  let _:Prims.unit = func_call true true in
  let _:Prims.unit = func_call false false in
  ()
