module Coverage.Mcdc.Nested_if
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let say (message: string) : Prims.unit =
  let _:string = Core.Hint.black_box #string message in
  ()

let nested_if_in_condition (a b c: bool) : Prims.unit =
  if a && (if b || c then true else false)
  then
    let _:Prims.unit = say "yes" in
    ()
  else
    let _:Prims.unit = say "no" in
    ()

let doubly_nested_if_in_condition (a b c d: bool) : Prims.unit =
  if a && (if b || (if c && d then true else false) then false else true)
  then
    let _:Prims.unit = say "yes" in
    ()
  else
    let _:Prims.unit = say "no" in
    ()

let nested_single_condition_decision (a b: bool) : Prims.unit =
  if a && (if b then false else true)
  then
    let _:Prims.unit = say "yes" in
    ()
  else
    let _:Prims.unit = say "no" in
    ()

let nested_in_then_block_in_condition (a b c d e: bool) : Prims.unit =
  if a && (if b || c then if d && e then true else false else false)
  then
    let _:Prims.unit = say "yes" in
    ()
  else
    let _:Prims.unit = say "no" in
    ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = nested_if_in_condition true false false in
  let _:Prims.unit = nested_if_in_condition true true true in
  let _:Prims.unit = nested_if_in_condition true false true in
  let _:Prims.unit = nested_if_in_condition false true true in
  let _:Prims.unit = doubly_nested_if_in_condition true false false true in
  let _:Prims.unit = doubly_nested_if_in_condition true true true true in
  let _:Prims.unit = doubly_nested_if_in_condition true false true true in
  let _:Prims.unit = doubly_nested_if_in_condition false true true true in
  let _:Prims.unit = nested_single_condition_decision true true in
  let _:Prims.unit = nested_single_condition_decision true false in
  let _:Prims.unit = nested_single_condition_decision false false in
  let _:Prims.unit = nested_in_then_block_in_condition false false false false false in
  let _:Prims.unit = nested_in_then_block_in_condition true false false false false in
  let _:Prims.unit = nested_in_then_block_in_condition true true false false false in
  let _:Prims.unit = nested_in_then_block_in_condition true false true false false in
  let _:Prims.unit = nested_in_then_block_in_condition true false true true false in
  let _:Prims.unit = nested_in_then_block_in_condition true false true false true in
  let _:Prims.unit = nested_in_then_block_in_condition true false true true true in
  ()
