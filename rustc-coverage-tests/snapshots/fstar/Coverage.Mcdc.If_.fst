module Coverage.Mcdc.If_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let say (message: string) : Prims.unit =
  let _:string = Core.Hint.black_box #string message in
  ()

let mcdc_check_neither (a b: bool) : Prims.unit =
  if a && b
  then
    let _:Prims.unit = say "a and b" in
    ()
  else
    let _:Prims.unit = say "not both" in
    ()

let mcdc_check_a (a b: bool) : Prims.unit =
  if a && b
  then
    let _:Prims.unit = say "a and b" in
    ()
  else
    let _:Prims.unit = say "not both" in
    ()

let mcdc_check_b (a b: bool) : Prims.unit =
  if a && b
  then
    let _:Prims.unit = say "a and b" in
    ()
  else
    let _:Prims.unit = say "not both" in
    ()

let mcdc_check_both (a b: bool) : Prims.unit =
  if a && b
  then
    let _:Prims.unit = say "a and b" in
    ()
  else
    let _:Prims.unit = say "not both" in
    ()

let mcdc_check_tree_decision (a b c: bool) : Prims.unit =
  if a && (b || c)
  then
    let _:Prims.unit = say "pass" in
    ()
  else
    let _:Prims.unit = say "reject" in
    ()

let mcdc_check_not_tree_decision (a b c: bool) : Prims.unit =
  if (a || b) && c
  then
    let _:Prims.unit = say "pass" in
    ()
  else
    let _:Prims.unit = say "reject" in
    ()

let mcdc_nested_if (a b c: bool) : Prims.unit =
  if a || b
  then
    let _:Prims.unit = say "a or b" in
    if b && c
    then
      let _:Prims.unit = say "b and c" in
      ()
  else
    let _:Prims.unit = say "neither a nor b" in
    ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = mcdc_check_neither false false in
  let _:Prims.unit = mcdc_check_neither false true in
  let _:Prims.unit = mcdc_check_a true true in
  let _:Prims.unit = mcdc_check_a false true in
  let _:Prims.unit = mcdc_check_b true true in
  let _:Prims.unit = mcdc_check_b true false in
  let _:Prims.unit = mcdc_check_both false true in
  let _:Prims.unit = mcdc_check_both true true in
  let _:Prims.unit = mcdc_check_both true false in
  let _:Prims.unit = mcdc_check_tree_decision false true true in
  let _:Prims.unit = mcdc_check_tree_decision true true false in
  let _:Prims.unit = mcdc_check_tree_decision true false false in
  let _:Prims.unit = mcdc_check_tree_decision true false true in
  let _:Prims.unit = mcdc_check_not_tree_decision false true true in
  let _:Prims.unit = mcdc_check_not_tree_decision true true false in
  let _:Prims.unit = mcdc_check_not_tree_decision true false false in
  let _:Prims.unit = mcdc_check_not_tree_decision true false true in
  let _:Prims.unit = mcdc_nested_if true false true in
  let _:Prims.unit = mcdc_nested_if true true true in
  let _:Prims.unit = mcdc_nested_if true true false in
  ()
