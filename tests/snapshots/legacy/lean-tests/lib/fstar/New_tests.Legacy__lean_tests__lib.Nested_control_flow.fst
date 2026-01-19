module New_tests.Legacy__lean_tests__lib.Nested_control_flow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let nested_control_flow (_: Prims.unit) : Prims.unit =
  let x1:i32 = mk_i32 1 +! (if true then mk_i32 0 else mk_i32 1) in
  let x2:i32 = mk_i32 1 +! (match mk_i32 1, mk_i32 2 <: (i32 & i32) with | _ -> mk_i32 0) in
  let x:i32 = mk_i32 9 in
  let x3:i32 = mk_i32 1 +! (x +! mk_i32 1 <: i32) in
  ()

let explicit_hoisting (_: Prims.unit) : Prims.unit =
  let x1_tmp:i32 = if true then mk_i32 0 else mk_i32 1 in
  let x1:i32 = mk_i32 1 +! x1_tmp in
  let x2_tmp:i32 = match mk_i32 1, mk_i32 2 <: (i32 & i32) with | _ -> mk_i32 0 in
  let x2:i32 = mk_i32 1 +! x2_tmp in
  let x3_tmp_x:i32 = mk_i32 9 in
  let x3_tmp:i32 = x3_tmp_x +! mk_i32 1 in
  let x3:i32 = mk_i32 1 +! x3_tmp in
  ()

let complex_nesting (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let x1:i32 =
    if true
    then
      let y:i32 =
        if false
        then
          let z:i32 = match () <: Prims.unit with | _ -> mk_i32 9 in
          let z:i32 = mk_i32 1 +! z in
          z +! mk_i32 1
        else
          let z:i32 = mk_i32 9 in
          let z:i32 = z +! mk_i32 1 in
          z
      in
      let y:i32 = y +! mk_i32 1 in
      y +! mk_i32 1
    else mk_i32 0
  in
  let x1:i32 = x1 +! mk_i32 1 in
  let x2:i32 =
    match Core_models.Option.Option_Some (mk_i32 89) <: Core_models.Option.t_Option i32 with
    | Core_models.Option.Option_Some a ->
      let y:i32 = mk_i32 1 +! a in
      let y:i32 = y +! mk_i32 1 in
      if y =. mk_i32 0
      then
        let z:i32 = mk_i32 9 in
        let z:i32 = (z +! y <: i32) +! mk_i32 1 in
        z
      else mk_i32 10
    | Core_models.Option.Option_None  ->
      let y:i32 =
        if false
        then mk_i32 9
        else
          let z:i32 = mk_i32 9 in
          let z:i32 = z +! mk_i32 1 in
          z +! mk_i32 9
      in
      let y:i32 = y +! mk_i32 1 in
      y
  in
  (() <: Prims.unit), () <: (Prims.unit & Prims.unit)
