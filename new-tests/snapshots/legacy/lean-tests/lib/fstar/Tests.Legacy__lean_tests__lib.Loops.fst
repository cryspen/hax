module Tests.Legacy__lean_tests__lib.Loops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// @fail(extraction): proverif(HAX0008)
let loop1 (_: Prims.unit) : u32 =
  let (x: u32):u32 = mk_u32 0 in
  let x:u32 =
    Rust_primitives.Hax.Folds.fold_range (mk_u32 1)
      (mk_u32 10)
      (fun x temp_1_ ->
          let x:u32 = x in
          let _:u32 = temp_1_ in
          true)
      x
      (fun x i ->
          let x:u32 = x in
          let i:u32 = i in
          x +! i <: u32)
  in
  x

/// @fail(extraction): proverif(HAX0008)
let loop2 (_: Prims.unit) : u32 =
  let (x: u32):u32 = mk_u32 0 in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_u32 1)
      (mk_u32 10)
      (fun x temp_1_ ->
          let x:u32 = x in
          let _:u32 = temp_1_ in
          true)
      x
      (fun x i ->
          let x:u32 = x in
          let i:u32 = i in
          if i =. mk_u32 5 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break x
              <:
              Core.Ops.Control_flow.t_ControlFlow u32 (Prims.unit & u32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow u32 (Prims.unit & u32)) u32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (x +! i <: u32)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow u32 (Prims.unit & u32)) u32)
    <:
    Core.Ops.Control_flow.t_ControlFlow u32 u32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue x -> x
