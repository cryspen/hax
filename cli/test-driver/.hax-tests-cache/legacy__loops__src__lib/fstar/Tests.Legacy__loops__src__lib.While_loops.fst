module Tests.Legacy__loops__src__lib.While_loops
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let f (_: Prims.unit) : u8 =
  let x:u8 = mk_u8 0 in
  let x:u8 =
    Rust_primitives.Hax.while_loop (fun x ->
          let x:u8 = x in
          x <. mk_u8 10 <: bool)
      (fun x ->
          let x:u8 = x in
          true)
      (fun x ->
          let x:u8 = x in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      x
      (fun x ->
          let x:u8 = x in
          let x:u8 = x +! mk_u8 3 in
          x)
  in
  x +! mk_u8 12

let while_invariant_decr (_: Prims.unit) : u8 =
  let x:u8 = mk_u8 0 in
  let x:u8 =
    Rust_primitives.Hax.while_loop (fun x ->
          let x:u8 = x in
          x <. mk_u8 10 <: bool)
      (fun x ->
          let x:u8 = x in
          b2t (x <=. mk_u8 10 <: bool))
      (fun x ->
          let x:u8 = x in
          Rust_primitives.Hax.Int.from_machine (mk_u8 10 -! x <: u8) <: Hax_lib.Int.t_Int)
      x
      (fun x ->
          let x:u8 = x in
          let x:u8 = x +! mk_u8 3 in
          x)
  in
  x +! mk_u8 12

let while_invariant_decr_rev (_: Prims.unit) : u8 =
  let x:u8 = mk_u8 0 in
  let x:u8 =
    Rust_primitives.Hax.while_loop (fun x ->
          let x:u8 = x in
          x <. mk_u8 10 <: bool)
      (fun x ->
          let x:u8 = x in
          b2t (x <=. mk_u8 10 <: bool))
      (fun x ->
          let x:u8 = x in
          Rust_primitives.Hax.Int.from_machine (mk_u8 10 -! x <: u8) <: Hax_lib.Int.t_Int)
      x
      (fun x ->
          let x:u8 = x in
          let x:u8 = x +! mk_u8 3 in
          x)
  in
  x +! mk_u8 12
