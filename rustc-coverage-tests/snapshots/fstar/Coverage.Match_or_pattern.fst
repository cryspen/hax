module Coverage.Match_or_pattern
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

let main (_: Prims.unit) : Prims.unit =
  let is_true:bool =
    (Core.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let (a: u8):u8 = mk_u8 0 in
  let (b: u8):u8 = mk_u8 0 in
  let a, b:(u8 & u8) =
    if is_true
    then
      let a:u8 = mk_u8 2 in
      let b:u8 = mk_u8 0 in
      a, b <: (u8 & u8)
    else a, b <: (u8 & u8)
  in
  let _:Prims.unit =
    match a, b <: (u8 & u8) with
    | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 2
    | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 3
    | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 2
    | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 3 -> ()
    | _ -> ()
  in
  let a, b:(u8 & u8) =
    if is_true
    then
      let a:u8 = mk_u8 0 in
      let b:u8 = mk_u8 0 in
      a, b <: (u8 & u8)
    else a, b <: (u8 & u8)
  in
  let _:Prims.unit =
    match a, b <: (u8 & u8) with
    | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 2
    | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 3
    | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 2
    | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 3 -> ()
    | _ -> ()
  in
  let a, b:(u8 & u8) =
    if is_true
    then
      let a:u8 = mk_u8 2 in
      let b:u8 = mk_u8 2 in
      a, b <: (u8 & u8)
    else a, b <: (u8 & u8)
  in
  let _:Prims.unit =
    match a, b <: (u8 & u8) with
    | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 2
    | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 3
    | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 2
    | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 3 -> ()
    | _ -> ()
  in
  let a, b:(u8 & u8) =
    if is_true
    then
      let a:u8 = mk_u8 0 in
      let b:u8 = mk_u8 2 in
      a, b <: (u8 & u8)
    else a, b <: (u8 & u8)
  in
  match a, b <: (u8 & u8) with
  | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 2
  | Rust_primitives.Integers.MkInt 0, Rust_primitives.Integers.MkInt 3
  | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 2
  | Rust_primitives.Integers.MkInt 1, Rust_primitives.Integers.MkInt 3 -> ()
  | _ -> ()
