module New_tests.Legacy__lean_tests__lib.Matching
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): ssprove(HAX0001)
let test_const_matching (x: u32) (c: FStar.Char.char) (s: string) (b: bool) : u32 =
  let x:u32 =
    match x <: u32 with
    | Rust_primitives.Integers.MkInt 0 -> mk_u32 42
    | _ -> mk_u32 0
  in
  let c:u32 =
    match c <: FStar.Char.char with
    | 'a' -> mk_u32 42
    | _ -> mk_u32 0
  in
  let s:u32 =
    match s <: string with
    | "Hello" -> mk_u32 42
    | _ -> mk_u32 0
  in
  let b:u32 =
    match b <: bool with
    | true -> mk_u32 42
    | false -> mk_u32 0
  in
  ((x +! c <: u32) +! s <: u32) +! b

/// @fail(extraction): proverif(HAX0008), fstar(HAX0008), ssprove(HAX0008), coq(HAX0008)
let test_binding_subpattern_matching (x: (u8 & (u8 & u8))) : u8 =
  Rust_primitives.Hax.failure "Explicit rejection by a phase in the Hax engine:\na node of kind [As_pattern] have been found in the AST\n\nNote: the error was labeled with context `reject_AsPattern`.\n"
    "(match (x) {\n Tuple2(0, pair @ Tuple2(a, b)) => {\n rust_primitives::hax::machine_int::add(\n rust_primitives::hax::machine_int::add(\n rust_primitives::hax::machine_int::add(a, b),\n proj_proj_tuple0(pai..."
