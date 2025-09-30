module Tests.Rustc_tests__branch__while
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let while_cond (_: Prims.unit) : (i32 & Prims.unit) =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let a:i32 = mk_i32 8 in
  Rust_primitives.Hax.while_loop (fun a ->
        let a:i32 = a in
        a >. mk_i32 0 <: bool)
    (fun a ->
        let a:i32 = a in
        true)
    (fun a ->
        let a:i32 = a in
        Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
    a
    (fun a ->
        let a:i32 = a in
        let a:i32 = a -! mk_i32 1 in
        a),
  ()
  <:
  (i32 & Prims.unit)

let while_cond_not (_: Prims.unit) : (i32 & Prims.unit) =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let a:i32 = mk_i32 8 in
  Rust_primitives.Hax.while_loop (fun a ->
        let a:i32 = a in
        ~.(a =. mk_i32 0 <: bool) <: bool)
    (fun a ->
        let a:i32 = a in
        true)
    (fun a ->
        let a:i32 = a in
        Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
    a
    (fun a ->
        let a:i32 = a in
        let a:i32 = a -! mk_i32 1 in
        a),
  ()
  <:
  (i32 & Prims.unit)

let while_op_and (_: Prims.unit) : ((i32 & i32) & Prims.unit) =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let a:i32 = mk_i32 8 in
  let b:i32 = mk_i32 4 in
  Rust_primitives.Hax.while_loop (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        (a >. mk_i32 0 <: bool) && (b >. mk_i32 0 <: bool))
    (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        true)
    (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
    (a, b <: (i32 & i32))
    (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        let a:i32 = a -! mk_i32 1 in
        let b:i32 = b -! mk_i32 1 in
        a, b <: (i32 & i32)),
  ()
  <:
  ((i32 & i32) & Prims.unit)

let while_op_or (_: Prims.unit) : ((i32 & i32) & Prims.unit) =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let a:i32 = mk_i32 4 in
  let b:i32 = mk_i32 8 in
  Rust_primitives.Hax.while_loop (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        (a >. mk_i32 0 <: bool) || (b >. mk_i32 0 <: bool))
    (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        true)
    (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
    (a, b <: (i32 & i32))
    (fun temp_0_ ->
        let a, b:(i32 & i32) = temp_0_ in
        let a:i32 = a -! mk_i32 1 in
        let b:i32 = b -! mk_i32 1 in
        a, b <: (i32 & i32)),
  ()
  <:
  ((i32 & i32) & Prims.unit)

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = while_cond () in
  let _:Prims.unit = while_cond_not () in
  let _:Prims.unit = while_op_and () in
  let _:Prims.unit = while_op_or () in
  ()
