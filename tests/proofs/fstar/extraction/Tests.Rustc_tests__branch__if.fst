module Tests.Rustc_tests__branch__if
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let say (message: string) : Prims.unit =
  let _:string = Core.Hint.black_box #string message in
  ()

let branch_not (a: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit = if a then say "a" in
  let _:Prims.unit =
    if ~.a
    then
      let _:Prims.unit = say "not a" in
      ()
  in
  let _:Prims.unit =
    if ~.(~.a <: bool)
    then
      let _:Prims.unit = say "not not a" in
      ()
  in
  if ~.(~.(~.a <: bool) <: bool)
  then
    let _:Prims.unit = say "not not not a" in
    ()

let branch_not_as (a: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit =
    if ~.a
    then
      let _:Prims.unit = say "not (a as bool)" in
      ()
  in
  let _:Prims.unit =
    if ~.(~.a <: bool)
    then
      let _:Prims.unit = say "not not (a as bool)" in
      ()
  in
  if ~.(~.(~.a <: bool) <: bool)
  then
    let _:Prims.unit = say "not not (a as bool)" in
    ()

let branch_and (a b: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  if a && b
  then
    let _:Prims.unit = say "both" in
    ()
  else
    let _:Prims.unit = say "not both" in
    ()

let branch_or (a b: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  if a || b
  then
    let _:Prims.unit = say "either" in
    ()
  else
    let _:Prims.unit = say "neither" in
    ()

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for a in (core::iter::traits::collect::f_into_iter([false, true, true])) {\n {\n let _: tuple0 = { tests::rustc_tests__branch__if::branch_not(a) };\n {\n let _: tuple0 = { tests::rustc_tests__branch__i..."

  in
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
    "{\n for a in (core::iter::traits::collect::f_into_iter([\n false, true, true, true, true,\n ])) {\n {\n for b in (core::iter::traits::collect::f_into_iter([\n false, true, true,\n ])) {\n {\n let _: tuple0 = {..."
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
