module Tests.Rustc_tests__branch__mod.Lazy_boolean
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let branch_and (a b: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let c:bool = a && b in
  let _:bool = Core.Hint.black_box #bool c in
  ()

let branch_or (a b: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let c:bool = a || b in
  let _:bool = Core.Hint.black_box #bool c in
  ()

let chain (x: u32) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let c:bool = x >. mk_u32 1 && x >. mk_u32 2 && x >. mk_u32 4 && x >. mk_u32 8 in
  let _:bool = Core.Hint.black_box #bool c in
  let d:bool = x <. mk_u32 1 || x <. mk_u32 2 || x <. mk_u32 4 || x <. mk_u32 8 in
  let _:bool = Core.Hint.black_box #bool d in
  ()

let nested_mixed (x: u32) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let c:bool = (x <. mk_u32 4 || x >=. mk_u32 9) && (x <. mk_u32 2 || x >=. mk_u32 10) in
  let _:bool = Core.Hint.black_box #bool c in
  let d:bool = x <. mk_u32 4 && x <. mk_u32 1 || x >=. mk_u32 8 && x >=. mk_u32 10 in
  let _:bool = Core.Hint.black_box #bool d in
  ()

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for a in (core::iter::traits::collect::f_into_iter([\n false, true, true, true, true,\n ])) {\n {\n for b in (core::iter::traits::collect::f_into_iter([\n false, true, true,\n ])) {\n {\n let _: tuple0 = {..."

  in
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
    "{\n for x in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 16,\n })) {\n {\n let _: tuple0 = {\n tests::rustc_tests__branch__mod::lazy_boolean::chain(x)\n };\n {\n l..."
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
