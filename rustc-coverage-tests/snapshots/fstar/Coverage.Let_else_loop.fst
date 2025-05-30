module Coverage.Let_else_loop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let loopy (cond: bool) : Prims.unit =
  match cond <: bool with
  | true -> ()
  | _ ->
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
      "{\n loop {\n Tuple0\n }\n }",
    ()
    <:
    (Prims.unit & Prims.unit)

let e_loop_either_way (cond: bool) : Prims.unit =
  match cond <: bool with
  | true ->
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
            "{\n loop {\n Tuple0\n }\n }"
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))
  | _ ->
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
      "{\n loop {\n Tuple0\n }\n }",
    ()
    <:
    (Prims.unit & Prims.unit)

let e_if (cond: bool) : Prims.unit =
  if cond
  then
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
            "{\n loop {\n Tuple0\n }\n }"
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))
  else
    Rust_primitives.Hax.never_to_any ((Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
            "{\n loop {\n Tuple0\n }\n }"
          <:
          Prims.unit),
        ()
        <:
        (Prims.unit & Prims.unit))

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = loopy true in
  ()
