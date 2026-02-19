module New_tests.Rustc_coverage__branch__if_let
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let say (message: string) : Prims.unit =
  let _:string = Core_models.Hint.black_box #string message in
  ()

/// @fail(extraction): proverif(HAX0008)
let if_let (input: Core_models.Option.t_Option string) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 1)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          ())
  in
  let _:Prims.unit =
    match input <: Core_models.Option.t_Option string with
    | Core_models.Option.Option_Some x ->
      let _:Prims.unit = say x in
      ()
    | _ ->
      let _:Prims.unit = say "none" in
      ()
  in
  let _:Prims.unit = say "done" in
  ()

/// @fail(extraction): coq(HAX0002, HAX0002), ssprove(HAX0002, HAX0002), proverif(HAX0002, HAX0002), lean(HAX0002, HAX0002), fstar(HAX0002, HAX0002)
let if_let_chain (a b: Core_models.Option.t_Option string) : Prims.unit =
  let _:Prims.unit =
    if
      Rust_primitives.Hax.failure "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: `Let` nodes are supposed to be pre-processed\n\nNote: the error was labeled with context `AST import`.\n"
        "" &&
      Rust_primitives.Hax.failure "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: `Let` nodes are supposed to be pre-processed\n\nNote: the error was labeled with context `AST import`.\n"
        ""
    then
      let _:Prims.unit = say x in
      let _:Prims.unit = say y in
      ()
    else
      let _:Prims.unit = say "not both" in
      ()
  in
  let _:Prims.unit = say "done" in
  ()

/// @fail(extraction): proverif(HAX0008, HAX0008, HAX0008)
let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    if_let (Core_models.Option.Option_Some "x" <: Core_models.Option.t_Option string)
  in
  let _:Prims.unit =
    if_let (Core_models.Option.Option_Some "x" <: Core_models.Option.t_Option string)
  in
  let _:Prims.unit =
    if_let (Core_models.Option.Option_None <: Core_models.Option.t_Option string)
  in
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 8)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          if_let_chain (Core_models.Option.Option_Some "a" <: Core_models.Option.t_Option string)
            (Core_models.Option.Option_Some "b" <: Core_models.Option.t_Option string)
          <:
          Prims.unit)
  in
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 4)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          if_let_chain (Core_models.Option.Option_Some "a" <: Core_models.Option.t_Option string)
            (Core_models.Option.Option_None <: Core_models.Option.t_Option string)
          <:
          Prims.unit)
  in
  let _:Prims.unit =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 2)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      ()
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:i32 = temp_1_ in
          if_let_chain (Core_models.Option.Option_None <: Core_models.Option.t_Option string)
            (Core_models.Option.Option_Some "b" <: Core_models.Option.t_Option string)
          <:
          Prims.unit)
  in
  let _:Prims.unit =
    if_let_chain (Core_models.Option.Option_None <: Core_models.Option.t_Option string)
      (Core_models.Option.Option_None <: Core_models.Option.t_Option string)
  in
  ()
