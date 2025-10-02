module Test_driver.Commands
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_types.Diagnostics.Message in
  ()

let haxmeta (flags: t_Slice string) : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

let haxmeta__anon_const_0__v_PERMITS: Tokio.Sync.Semaphore.t_Semaphore =
  Tokio.Sync.Semaphore.impl_Semaphore__const_new (mk_usize 1)

let hax_engine
      (haxmeta: Std.Path.t_Path)
      (test_module_name: string)
      (output_dir: Std.Path.t_Path)
      (backend: Hax_types.Cli_options.t_BackendName)
      (into_flags backend_flags: t_Slice Alloc.String.t_String)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

type t_OutMsg =
  | OutMsg_Cargo : Cargo_metadata.Messages.t_CompilerMessage -> t_OutMsg
  | OutMsg_Hax : Hax_types.Diagnostics.Message.t_HaxMessage -> t_OutMsg
  | OutMsg_Unknown : Alloc.String.t_String -> t_OutMsg

type t_HaxEngineOutput = {
  f_error_code:i32;
  f_messages:Alloc.Vec.t_Vec t_OutMsg Alloc.Alloc.t_Global;
  f_stderr:Alloc.String.t_String
}

let e_: Prims.unit = ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val e___impl': Serde.Ser.t_Serialize t_OutMsg

unfold
let e___impl = e___impl'

let e_ee_1: Prims.unit = ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val e_ee_1__impl': Serde.De.t_Deserialize t_OutMsg

unfold
let e_ee_1__impl = e_ee_1__impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Fmt.t_Debug t_OutMsg

unfold
let impl_1 = impl_1'

let impl_OutMsg__render (self: t_OutMsg) : Core.Option.t_Option Alloc.String.t_String =
  match self <: t_OutMsg with
  | OutMsg_Cargo compiler_message ->
    Core.Option.Option_Some
    (Core.Option.impl__unwrap #Alloc.String.t_String
        (Core.Clone.f_clone #(Core.Option.t_Option Alloc.String.t_String)
            #FStar.Tactics.Typeclasses.solve
            compiler_message.Cargo_metadata.Messages.f_message.Cargo_metadata.Diagnostic.f_rendered
          <:
          Core.Option.t_Option Alloc.String.t_String))
    <:
    Core.Option.t_Option Alloc.String.t_String
  | OutMsg_Hax hax_message ->
    Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
      "hax_types::diagnostics::message::impl_HaxMessage__render"
      (Core.Clone.f_clone #Hax_types.Diagnostics.Message.t_HaxMessage
          #FStar.Tactics.Typeclasses.solve
          hax_message)
      (Hax_types.Cli_options.MessageFormat_Human <: Hax_types.Cli_options.t_MessageFormat)
      (Rust_primitives.Hax.failure "The mutation of this &mut is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `DirectAndMut`.\n"
          "core::option::Option_None()")
  | OutMsg_Unknown unknown ->
    Core.Option.Option_Some
    (Core.Clone.f_clone #Alloc.String.t_String #FStar.Tactics.Typeclasses.solve unknown)
    <:
    Core.Option.t_Option Alloc.String.t_String
