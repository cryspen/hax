
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Test_driver.Commands.haxmeta
  (flags : (RustSlice String))
  : Result Rust_primitives.Hax.failure
  := do
  (← Rust_primitives.Hax.failure
      "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Got type `Coroutine`: coroutines are not supported by hax

This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `AST import`.
"
      "")

def Test_driver.Commands.haxmeta.Closure.PERMITS
  : Result Tokio.Sync.Semaphore.Semaphore
  := do
  (← Tokio.Sync.Semaphore.Impl.const_new (1 : usize))

def Test_driver.Commands.hax_engine
  (haxmeta : Std.Path.Path)
  (test_module_name : String)
  (output_dir : Std.Path.Path)
  (backend : Hax_types.Cli_options.BackendName)
  (into_flags : (RustSlice Alloc.String.String))
  (backend_flags : (RustSlice Alloc.String.String))
  : Result Rust_primitives.Hax.failure
  := do
  (← Rust_primitives.Hax.failure
      "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Got type `Coroutine`: coroutines are not supported by hax

This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `AST import`.
"
      "")

inductive Test_driver.Commands.OutMsg : Type
| Cargo : Cargo_metadata.Messages.CompilerMessage -> Test_driver.Commands.OutMsg

| Hax : Hax_types.Diagnostics.Message.HaxMessage -> Test_driver.Commands.OutMsg 
| Unknown : Alloc.String.String -> Test_driver.Commands.OutMsg 


structure Test_driver.Commands.HaxEngineOutput where
  error_code : i32
  messages : (Alloc.Vec.Vec Test_driver.Commands.OutMsg Alloc.Alloc.Global)
  stderr : Alloc.String.String

instance Test_driver.Commands._.Impl :
  Serde.Ser.Serialize Test_driver.Commands.OutMsg
  where


instance Test_driver.Commands.__1.Impl :
  Serde.De.Deserialize Test_driver.Commands.OutMsg
  where


instance Test_driver.Commands.Impl_1 :
  Core.Fmt.Debug Test_driver.Commands.OutMsg
  where


def Test_driver.Commands.Impl.render
  (self : Test_driver.Commands.OutMsg)
  : Result (Core.Option.Option Alloc.String.String)
  := do
  (match self with
    | (Test_driver.Commands.OutMsg.Cargo compiler_message)
      => do
        (Core.Option.Option.Some
          (← Core.Option.Impl.unwrap Alloc.String.String
              (← Core.Clone.Clone.clone
                  (Cargo_metadata.Diagnostic.Diagnostic.rendered
                      (Cargo_metadata.Messages.CompilerMessage.message
                          compiler_message)))))
    | (Test_driver.Commands.OutMsg.Hax hax_message)
      => do
        (← (← Rust_primitives.Hax.failure
              "The mutation of this &mut is not allowed here.

This is discussed in issue https://github.com/hacspec/hax/issues/420.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `DirectAndMut`.
"
              "hax_types::diagnostics::message::impl_HaxMessage__render")
            (← Core.Clone.Clone.clone hax_message)
            Hax_types.Cli_options.MessageFormat.Human
            (← Rust_primitives.Hax.failure
                "The mutation of this &mut is not allowed here.

This is discussed in issue https://github.com/hacspec/hax/issues/420.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `DirectAndMut`.
"
                "core::option::Option_None()"))
    | (Test_driver.Commands.OutMsg.Unknown unknown)
      => do (Core.Option.Option.Some (← Core.Clone.Clone.clone unknown)))