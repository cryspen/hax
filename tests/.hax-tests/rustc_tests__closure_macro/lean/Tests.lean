
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

def Tests.Rustc_tests__closure_macro.load_configuration_files
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Alloc.String.String Alloc.String.String)
  := do
  (Core.Result.Result.Ok (← Core.Convert.From.from "config"))

def Tests.Rustc_tests__closure_macro.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 Alloc.String.String)
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["Starting service
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  (match
    (← Core.Result.Impl.or_else
        Alloc.String.String
        Alloc.String.String
        Alloc.String.String
        Alloc.String.String
        -> Result (Core.Result.Result Alloc.String.String Alloc.String.String)
        (← Tests.Rustc_tests__closure_macro.load_configuration_files
            Rust_primitives.Hax.Tuple0.mk)
        (fun e => (do
            let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
              #v[(← Core.Fmt.Rt.Impl.new_display Alloc.String.String e)]);
            let message : Alloc.String.String ← (pure
              (← Core.Hint.must_use Alloc.String.String
                  (← Alloc.Fmt.format
                      (← Core.Fmt.Rt.Impl_1.new_v1 (1 : usize) (1 : usize)
                          #v["Error loading configs: "]
                          args))));
            (← if
            (← Rust_primitives.Hax.Machine_int.gt
                (← Alloc.String.Impl.len message)
                (0 : usize)) then do
              let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
                #v[(← Core.Fmt.Rt.Impl.new_display Alloc.String.String
                         message)]);
              let _ ← (pure
                (← Std.Io.Stdio._print
                    (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
                        #v["", "
"]
                        args)));
              let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
              (Core.Result.Result.Ok (← Core.Convert.From.from "ok"))
            else do
              let _ ← (pure
                (← if
                (← Rust_primitives.Hax.Machine_int.gt
                    (← Core.Str.Impl.len "error")
                    (0 : usize)) then do
                  let _ ← (pure
                    (← Std.Io.Stdio._print
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["no msg
"])));
                  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                  Rust_primitives.Hax.Tuple0.mk
                else do
                  let _ ← (pure
                    (← Std.Io.Stdio._print
                        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                            #v["error
"])));
                  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                  Rust_primitives.Hax.Tuple0.mk));
              (Core.Result.Result.Err (← Core.Convert.From.from "error"))) :
            Result
            (Core.Result.Result Alloc.String.String Alloc.String.String))))
  with
    | (Core.Result.Result.Ok config)
      => do
        let startup_delay_duration : Alloc.String.String ← (pure
          (← Core.Convert.From.from "arg"));
        let _ ← (pure
          (Rust_primitives.Hax.Tuple2.mk config startup_delay_duration));
        (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))