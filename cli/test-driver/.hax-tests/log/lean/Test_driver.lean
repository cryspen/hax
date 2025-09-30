
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

inductive Test_driver.Log.BackendJobKind : Type
| CargoHaxSerialize : Test_driver.Log.BackendJobKind 
| CargoHaxInto (test : Alloc.String.String) : Test_driver.Log.BackendJobKind 
| Verification (test : Alloc.String.String) : Test_driver.Log.BackendJobKind 


inductive Test_driver.Log.JobKind : Type
| ResolveTests : Test_driver.Log.JobKind 
| BackendJob (kind : Test_driver.Log.BackendJobKind)
             (backend : Hax_types.Cli_options.BackendName)
    : Test_driver.Log.JobKind 


instance Test_driver.Log.Impl_2 : Core.Clone.Clone Test_driver.Log.JobKind where


instance Test_driver.Log.Impl_3 : Core.Fmt.Debug Test_driver.Log.JobKind where


instance Test_driver.Log.Impl_4 : Core.Hash.Hash Test_driver.Log.JobKind where


instance Test_driver.Log.Impl_5 :
  Core.Marker.StructuralPartialEq Test_driver.Log.JobKind
  where


instance Test_driver.Log.Impl_6 :
  Core.Cmp.PartialEq Test_driver.Log.JobKind Test_driver.Log.JobKind
  where


instance Test_driver.Log.Impl_7 : Core.Cmp.Eq Test_driver.Log.JobKind where


instance Test_driver.Log.Impl_8 :
  Core.Clone.Clone Test_driver.Log.BackendJobKind
  where


instance Test_driver.Log.Impl_9 :
  Core.Fmt.Debug Test_driver.Log.BackendJobKind
  where


instance Test_driver.Log.Impl_10 :
  Core.Hash.Hash Test_driver.Log.BackendJobKind
  where


instance Test_driver.Log.Impl_11 :
  Core.Marker.StructuralPartialEq Test_driver.Log.BackendJobKind
  where


instance Test_driver.Log.Impl_12 :
  Core.Cmp.PartialEq
  Test_driver.Log.BackendJobKind
  Test_driver.Log.BackendJobKind
  where


instance Test_driver.Log.Impl_13 :
  Core.Cmp.Eq Test_driver.Log.BackendJobKind
  where


inductive Test_driver.Log.ReportMessage : Type
| Start : Test_driver.Log.ReportMessage 
| Message : Alloc.String.String -> Test_driver.Log.ReportMessage 
| End : (Alloc.Sync.Arc
      (Core.Result.Result Rust_primitives.Hax.Tuple0 Anyhow.Error)
      Alloc.Alloc.Global) -> Test_driver.Log.ReportMessage 


instance Test_driver.Log.Impl_14 :
  Core.Clone.Clone Test_driver.Log.ReportMessage
  where


instance Test_driver.Log.Impl_15 :
  Core.Fmt.Debug Test_driver.Log.ReportMessage
  where


structure Test_driver.Log.JobReport where
  job : Test_driver.Log.JobKind
  message : Test_driver.Log.ReportMessage

instance Test_driver.Log.Impl_16 :
  Core.Clone.Clone Test_driver.Log.JobReport
  where


instance Test_driver.Log.Impl_17 :
  Core.Fmt.Debug Test_driver.Log.JobReport
  where


instance Test_driver.Log.Impl : Core.Fmt.Display Test_driver.Log.JobKind where
  fmt (self : Test_driver.Log.JobKind) (f : Core.Fmt.Formatter) := do
    let ⟨f, hax_temp_output⟩ ← (pure
      (match self with
        | (Test_driver.Log.JobKind.ResolveTests )
          => do
            let ⟨tmp0, out⟩ ← (pure
              (← Core.Fmt.Impl_11.write_fmt
                  f
                  (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                      #v["discover tests"])));
            let f : Core.Fmt.Formatter ← (pure tmp0);
            (Rust_primitives.Hax.Tuple2.mk f out)
        | (Test_driver.Log.JobKind.BackendJob
            (kind := kind) (backend := backend))
          => do
            (match kind with
              | (Test_driver.Log.BackendJobKind.CargoHaxSerialize )
                => do
                  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ←
                    (pure
                    #v[(← Core.Fmt.Rt.Impl.new_display
                             Hax_types.Cli_options.BackendName backend)]);
                  let ⟨tmp0, out⟩ ← (pure
                    (← Core.Fmt.Impl_11.write_fmt
                        f
                        (← Core.Fmt.Rt.Impl_1.new_v1 (1 : usize) (1 : usize)
                            #v["cargo: "]
                            args)));
                  let f : Core.Fmt.Formatter ← (pure tmp0);
                  (Rust_primitives.Hax.Tuple2.mk f out)
              | (Test_driver.Log.BackendJobKind.CargoHaxInto (test := test))
                => do
                  let
                    args : (Rust_primitives.Hax.Tuple2
                      Hax_types.Cli_options.BackendName
                      Alloc.String.String) ← (pure
                    (Rust_primitives.Hax.Tuple2.mk backend test));
                  let args : (RustArray Core.Fmt.Rt.Argument (2 : usize)) ←
                    (pure
                    #v[(← Core.Fmt.Rt.Impl.new_display
                             Hax_types.Cli_options.BackendName
                             (Rust_primitives.Hax.Tuple0._0 args)),
                         (← Core.Fmt.Rt.Impl.new_display Alloc.String.String
                             (Rust_primitives.Hax.Tuple0._1 args))]);
                  let ⟨tmp0, out⟩ ← (pure
                    (← Core.Fmt.Impl_11.write_fmt
                        f
                        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (2 : usize)
                            #v["engine: ", "/"]
                            args)));
                  let f : Core.Fmt.Formatter ← (pure tmp0);
                  (Rust_primitives.Hax.Tuple2.mk f out)
              | (Test_driver.Log.BackendJobKind.Verification (test := test))
                => do
                  let
                    args : (Rust_primitives.Hax.Tuple2
                      Hax_types.Cli_options.BackendName
                      Alloc.String.String) ← (pure
                    (Rust_primitives.Hax.Tuple2.mk backend test));
                  let args : (RustArray Core.Fmt.Rt.Argument (2 : usize)) ←
                    (pure
                    #v[(← Core.Fmt.Rt.Impl.new_display
                             Hax_types.Cli_options.BackendName
                             (Rust_primitives.Hax.Tuple0._0 args)),
                         (← Core.Fmt.Rt.Impl.new_display Alloc.String.String
                             (Rust_primitives.Hax.Tuple0._1 args))]);
                  let ⟨tmp0, out⟩ ← (pure
                    (← Core.Fmt.Impl_11.write_fmt
                        f
                        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (2 : usize)
                            #v["verification: ", ": "]
                            args)));
                  let f : Core.Fmt.Formatter ← (pure tmp0);
                  (Rust_primitives.Hax.Tuple2.mk f out))));
    (Rust_primitives.Hax.Tuple2.mk f hax_temp_output)

def Test_driver.Log.Impl_1.report_message
  (impl_AsRef_str_ : Type) [(Core.Convert.AsRef impl_AsRef_str_ String)] (self :
  Test_driver.Log.JobKind)
  (message : impl_AsRef_str_)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.failure
        "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
        "{
 for line in (core::iter::traits::collect::f_into_iter(
 core::str::impl_str__lines(core::convert::f_as_ref(message)),
 )) {
 test_driver::log::impl_JobKind__report(
 self,
 test_driver::log::Report...")
    Rust_primitives.Hax.Tuple0.mk)

def Test_driver.Log.Impl_1.run
  (R : Type)
  (F : Type)
  (impl_Fn(JobKind)_-__F : Type)
  [(Core.Future.Future.Future F)]
  [-- unsupported constraint]
  [(Core.Ops.Function.Fn
    impl_Fn(JobKind)_-__F
    (Rust_primitives.Hax.Tuple1 Test_driver.Log.JobKind))]
  [-- unsupported constraint]
  (self : Test_driver.Log.JobKind)
  (f : impl_Fn(JobKind)_-__F)
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

def Test_driver.Log.REPORTS
  : Result
  (Std.Sync.Lazy_lock.LazyLock
    (Tokio.Sync.Mpsc.Unbounded.UnboundedSender Test_driver.Log.JobReport)
    Rust_primitives.Hax.Tuple0
    -> Result (Tokio.Sync.Mpsc.Unbounded.UnboundedSender
      Test_driver.Log.JobReport))
  := do
  (← Std.Sync.Lazy_lock.Impl.new
      (Tokio.Sync.Mpsc.Unbounded.UnboundedSender Test_driver.Log.JobReport)
      Rust_primitives.Hax.Tuple0
      -> Result (Tokio.Sync.Mpsc.Unbounded.UnboundedSender
        Test_driver.Log.JobReport)
      (fun _ => (do
          let ⟨tx, rx⟩ ← (pure
            (← Tokio.Sync.Mpsc.Unbounded.unbounded_channel
                Test_driver.Log.JobReport Rust_primitives.Hax.Tuple0.mk));
          let _ ← (pure
            (← Rust_primitives.Hax.failure
                "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Got type `Coroutine`: coroutines are not supported by hax

This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `AST import`.
"
                ""));
          tx : Result
          (Tokio.Sync.Mpsc.Unbounded.UnboundedSender
            Test_driver.Log.JobReport))))

def Test_driver.Log.Impl_1.report
  (self : Test_driver.Log.JobKind)
  (message : Test_driver.Log.ReportMessage)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Core.Result.Impl.unwrap
      Rust_primitives.Hax.Tuple0
      (Tokio.Sync.Mpsc.Error.SendError Test_driver.Log.JobReport)
      (← Tokio.Sync.Mpsc.Unbounded.Impl_4.send Test_driver.Log.JobReport
          (← Core.Ops.Deref.Deref.deref Test_driver.Log.REPORTS)
          (Test_driver.Log.JobReport.mk
            (job := (← Core.Clone.Clone.clone self)) (message := message))))