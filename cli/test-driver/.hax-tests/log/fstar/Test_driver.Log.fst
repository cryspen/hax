module Test_driver.Log
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_types.Cli_options in
  let open Std.Sync.Lazy_lock in
  let open Tokio.Sync.Mpsc.Error in
  ()

type t_BackendJobKind =
  | BackendJobKind_CargoHaxSerialize : t_BackendJobKind
  | BackendJobKind_CargoHaxInto { f_test:Alloc.String.t_String }: t_BackendJobKind
  | BackendJobKind_Verification { f_test:Alloc.String.t_String }: t_BackendJobKind

type t_JobKind =
  | JobKind_ResolveTests : t_JobKind
  | JobKind_BackendJob {
    f_kind:t_BackendJobKind;
    f_backend:Hax_types.Cli_options.t_BackendName
  }: t_JobKind

let impl_2: Core.Clone.t_Clone t_JobKind =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Fmt.t_Debug t_JobKind

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Hash.t_Hash t_JobKind

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Marker.t_StructuralPartialEq t_JobKind

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Cmp.t_PartialEq t_JobKind t_JobKind

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Cmp.t_Eq t_JobKind

unfold
let impl_7 = impl_7'

let impl_8: Core.Clone.t_Clone t_BackendJobKind =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Fmt.t_Debug t_BackendJobKind

unfold
let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core.Hash.t_Hash t_BackendJobKind

unfold
let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core.Marker.t_StructuralPartialEq t_BackendJobKind

unfold
let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core.Cmp.t_PartialEq t_BackendJobKind t_BackendJobKind

unfold
let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core.Cmp.t_Eq t_BackendJobKind

unfold
let impl_13 = impl_13'

type t_ReportMessage =
  | ReportMessage_Start : t_ReportMessage
  | ReportMessage_Message : Alloc.String.t_String -> t_ReportMessage
  | ReportMessage_End :
      Alloc.Sync.t_Arc (Core.Result.t_Result Prims.unit Anyhow.t_Error) Alloc.Alloc.t_Global
    -> t_ReportMessage

let impl_14: Core.Clone.t_Clone t_ReportMessage =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core.Fmt.t_Debug t_ReportMessage

unfold
let impl_15 = impl_15'

type t_JobReport = {
  f_job:t_JobKind;
  f_message:t_ReportMessage
}

let impl_16: Core.Clone.t_Clone t_JobReport =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_17': Core.Fmt.t_Debug t_JobReport

unfold
let impl_17 = impl_17'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Fmt.t_Display t_JobKind =
  {
    f_fmt_pre = (fun (self: t_JobKind) (f: Core.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_JobKind)
        (f: Core.Fmt.t_Formatter)
        (out1: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_JobKind) (f: Core.Fmt.t_Formatter) ->
      let f, hax_temp_output:(Core.Fmt.t_Formatter &
        Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
        match self <: t_JobKind with
        | JobKind_ResolveTests  ->
          let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
            Core.Fmt.impl_11__write_fmt f
              (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                  (let list = ["discover tests"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core.Fmt.t_Arguments)
          in
          let f:Core.Fmt.t_Formatter = tmp0 in
          f, out <: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
        | JobKind_BackendJob { f_kind = kind ; f_backend = backend } ->
          match kind <: t_BackendJobKind with
          | BackendJobKind_CargoHaxSerialize  ->
            let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
              let list =
                [Core.Fmt.Rt.impl__new_display #Hax_types.Cli_options.t_BackendName backend]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list
            in
            let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
            =
              Core.Fmt.impl_11__write_fmt f
                (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                    (mk_usize 1)
                    (let list = ["cargo: "] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    args
                  <:
                  Core.Fmt.t_Arguments)
            in
            let f:Core.Fmt.t_Formatter = tmp0 in
            f, out <: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
          | BackendJobKind_CargoHaxInto { f_test = test } ->
            let args:(Hax_types.Cli_options.t_BackendName & Alloc.String.t_String) =
              backend, test <: (Hax_types.Cli_options.t_BackendName & Alloc.String.t_String)
            in
            let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 2) =
              let list =
                [
                  Core.Fmt.Rt.impl__new_display #Hax_types.Cli_options.t_BackendName args._1;
                  Core.Fmt.Rt.impl__new_display #Alloc.String.t_String args._2
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list
            in
            let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
            =
              Core.Fmt.impl_11__write_fmt f
                (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
                    (mk_usize 2)
                    (let list = ["engine: "; "/"] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                      Rust_primitives.Hax.array_of_list 2 list)
                    args
                  <:
                  Core.Fmt.t_Arguments)
            in
            let f:Core.Fmt.t_Formatter = tmp0 in
            f, out <: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
          | BackendJobKind_Verification { f_test = test } ->
            let args:(Hax_types.Cli_options.t_BackendName & Alloc.String.t_String) =
              backend, test <: (Hax_types.Cli_options.t_BackendName & Alloc.String.t_String)
            in
            let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 2) =
              let list =
                [
                  Core.Fmt.Rt.impl__new_display #Hax_types.Cli_options.t_BackendName args._1;
                  Core.Fmt.Rt.impl__new_display #Alloc.String.t_String args._2
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list
            in
            let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
            =
              Core.Fmt.impl_11__write_fmt f
                (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
                    (mk_usize 2)
                    (let list = ["verification: "; ": "] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                      Rust_primitives.Hax.array_of_list 2 list)
                    args
                  <:
                  Core.Fmt.t_Arguments)
            in
            let f:Core.Fmt.t_Formatter = tmp0 in
            f, out <: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
      in
      f, hax_temp_output
      <:
      (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
  }

let impl_JobKind__report_message
      (#iimpl_488124255_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Convert.t_AsRef iimpl_488124255_ string)
      (self: t_JobKind)
      (message: iimpl_488124255_)
    : (Prims.unit & Prims.unit) =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
    "{\n for line in (core::iter::traits::collect::f_into_iter(\n core::str::impl_str__lines(core::convert::f_as_ref(message)),\n )) {\n test_driver::log::impl_JobKind__report(\n self,\n test_driver::log::Report..."
  ,
  ()
  <:
  (Prims.unit & Prims.unit)

let impl_JobKind__run
      (#v_R #v_F #iimpl_637359003_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Future.Future.t_Future v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core.Ops.Function.t_Fn iimpl_637359003_ t_JobKind)
      (self: t_JobKind)
      (f: iimpl_637359003_)
    : Rust_primitives.Hax.failure =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
    ""

let v_REPORTS: Std.Sync.Lazy_lock.t_LazyLock
  (Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport)
  (Prims.unit -> Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport) =
  Std.Sync.Lazy_lock.impl__new #(Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        let tx, rx:(Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport &
          Tokio.Sync.Mpsc.Unbounded.t_UnboundedReceiver t_JobReport) =
          Tokio.Sync.Mpsc.Unbounded.unbounded_channel #t_JobReport ()
        in
        let _:Tokio.Runtime.Task.Join.t_JoinHandle Prims.unit =
          Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `AST import`.\n"
            ""
        in
        tx)

let impl_JobKind__report (self: t_JobKind) (message: t_ReportMessage) : Prims.unit =
  Core.Result.impl__unwrap #Prims.unit
    #(Tokio.Sync.Mpsc.Error.t_SendError t_JobReport)
    (Tokio.Sync.Mpsc.Unbounded.impl_4__send #t_JobReport
        (Core.Ops.Deref.f_deref #(Std.Sync.Lazy_lock.t_LazyLock
                (Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport)
                (Prims.unit -> Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport))
            #FStar.Tactics.Typeclasses.solve
            v_REPORTS
          <:
          Tokio.Sync.Mpsc.Unbounded.t_UnboundedSender t_JobReport)
        ({
            f_job = Core.Clone.f_clone #t_JobKind #FStar.Tactics.Typeclasses.solve self <: t_JobKind;
            f_message = message
          }
          <:
          t_JobReport)
      <:
      Core.Result.t_Result Prims.unit (Tokio.Sync.Mpsc.Error.t_SendError t_JobReport))
