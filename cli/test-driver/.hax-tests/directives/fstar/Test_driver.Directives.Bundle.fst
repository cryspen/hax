module Test_driver.Directives.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Anyhow in
  let open Anyhow.Context in
  let open Anyhow.Error in
  let open Clap_builder.Derive in
  let open Clap_builder.Error in
  let open Clap_builder.Error.Format in
  let open Hax_types.Cli_options in
  let open Hax_types.Cli_options.Extension in
  let open Pest in
  let open Pest.Error in
  let open Pest.Iterators.Pairs in
  let open Pest.Parser in
  let open Pest.Parser_state in
  let open Std.Collections.Hash.Map in
  let open Std.Collections.Hash.Set in
  let open Std.Ffi.Os_str in
  let open Std.Hash.Random in
  ()

let parse_cli (raw_cli: string)
    : Core.Result.t_Result
      (Hax_types.Cli_options.t_BackendName &
        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error =
  match
    Anyhow.f_with_context #(Core.Option.t_Option
        (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
      #(Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
      #Core.Convert.t_Infallible
      #FStar.Tactics.Typeclasses.solve
      #Alloc.String.t_String
      (Shlex.split raw_cli
        <:
        Core.Option.t_Option (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
      (fun temp_0_ ->
          let _:Prims.unit = temp_0_ in
          let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
            let list = [Core.Fmt.Rt.impl__new_display #string raw_cli] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list
          in
          Core.Hint.must_use #Alloc.String.t_String
            (Alloc.Fmt.format (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
                    (mk_usize 1)
                    (let list =
                        [
                          "Could not parse `";
                          "` as a valid shell command. This is probably due to unclosed quote."
                        ]
                      in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                      Rust_primitives.Hax.array_of_list 2 list)
                    args
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Alloc.String.t_String))
    <:
    Core.Result.t_Result (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
  with
  | Core.Result.Result_Ok cli ->
    (match
        Clap_builder.Derive.f_try_parse_from #(Hax_types.Cli_options.t_ExtensibleOptions Prims.unit)
          #FStar.Tactics.Typeclasses.solve
          #(Core.Iter.Adapters.Chain.t_Chain (Core.Array.Iter.t_IntoIter string (mk_usize 1))
              (Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Alloc.String.t_String)
                  (Alloc.String.t_String -> string)))
          #string
          (Core.Iter.Traits.Iterator.f_chain #(Core.Array.Iter.t_IntoIter string (mk_usize 1))
              #FStar.Tactics.Typeclasses.solve
              #(Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Alloc.String.t_String)
                  (Alloc.String.t_String -> string))
              (Core.Iter.Traits.Collect.f_into_iter #(t_Array string (mk_usize 1))
                  #FStar.Tactics.Typeclasses.solve
                  (let list = ["hax"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core.Array.Iter.t_IntoIter string (mk_usize 1))
              (Core.Iter.Traits.Iterator.f_map #(Core.Slice.Iter.t_Iter Alloc.String.t_String)
                  #FStar.Tactics.Typeclasses.solve
                  #string
                  (Core.Slice.impl__iter #Alloc.String.t_String
                      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec Alloc.String.t_String
                              Alloc.Alloc.t_Global)
                          #FStar.Tactics.Typeclasses.solve
                          cli
                        <:
                        t_Slice Alloc.String.t_String)
                    <:
                    Core.Slice.Iter.t_Iter Alloc.String.t_String)
                  (fun s ->
                      let s:Alloc.String.t_String = s in
                      Alloc.String.impl_String__as_str s <: string)
                <:
                Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Alloc.String.t_String)
                  (Alloc.String.t_String -> string))
            <:
            Core.Iter.Adapters.Chain.t_Chain (Core.Array.Iter.t_IntoIter string (mk_usize 1))
              (Core.Iter.Adapters.Map.t_Map (Core.Slice.Iter.t_Iter Alloc.String.t_String)
                  (Alloc.String.t_String -> string)))
        <:
        Core.Result.t_Result (Hax_types.Cli_options.t_ExtensibleOptions Prims.unit)
          (Clap_builder.Error.t_Error Clap_builder.Error.Format.t_RichFormatter)
      with
      | Core.Result.Result_Ok options ->
        (match
            options.Hax_types.Cli_options.f_command <: Hax_types.Cli_options.t_Command Prims.unit
          with
          | Hax_types.Cli_options.Command_Backend backend_options ->
            if
              Core.Option.impl__is_some #Alloc.String.t_String
                backend_options.Hax_types.Cli_options.f_prune_haxmeta
            then
              let error:Anyhow.t_Error =
                Anyhow.__private.format_err (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                      (let list = ["Specifying manually a `--prune_haxmeta` is forbiden"] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    Core.Fmt.t_Arguments)
              in
              Core.Result.Result_Err error
              <:
              Core.Result.t_Result
                (Hax_types.Cli_options.t_BackendName &
                  Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                  Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
            else
              if
                Core.Option.impl__is_some #Hax_types.Cli_options.t_DebugEngineMode
                  backend_options.Hax_types.Cli_options.f_debug_engine
              then
                let error:Anyhow.t_Error =
                  Anyhow.__private.format_err (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["Specifying manually a `--debug_engine` is forbiden"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                Core.Result.Result_Err error
                <:
                Core.Result.t_Result
                  (Hax_types.Cli_options.t_BackendName &
                    Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                    Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
              else
                if backend_options.Hax_types.Cli_options.f_profile
                then
                  let error:Anyhow.t_Error =
                    Anyhow.__private.format_err (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                          (let list = ["Specifying manually a `--profile` is forbiden"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        Core.Fmt.t_Arguments)
                  in
                  Core.Result.Result_Err error
                  <:
                  Core.Result.t_Result
                    (Hax_types.Cli_options.t_BackendName &
                      Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
                else
                  if backend_options.Hax_types.Cli_options.f_stats
                  then
                    let error:Anyhow.t_Error =
                      Anyhow.__private.format_err (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                            (let list = ["Specifying manually a `--stats` is forbiden"] in
                              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                              Rust_primitives.Hax.array_of_list 1 list)
                          <:
                          Core.Fmt.t_Arguments)
                    in
                    Core.Result.Result_Err error
                    <:
                    Core.Result.t_Result
                      (Hax_types.Cli_options.t_BackendName &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
                  else
                    let backend_options_with_profile:Hax_types.Cli_options.t_BackendOptions
                    Prims.unit =
                      {
                        Core.Clone.f_clone #(Hax_types.Cli_options.t_BackendOptions Prims.unit)
                          #FStar.Tactics.Typeclasses.solve
                          backend_options with
                        Hax_types.Cli_options.f_profile = true
                      }
                      <:
                      Hax_types.Cli_options.t_BackendOptions Prims.unit
                    in
                    let backend:Hax_types.Cli_options.t_BackendName =
                      Core.Convert.f_from #Hax_types.Cli_options.t_BackendName
                        #(Hax_types.Cli_options.t_Backend Prims.unit)
                        #FStar.Tactics.Typeclasses.solve
                        backend_options.Hax_types.Cli_options.f_backend
                    in
                    let _, out:(Core.Ops.Range.t_Range usize &
                      Core.Option.t_Option
                      (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)) =
                      Core.Iter.Traits.Iterator.f_find_map #(Core.Ops.Range.t_Range usize)
                        #FStar.Tactics.Typeclasses.solve
                        #(Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
                        ({
                            Core.Ops.Range.f_start = mk_usize 0;
                            Core.Ops.Range.f_end
                            =
                            Alloc.Vec.impl_1__len #Alloc.String.t_String #Alloc.Alloc.t_Global cli
                            <:
                            usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize)
                        (fun i ->
                            let i:usize = i in
                            let lhs, rhs:(t_Slice Alloc.String.t_String &
                              t_Slice Alloc.String.t_String) =
                              cli.[ { Core.Ops.Range.f_end = i } <: Core.Ops.Range.t_RangeTo usize ],
                              cli.[ { Core.Ops.Range.f_start = i +! mk_usize 1 <: usize }
                                <:
                                Core.Ops.Range.t_RangeFrom usize ]
                              <:
                              (t_Slice Alloc.String.t_String & t_Slice Alloc.String.t_String)
                            in
                            let cli:Core.Iter.Adapters.Chain.t_Chain
                              (Core.Iter.Sources.Once.t_Once Alloc.String.t_String)
                              (Core.Iter.Adapters.Chain.t_Chain
                                  (Core.Iter.Adapters.Cloned.t_Cloned
                                    (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                  (Core.Iter.Adapters.Chain.t_Chain
                                      (Core.Array.Iter.t_IntoIter Alloc.String.t_String (mk_usize 2)
                                      )
                                      (Core.Iter.Adapters.Cloned.t_Cloned
                                        (Core.Slice.Iter.t_Iter Alloc.String.t_String)))) =
                              Core.Iter.Traits.Iterator.f_chain #(Core.Iter.Sources.Once.t_Once
                                  Alloc.String.t_String)
                                #FStar.Tactics.Typeclasses.solve
                                #(Core.Iter.Adapters.Chain.t_Chain
                                    (Core.Iter.Adapters.Cloned.t_Cloned
                                      (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                    (Core.Iter.Adapters.Chain.t_Chain
                                        (Core.Array.Iter.t_IntoIter Alloc.String.t_String
                                            (mk_usize 2))
                                        (Core.Iter.Adapters.Cloned.t_Cloned
                                          (Core.Slice.Iter.t_Iter Alloc.String.t_String))))
                                (Core.Iter.Sources.Once.once #Alloc.String.t_String
                                    (Alloc.String.f_to_string #string
                                        #FStar.Tactics.Typeclasses.solve
                                        "hax"
                                      <:
                                      Alloc.String.t_String)
                                  <:
                                  Core.Iter.Sources.Once.t_Once Alloc.String.t_String)
                                (Core.Iter.Traits.Iterator.f_chain #(Core.Iter.Adapters.Cloned.t_Cloned
                                      (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                    #FStar.Tactics.Typeclasses.solve
                                    #(Core.Iter.Adapters.Chain.t_Chain
                                        (Core.Array.Iter.t_IntoIter Alloc.String.t_String
                                            (mk_usize 2))
                                        (Core.Iter.Adapters.Cloned.t_Cloned
                                          (Core.Slice.Iter.t_Iter Alloc.String.t_String)))
                                    (Core.Iter.Traits.Iterator.f_cloned #(Core.Slice.Iter.t_Iter
                                          Alloc.String.t_String)
                                        #FStar.Tactics.Typeclasses.solve
                                        #Alloc.String.t_String
                                        (Core.Slice.impl__iter #Alloc.String.t_String lhs
                                          <:
                                          Core.Slice.Iter.t_Iter Alloc.String.t_String)
                                      <:
                                      Core.Iter.Adapters.Cloned.t_Cloned
                                      (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                    (Core.Iter.Traits.Iterator.f_chain #(Core.Array.Iter.t_IntoIter
                                            Alloc.String.t_String (mk_usize 2))
                                        #FStar.Tactics.Typeclasses.solve
                                        #(Core.Iter.Adapters.Cloned.t_Cloned
                                          (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                        (Core.Iter.Traits.Collect.f_into_iter #(t_Array
                                                Alloc.String.t_String (mk_usize 2))
                                            #FStar.Tactics.Typeclasses.solve
                                            (let list =
                                                [
                                                  Core.Convert.f_into #string
                                                    #Alloc.String.t_String
                                                    #FStar.Tactics.Typeclasses.solve
                                                    "--profile"
                                                  <:
                                                  Alloc.String.t_String;
                                                  Alloc.String.f_to_string #Hax_types.Cli_options.t_BackendName
                                                    #FStar.Tactics.Typeclasses.solve
                                                    backend
                                                  <:
                                                  Alloc.String.t_String
                                                ]
                                              in
                                              FStar.Pervasives.assert_norm
                                              (Prims.eq2 (List.Tot.length list) 2);
                                              Rust_primitives.Hax.array_of_list 2 list)
                                          <:
                                          Core.Array.Iter.t_IntoIter Alloc.String.t_String
                                            (mk_usize 2))
                                        (Core.Iter.Traits.Iterator.f_cloned #(Core.Slice.Iter.t_Iter
                                              Alloc.String.t_String)
                                            #FStar.Tactics.Typeclasses.solve
                                            #Alloc.String.t_String
                                            (Core.Slice.impl__iter #Alloc.String.t_String rhs
                                              <:
                                              Core.Slice.Iter.t_Iter Alloc.String.t_String)
                                          <:
                                          Core.Iter.Adapters.Cloned.t_Cloned
                                          (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                      <:
                                      Core.Iter.Adapters.Chain.t_Chain
                                        (Core.Array.Iter.t_IntoIter Alloc.String.t_String
                                            (mk_usize 2))
                                        (Core.Iter.Adapters.Cloned.t_Cloned
                                          (Core.Slice.Iter.t_Iter Alloc.String.t_String)))
                                  <:
                                  Core.Iter.Adapters.Chain.t_Chain
                                    (Core.Iter.Adapters.Cloned.t_Cloned
                                      (Core.Slice.Iter.t_Iter Alloc.String.t_String))
                                    (Core.Iter.Adapters.Chain.t_Chain
                                        (Core.Array.Iter.t_IntoIter Alloc.String.t_String
                                            (mk_usize 2))
                                        (Core.Iter.Adapters.Cloned.t_Cloned
                                          (Core.Slice.Iter.t_Iter Alloc.String.t_String))))
                            in
                            if
                              Rust_primitives.Hax.failure "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: `Let` nodes are supposed to be pre-processed\n\n\nNote: the error was labeled with context `AST import`.\n"
                                "" &&
                              options_1_.Hax_types.Cli_options.f_command =.
                              (Hax_types.Cli_options.Command_Backend
                                (Core.Clone.f_clone #(Hax_types.Cli_options.t_BackendOptions
                                      Prims.unit)
                                    #FStar.Tactics.Typeclasses.solve
                                    backend_options_with_profile
                                  <:
                                  Hax_types.Cli_options.t_BackendOptions Prims.unit)
                                <:
                                Hax_types.Cli_options.t_Command Prims.unit)
                            then
                              Core.Option.Option_Some
                              (Alloc.Slice.impl__to_vec #Alloc.String.t_String
                                  (lhs.[ { Core.Ops.Range.f_start = mk_usize 1 }
                                      <:
                                      Core.Ops.Range.t_RangeFrom usize ]
                                    <:
                                    t_Slice Alloc.String.t_String),
                                Alloc.Slice.impl__to_vec #Alloc.String.t_String rhs
                                <:
                                (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                                  Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
                              <:
                              Core.Option.t_Option
                              (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
                            else
                              Core.Option.Option_None
                              <:
                              Core.Option.t_Option
                              (Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                                Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
                    in
                    let into_flags, backend_flags:(Alloc.Vec.t_Vec Alloc.String.t_String
                        Alloc.Alloc.t_Global &
                      Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) =
                      Core.Option.impl__expect #(Alloc.Vec.t_Vec Alloc.String.t_String
                            Alloc.Alloc.t_Global &
                          Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
                        out
                        "Could not split arguments!"
                    in
                    Core.Result.Result_Ok
                    (backend, into_flags, backend_flags
                      <:
                      (Hax_types.Cli_options.t_BackendName &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Hax_types.Cli_options.t_BackendName &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
          | _ ->
            Core.Panicking.panic_fmt (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 1)
                  (mk_usize 0)
                  (let list =
                      [
                        "internal error: entered unreachable code: Expected backend options since the command starts with `into `!"
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                  (let list:Prims.list Core.Fmt.Rt.t_Argument = [] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
                    Rust_primitives.Hax.array_of_list 0 list)
                <:
                Core.Fmt.t_Arguments))
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err
        (Core.Convert.f_from #Anyhow.t_Error
            #(Clap_builder.Error.t_Error Clap_builder.Error.Format.t_RichFormatter)
            #FStar.Tactics.Typeclasses.solve
            err)
        <:
        Core.Result.t_Result
          (Hax_types.Cli_options.t_BackendName &
            Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
            Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result
      (Hax_types.Cli_options.t_BackendName &
        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
        Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error

type t_TestDirective =
  | TestDirective_SetCli {
    f_backend:Hax_types.Cli_options.t_BackendName;
    f_into_flags:Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global;
    f_backend_flags:Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global
  }: t_TestDirective
  | TestDirective_BackendDirective {
    f_backend:Hax_types.Cli_options.t_BackendName;
    f_directive:Alloc.String.t_String
  }: t_TestDirective
  | TestDirective_Off {
    f_backends:Std.Collections.Hash.Set.t_HashSet Hax_types.Cli_options.t_BackendName
      Std.Hash.Random.t_RandomState
  }: t_TestDirective

let impl_2: Core.Clone.t_Clone t_TestDirective =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Fmt.t_Debug t_TestDirective

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Marker.t_StructuralPartialEq t_TestDirective

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Cmp.t_PartialEq t_TestDirective t_TestDirective

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Cmp.t_Eq t_TestDirective

unfold
let impl_4 = impl_4'

type t_FailureKind =
  | FailureKind_Typecheck : t_FailureKind
  | FailureKind_Extract : t_FailureKind

let t_FailureKind_cast_to_repr (x: t_FailureKind) : isize =
  match x <: t_FailureKind with
  | FailureKind_Typecheck  -> mk_isize 0
  | FailureKind_Extract  -> mk_isize 1

let impl_12: Core.Clone.t_Clone t_FailureKind =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': Core.Fmt.t_Debug t_FailureKind

unfold
let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': Core.Marker.t_StructuralPartialEq t_FailureKind

unfold
let impl_15 = impl_15'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': Core.Cmp.t_PartialEq t_FailureKind t_FailureKind

unfold
let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': Core.Cmp.t_Eq t_FailureKind

unfold
let impl_14 = impl_14'

type t_ErrorCode = | ErrorCode : Alloc.String.t_String -> t_ErrorCode

let impl_17: Core.Clone.t_Clone t_ErrorCode =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18': Core.Fmt.t_Debug t_ErrorCode

unfold
let impl_18 = impl_18'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_20': Core.Marker.t_StructuralPartialEq t_ErrorCode

unfold
let impl_20 = impl_20'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_21': Core.Cmp.t_PartialEq t_ErrorCode t_ErrorCode

unfold
let impl_21 = impl_21'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19': Core.Cmp.t_Eq t_ErrorCode

unfold
let impl_19 = impl_19'

type t_ItemDirective =
  | ItemDirective_Failure {
    f_kind:t_FailureKind;
    f_backends:Std.Collections.Hash.Map.t_HashMap Hax_types.Cli_options.t_BackendName
      (Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global)
      Std.Hash.Random.t_RandomState
  }: t_ItemDirective

type t_Directive =
  | Directive_Test : t_TestDirective -> t_Directive
  | Directive_Item : t_ItemDirective -> t_Directive

let impl_7: Core.Clone.t_Clone t_Directive =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core.Fmt.t_Debug t_Directive

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core.Marker.t_StructuralPartialEq t_Directive

unfold
let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core.Cmp.t_PartialEq t_Directive t_Directive

unfold
let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Cmp.t_Eq t_Directive

unfold
let impl_9 = impl_9'

let impl_22: Core.Clone.t_Clone t_ItemDirective =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_23': Core.Fmt.t_Debug t_ItemDirective

unfold
let impl_23 = impl_23'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_25': Core.Marker.t_StructuralPartialEq t_ItemDirective

unfold
let impl_25 = impl_25'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_26': Core.Cmp.t_PartialEq t_ItemDirective t_ItemDirective

unfold
let impl_26 = impl_26'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_24': Core.Cmp.t_Eq t_ItemDirective

unfold
let impl_24 = impl_24'

let parse_backend_name (s: string)
    : Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error =
  Anyhow.f_context #(Core.Option.t_Option Hax_types.Cli_options.t_BackendName)
    #Hax_types.Cli_options.t_BackendName
    #Core.Convert.t_Infallible
    #FStar.Tactics.Typeclasses.solve
    #string
    (Core.Result.impl__ok #Hax_types.Cli_options.t_BackendName
        #Alloc.String.t_String
        (Clap_builder.Derive.f_from_str #Hax_types.Cli_options.t_BackendName
            #FStar.Tactics.Typeclasses.solve
            s
            true
          <:
          Core.Result.t_Result Hax_types.Cli_options.t_BackendName Alloc.String.t_String)
      <:
      Core.Option.t_Option Hax_types.Cli_options.t_BackendName)
    "Parsing backend name"

type t_DirectivesParser = | DirectivesParser : t_DirectivesParser

let e_PEST_GRAMMAR_DirectivesParser: t_Array string (mk_usize 0) =
  let list:Prims.list string = [] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 0);
  Rust_primitives.Hax.array_of_list 0 list

type t_Rule =
  | Rule_EOI : t_Rule
  | Rule_WHITESPACE : t_Rule
  | Rule_NEWLINE : t_Rule
  | Rule_directive : t_Rule
  | Rule_cli : t_Rule
  | Rule_backend_directive : t_Rule
  | Rule_off : t_Rule
  | Rule_fail : t_Rule
  | Rule_backend_fail : t_Rule
  | Rule_backend : t_Rule
  | Rule_errcode : t_Rule
  | Rule_fail_kind : t_Rule
  | Rule_line_text : t_Rule

let t_Rule_cast_to_repr (x: t_Rule) : isize =
  match x <: t_Rule with
  | Rule_EOI  -> mk_isize 0
  | Rule_WHITESPACE  -> mk_isize 1
  | Rule_NEWLINE  -> mk_isize 2
  | Rule_directive  -> mk_isize 3
  | Rule_cli  -> mk_isize 4
  | Rule_backend_directive  -> mk_isize 5
  | Rule_off  -> mk_isize 6
  | Rule_fail  -> mk_isize 7
  | Rule_backend_fail  -> mk_isize 8
  | Rule_backend  -> mk_isize 9
  | Rule_errcode  -> mk_isize 10
  | Rule_fail_kind  -> mk_isize 11
  | Rule_line_text  -> mk_isize 12

let impl_2__from__parser: Core.Clone.t_Clone t_Rule =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3__from__parser': Core.Marker.t_Copy t_Rule

unfold
let impl_3__from__parser = impl_3__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4__from__parser': Core.Fmt.t_Debug t_Rule

unfold
let impl_4__from__parser = impl_4__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6__from__parser': Core.Hash.t_Hash t_Rule

unfold
let impl_6__from__parser = impl_6__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8__from__parser': Core.Marker.t_StructuralPartialEq t_Rule

unfold
let impl_8__from__parser = impl_8__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9__from__parser': Core.Cmp.t_PartialEq t_Rule t_Rule

unfold
let impl_9__from__parser = impl_9__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5__from__parser': Core.Cmp.t_Eq t_Rule

unfold
let impl_5__from__parser = impl_5__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10__from__parser': Core.Cmp.t_PartialOrd t_Rule t_Rule

unfold
let impl_10__from__parser = impl_10__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7__from__parser': Core.Cmp.t_Ord t_Rule

unfold
let impl_7__from__parser = impl_7__from__parser'

let impl__all_rules (_: Prims.unit) : t_Slice t_Rule =
  (let list =
      [
        Rule_WHITESPACE <: t_Rule; Rule_NEWLINE <: t_Rule; Rule_directive <: t_Rule;
        Rule_cli <: t_Rule; Rule_backend_directive <: t_Rule; Rule_off <: t_Rule;
        Rule_fail <: t_Rule; Rule_backend_fail <: t_Rule; Rule_backend <: t_Rule;
        Rule_errcode <: t_Rule; Rule_fail_kind <: t_Rule; Rule_line_text <: t_Rule
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
    Rust_primitives.Hax.array_of_list 12 list)
  <:
  t_Slice t_Rule

let f_parse__impl_1__t_rules__t_visible__v_WHITESPACE
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__atomic #t_Rule
    state
    (Pest.Parser_state.Atomicity_Atomic <: Pest.Parser_state.t_Atomicity)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Core.Result.impl__or_else #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
              Alloc.Alloc.t_Global)
          #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Pest.Parser_state.impl_10__match_string #t_Rule state " "
            <:
            Core.Result.t_Result
              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Pest.Parser_state.impl_10__match_string #t_Rule state "\t"
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_hidden__skip
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  if
    (Pest.Parser_state.impl_10__atomicity #t_Rule state <: Pest.Parser_state.t_Atomicity) =.
    (Pest.Parser_state.Atomicity_NonAtomic <: Pest.Parser_state.t_Atomicity)
  then
    Pest.Parser_state.impl_10__repeat #t_Rule
      state
      (fun state ->
          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
          =
            state
          in
          f_parse__impl_1__t_rules__t_visible__v_WHITESPACE state
          <:
          Core.Result.t_Result
            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
  else
    Core.Result.Result_Ok state
    <:
    Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)

let f_parse__impl_1__t_rules__t_visible__v_NEWLINE
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Core.Result.impl__or_else #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
        Alloc.Alloc.t_Global)
    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    (Pest.Parser_state.impl_10__match_string #t_Rule state "\n"
      <:
      Core.Result.t_Result
        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__match_string #t_Rule state "\r\n"
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__fail_kind
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_fail_kind <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__atomic #t_Rule
          state
          (Pest.Parser_state.Atomicity_Atomic <: Pest.Parser_state.t_Atomicity)
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__or_else #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                    Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Pest.Parser_state.impl_10__match_string #t_Rule state "tc"
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Pest.Parser_state.impl_10__match_string #t_Rule state "extraction"
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__v_ANY
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__skip #t_Rule state (mk_usize 1)

let f_parse__impl_1__t_rules__t_visible__line_text
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_line_text <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Pest.Parser_state.impl_10__optional #t_Rule
                state
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                          (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Pest.Parser_state.impl_10__sequence #t_Rule
                          state
                          (fun state ->
                              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global =
                                state
                              in
                              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Pest.Parser_state.impl_10__lookahead #t_Rule
                                        state
                                        false
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            f_parse__impl_1__t_rules__t_visible__v_NEWLINE state
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        f_parse__impl_1__t_rules__t_hidden__skip state
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    f_parse__impl_1__t_rules__t_visible__v_ANY state
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          Pest.Parser_state.impl_10__repeat #t_Rule
                            state
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                Pest.Parser_state.impl_10__sequence #t_Rule
                                  state
                                  (fun state ->
                                      let state:Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global =
                                        state
                                      in
                                      Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (f_parse__impl_1__t_rules__t_hidden__skip state
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__sequence #t_Rule
                                              state
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Pest.Parser_state.impl_10__lookahead #t_Rule
                                                            state
                                                            false
                                                            (fun state ->
                                                                let state:Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global =
                                                                  state
                                                                in
                                                                f_parse__impl_1__t_rules__t_visible__v_NEWLINE
                                                                  state
                                                                <:
                                                                Core.Result.t_Result
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  )
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  ))
                                                          <:
                                                          Core.Result.t_Result
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global))
                                                        (fun state ->
                                                            let state:Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global =
                                                              state
                                                            in
                                                            f_parse__impl_1__t_rules__t_hidden__skip
                                                              state
                                                            <:
                                                            Core.Result.t_Result
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global)
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global))
                                                      <:
                                                      Core.Result.t_Result
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global))
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        f_parse__impl_1__t_rules__t_visible__v_ANY state

                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__cli
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_cli <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                        (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                            (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Pest.Parser_state.impl_10__match_string #t_Rule state "cli"
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_hidden__skip state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                        (fun state ->
                            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global =
                              state
                            in
                            Pest.Parser_state.impl_10__match_string #t_Rule state ":"
                            <:
                            Core.Result.t_Result
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global)
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global))
                    (fun state ->
                        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global =
                          state
                        in
                        f_parse__impl_1__t_rules__t_hidden__skip state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Pest.Parser_state.impl_10__optional #t_Rule
                      state
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          f_parse__impl_1__t_rules__t_visible__line_text state
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__v_EOI
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_EOI <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__end_of_input #t_Rule state
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__v_SOI
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__start_of_input #t_Rule state

let f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Core.Result.impl__or_else #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
        Alloc.Alloc.t_Global)
    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    (Core.Result.impl__or_else #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
            Alloc.Alloc.t_Global)
        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
        (Pest.Parser_state.impl_10__match_range #t_Rule
            state
            ({ Core.Ops.Range.f_start = 'a'; Core.Ops.Range.f_end = 'z' }
              <:
              Core.Ops.Range.t_Range char)
          <:
          Core.Result.t_Result
            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        (fun state ->
            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
              Alloc.Alloc.t_Global =
              state
            in
            Pest.Parser_state.impl_10__match_range #t_Rule
              state
              ({ Core.Ops.Range.f_start = 'A'; Core.Ops.Range.f_end = 'Z' }
                <:
                Core.Ops.Range.t_Range char)
            <:
            Core.Result.t_Result
              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
      <:
      Core.Result.t_Result
        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__match_range #t_Rule
          state
          ({ Core.Ops.Range.f_start = '0'; Core.Ops.Range.f_end = '9' }
            <:
            Core.Ops.Range.t_Range char)
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__backend
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_backend <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__atomic #t_Rule
          state
          (Pest.Parser_state.Atomicity_Atomic <: Pest.Parser_state.t_Atomicity)
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Pest.Parser_state.impl_10__sequence #t_Rule
                state
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                          (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Pest.Parser_state.impl_10__sequence #t_Rule
                          state
                          (fun state ->
                              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global =
                                state
                              in
                              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC state
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    Pest.Parser_state.impl_10__repeat #t_Rule
                                      state
                                      (fun state ->
                                          let state:Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global =
                                            state
                                          in
                                          f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC state

                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          Pest.Parser_state.impl_10__repeat #t_Rule
                            state
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                Pest.Parser_state.impl_10__sequence #t_Rule
                                  state
                                  (fun state ->
                                      let state:Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global =
                                        state
                                      in
                                      Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Pest.Parser_state.impl_10__match_string #t_Rule
                                                state
                                                "-"
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC
                                                  state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__repeat #t_Rule
                                              state
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC
                                                    state
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__backend_directive
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_backend_directive <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                        (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                            (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Pest.Parser_state.impl_10__match_string #t_Rule
                                                        state
                                                        "backend"
                                                      <:
                                                      Core.Result.t_Result
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global))
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        f_parse__impl_1__t_rules__t_hidden__skip state

                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                                (fun state ->
                                                    let state:Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global =
                                                      state
                                                    in
                                                    Pest.Parser_state.impl_10__match_string #t_Rule
                                                      state
                                                      "("
                                                    <:
                                                    Core.Result.t_Result
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global)
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global))
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_hidden__skip state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            f_parse__impl_1__t_rules__t_visible__backend state
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        f_parse__impl_1__t_rules__t_hidden__skip state
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    Pest.Parser_state.impl_10__match_string #t_Rule state ")"
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_hidden__skip state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                        (fun state ->
                            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global =
                              state
                            in
                            Pest.Parser_state.impl_10__match_string #t_Rule state ":"
                            <:
                            Core.Result.t_Result
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global)
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global))
                    (fun state ->
                        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global =
                          state
                        in
                        f_parse__impl_1__t_rules__t_hidden__skip state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Pest.Parser_state.impl_10__optional #t_Rule
                      state
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          f_parse__impl_1__t_rules__t_visible__line_text state
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__off
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_off <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                        (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                            (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Pest.Parser_state.impl_10__match_string #t_Rule state "off"
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        f_parse__impl_1__t_rules__t_hidden__skip state
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    Pest.Parser_state.impl_10__match_string #t_Rule state ":"
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_hidden__skip state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                        (fun state ->
                            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global =
                              state
                            in
                            f_parse__impl_1__t_rules__t_visible__backend state
                            <:
                            Core.Result.t_Result
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global)
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global))
                    (fun state ->
                        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global =
                          state
                        in
                        f_parse__impl_1__t_rules__t_hidden__skip state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Pest.Parser_state.impl_10__sequence #t_Rule
                      state
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          Pest.Parser_state.impl_10__optional #t_Rule
                            state
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                  #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Pest.Parser_state.impl_10__sequence #t_Rule
                                      state
                                      (fun state ->
                                          let state:Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global =
                                            state
                                          in
                                          Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Pest.Parser_state.impl_10__match_string #t_Rule
                                                    state
                                                    ","
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                                (fun state ->
                                                    let state:Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global =
                                                      state
                                                    in
                                                    f_parse__impl_1__t_rules__t_hidden__skip state
                                                    <:
                                                    Core.Result.t_Result
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global)
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global))
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_visible__backend state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                                  (fun state ->
                                      let state:Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global =
                                        state
                                      in
                                      Pest.Parser_state.impl_10__repeat #t_Rule
                                        state
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__sequence #t_Rule
                                              state
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (f_parse__impl_1__t_rules__t_hidden__skip state
                                                      <:
                                                      Core.Result.t_Result
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global))
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        Pest.Parser_state.impl_10__sequence #t_Rule
                                                          state
                                                          (fun state ->
                                                              let state:Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global =
                                                                state
                                                              in
                                                              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                #(Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                #(Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    #(Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    #(Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    (Pest.Parser_state.impl_10__match_string
                                                                        #t_Rule
                                                                        state
                                                                        ","
                                                                      <:
                                                                      Core.Result.t_Result
                                                                        (Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global)
                                                                        (Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global))
                                                                    (fun state ->
                                                                        let state:Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global =
                                                                          state
                                                                        in
                                                                        f_parse__impl_1__t_rules__t_hidden__skip
                                                                          state
                                                                        <:
                                                                        Core.Result.t_Result
                                                                          (Alloc.Boxed.t_Box
                                                                              (Pest.Parser_state.t_ParserState
                                                                                t_Rule)
                                                                              Alloc.Alloc.t_Global)
                                                                          (Alloc.Boxed.t_Box
                                                                              (Pest.Parser_state.t_ParserState
                                                                                t_Rule)
                                                                              Alloc.Alloc.t_Global))
                                                                  <:
                                                                  Core.Result.t_Result
                                                                    (Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    (Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global))
                                                                (fun state ->
                                                                    let state:Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                    =
                                                                      state
                                                                    in
                                                                    f_parse__impl_1__t_rules__t_visible__backend
                                                                      state
                                                                    <:
                                                                    Core.Result.t_Result
                                                                      (Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global)
                                                                      (Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global))
                                                              <:
                                                              Core.Result.t_Result
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global))
                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__errcode
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_errcode <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__atomic #t_Rule
          state
          (Pest.Parser_state.Atomicity_Atomic <: Pest.Parser_state.t_Atomicity)
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Pest.Parser_state.impl_10__sequence #t_Rule
                state
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                          (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          Pest.Parser_state.impl_10__repeat #t_Rule
                            state
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_visible__v_ASCII_ALPHANUMERIC state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__backend_fail
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_backend_fail <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                        (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                            (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (f_parse__impl_1__t_rules__t_visible__backend state
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_hidden__skip state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__match_string #t_Rule
                                              state
                                              "("
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        f_parse__impl_1__t_rules__t_hidden__skip state
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    f_parse__impl_1__t_rules__t_visible__errcode state
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_hidden__skip state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                        (fun state ->
                            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global =
                              state
                            in
                            Pest.Parser_state.impl_10__sequence #t_Rule
                              state
                              (fun state ->
                                  let state:Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
                                    state
                                  in
                                  Pest.Parser_state.impl_10__optional #t_Rule
                                    state
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Pest.Parser_state.impl_10__sequence #t_Rule
                                              state
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Pest.Parser_state.impl_10__match_string #t_Rule
                                                            state
                                                            ","
                                                          <:
                                                          Core.Result.t_Result
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global))
                                                        (fun state ->
                                                            let state:Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global =
                                                              state
                                                            in
                                                            f_parse__impl_1__t_rules__t_hidden__skip
                                                              state
                                                            <:
                                                            Core.Result.t_Result
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global)
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global))
                                                      <:
                                                      Core.Result.t_Result
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global))
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        f_parse__impl_1__t_rules__t_visible__errcode
                                                          state
                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                          (fun state ->
                                              let state:Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global =
                                                state
                                              in
                                              Pest.Parser_state.impl_10__repeat #t_Rule
                                                state
                                                (fun state ->
                                                    let state:Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global =
                                                      state
                                                    in
                                                    Pest.Parser_state.impl_10__sequence #t_Rule
                                                      state
                                                      (fun state ->
                                                          let state:Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global =
                                                            state
                                                          in
                                                          Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (f_parse__impl_1__t_rules__t_hidden__skip
                                                                state
                                                              <:
                                                              Core.Result.t_Result
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global))
                                                            (fun state ->
                                                                let state:Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global =
                                                                  state
                                                                in
                                                                Pest.Parser_state.impl_10__sequence #t_Rule
                                                                  state
                                                                  (fun state ->
                                                                      let state:Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global =
                                                                        state
                                                                      in
                                                                      Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global)
                                                                        #(Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global)
                                                                        #(Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global)
                                                                        (Core.Result.impl__and_then #(
                                                                              Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            #(Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            #(Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            (Pest.Parser_state.impl_10__match_string
                                                                                #t_Rule
                                                                                state
                                                                                ","
                                                                              <:
                                                                              Core.Result.t_Result
                                                                                (Alloc.Boxed.t_Box
                                                                                    (Pest.Parser_state.t_ParserState
                                                                                      t_Rule)
                                                                                    Alloc.Alloc.t_Global
                                                                                )
                                                                                (Alloc.Boxed.t_Box
                                                                                    (Pest.Parser_state.t_ParserState
                                                                                      t_Rule)
                                                                                    Alloc.Alloc.t_Global
                                                                                ))
                                                                            (fun state ->
                                                                                let state:Alloc.Boxed.t_Box
                                                                                  (Pest.Parser_state.t_ParserState
                                                                                    t_Rule)
                                                                                  Alloc.Alloc.t_Global
                                                                                =
                                                                                  state
                                                                                in
                                                                                f_parse__impl_1__t_rules__t_hidden__skip
                                                                                  state
                                                                                <:
                                                                                Core.Result.t_Result
                                                                                  (Alloc.Boxed.t_Box
                                                                                      (Pest.Parser_state.t_ParserState
                                                                                        t_Rule)
                                                                                      Alloc.Alloc.t_Global
                                                                                  )
                                                                                  (Alloc.Boxed.t_Box
                                                                                      (Pest.Parser_state.t_ParserState
                                                                                        t_Rule)
                                                                                      Alloc.Alloc.t_Global
                                                                                  ))
                                                                          <:
                                                                          Core.Result.t_Result
                                                                            (Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            (Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            ))
                                                                        (fun state ->
                                                                            let state:Alloc.Boxed.t_Box
                                                                              (Pest.Parser_state.t_ParserState
                                                                                t_Rule)
                                                                              Alloc.Alloc.t_Global =
                                                                              state
                                                                            in
                                                                            f_parse__impl_1__t_rules__t_visible__errcode
                                                                              state
                                                                            <:
                                                                            Core.Result.t_Result
                                                                              (Alloc.Boxed.t_Box
                                                                                  (Pest.Parser_state.t_ParserState
                                                                                    t_Rule)
                                                                                  Alloc.Alloc.t_Global
                                                                              )
                                                                              (Alloc.Boxed.t_Box
                                                                                  (Pest.Parser_state.t_ParserState
                                                                                    t_Rule)
                                                                                  Alloc.Alloc.t_Global
                                                                              ))
                                                                      <:
                                                                      Core.Result.t_Result
                                                                        (Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global)
                                                                        (Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global))
                                                                <:
                                                                Core.Result.t_Result
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  )
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  ))
                                                          <:
                                                          Core.Result.t_Result
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global))
                                                    <:
                                                    Core.Result.t_Result
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global)
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global))
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                            <:
                            Core.Result.t_Result
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global)
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global))
                    (fun state ->
                        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global =
                          state
                        in
                        f_parse__impl_1__t_rules__t_hidden__skip state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Pest.Parser_state.impl_10__match_string #t_Rule state ")"
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__fail
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_fail <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                        (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                            (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        #(Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (Pest.Parser_state.impl_10__match_string
                                                                #t_Rule
                                                                state
                                                                "fail"
                                                              <:
                                                              Core.Result.t_Result
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global))
                                                            (fun state ->
                                                                let state:Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global =
                                                                  state
                                                                in
                                                                f_parse__impl_1__t_rules__t_hidden__skip
                                                                  state
                                                                <:
                                                                Core.Result.t_Result
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  )
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  ))
                                                          <:
                                                          Core.Result.t_Result
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global))
                                                        (fun state ->
                                                            let state:Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global =
                                                              state
                                                            in
                                                            Pest.Parser_state.impl_10__match_string #t_Rule
                                                              state
                                                              "("
                                                            <:
                                                            Core.Result.t_Result
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global)
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global))
                                                      <:
                                                      Core.Result.t_Result
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global))
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        f_parse__impl_1__t_rules__t_hidden__skip state

                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                                (fun state ->
                                                    let state:Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global =
                                                      state
                                                    in
                                                    f_parse__impl_1__t_rules__t_visible__fail_kind state

                                                    <:
                                                    Core.Result.t_Result
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global)
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global))
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_hidden__skip state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__match_string #t_Rule
                                              state
                                              ")"
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        f_parse__impl_1__t_rules__t_hidden__skip state
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    Pest.Parser_state.impl_10__match_string #t_Rule state ":"
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_hidden__skip state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                        (fun state ->
                            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global =
                              state
                            in
                            f_parse__impl_1__t_rules__t_visible__backend_fail state
                            <:
                            Core.Result.t_Result
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global)
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global))
                    (fun state ->
                        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global =
                          state
                        in
                        f_parse__impl_1__t_rules__t_hidden__skip state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    Pest.Parser_state.impl_10__sequence #t_Rule
                      state
                      (fun state ->
                          let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global =
                            state
                          in
                          Pest.Parser_state.impl_10__optional #t_Rule
                            state
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                  #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Pest.Parser_state.impl_10__sequence #t_Rule
                                      state
                                      (fun state ->
                                          let state:Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global =
                                            state
                                          in
                                          Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                #(Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Pest.Parser_state.impl_10__match_string #t_Rule
                                                    state
                                                    ","
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                                (fun state ->
                                                    let state:Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global =
                                                      state
                                                    in
                                                    f_parse__impl_1__t_rules__t_hidden__skip state
                                                    <:
                                                    Core.Result.t_Result
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global)
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global))
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_visible__backend_fail state

                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                                  (fun state ->
                                      let state:Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global =
                                        state
                                      in
                                      Pest.Parser_state.impl_10__repeat #t_Rule
                                        state
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__sequence #t_Rule
                                              state
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    #(Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (f_parse__impl_1__t_rules__t_hidden__skip state
                                                      <:
                                                      Core.Result.t_Result
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global)
                                                        (Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global))
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        Pest.Parser_state.impl_10__sequence #t_Rule
                                                          state
                                                          (fun state ->
                                                              let state:Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global =
                                                                state
                                                              in
                                                              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                #(Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                #(Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    #(Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    #(Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    (Pest.Parser_state.impl_10__match_string
                                                                        #t_Rule
                                                                        state
                                                                        ","
                                                                      <:
                                                                      Core.Result.t_Result
                                                                        (Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global)
                                                                        (Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global))
                                                                    (fun state ->
                                                                        let state:Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global =
                                                                          state
                                                                        in
                                                                        f_parse__impl_1__t_rules__t_hidden__skip
                                                                          state
                                                                        <:
                                                                        Core.Result.t_Result
                                                                          (Alloc.Boxed.t_Box
                                                                              (Pest.Parser_state.t_ParserState
                                                                                t_Rule)
                                                                              Alloc.Alloc.t_Global)
                                                                          (Alloc.Boxed.t_Box
                                                                              (Pest.Parser_state.t_ParserState
                                                                                t_Rule)
                                                                              Alloc.Alloc.t_Global))
                                                                  <:
                                                                  Core.Result.t_Result
                                                                    (Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global)
                                                                    (Alloc.Boxed.t_Box
                                                                        (Pest.Parser_state.t_ParserState
                                                                          t_Rule)
                                                                        Alloc.Alloc.t_Global))
                                                                (fun state ->
                                                                    let state:Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                    =
                                                                      state
                                                                    in
                                                                    f_parse__impl_1__t_rules__t_visible__backend_fail
                                                                      state
                                                                    <:
                                                                    Core.Result.t_Result
                                                                      (Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global)
                                                                      (Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global))
                                                              <:
                                                              Core.Result.t_Result
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global))
                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

let f_parse__impl_1__t_rules__t_visible__directive
      (state: Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
    : Core.Result.t_Result
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global) =
  Pest.Parser_state.impl_10__rule #t_Rule
    state
    (Rule_directive <: t_Rule)
    (fun state ->
        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
          state
        in
        Pest.Parser_state.impl_10__sequence #t_Rule
          state
          (fun state ->
              let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                Alloc.Alloc.t_Global =
                state
              in
              Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                        (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                        Alloc.Alloc.t_Global)
                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                            (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                        (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            #(Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (f_parse__impl_1__t_rules__t_visible__v_SOI state
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                            (fun state ->
                                                let state:Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global =
                                                  state
                                                in
                                                f_parse__impl_1__t_rules__t_hidden__skip state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                        (fun state ->
                                            let state:Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global =
                                              state
                                            in
                                            Pest.Parser_state.impl_10__sequence #t_Rule
                                              state
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  Pest.Parser_state.impl_10__optional #t_Rule
                                                    state
                                                    (fun state ->
                                                        let state:Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global =
                                                          state
                                                        in
                                                        Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          #(Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          #(Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (f_parse__impl_1__t_rules__t_visible__v_NEWLINE
                                                              state
                                                            <:
                                                            Core.Result.t_Result
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global)
                                                              (Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global))
                                                          (fun state ->
                                                              let state:Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global =
                                                                state
                                                              in
                                                              Pest.Parser_state.impl_10__repeat #t_Rule
                                                                state
                                                                (fun state ->
                                                                    let state:Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                    =
                                                                      state
                                                                    in
                                                                    Pest.Parser_state.impl_10__sequence
                                                                      #t_Rule
                                                                      state
                                                                      (fun state ->
                                                                          let state:Alloc.Boxed.t_Box
                                                                            (Pest.Parser_state.t_ParserState
                                                                              t_Rule)
                                                                            Alloc.Alloc.t_Global =
                                                                            state
                                                                          in
                                                                          Core.Result.impl__and_then
                                                                            #(Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            #(Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            #(Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            (f_parse__impl_1__t_rules__t_hidden__skip
                                                                                state
                                                                              <:
                                                                              Core.Result.t_Result
                                                                                (Alloc.Boxed.t_Box
                                                                                    (Pest.Parser_state.t_ParserState
                                                                                      t_Rule)
                                                                                    Alloc.Alloc.t_Global
                                                                                )
                                                                                (Alloc.Boxed.t_Box
                                                                                    (Pest.Parser_state.t_ParserState
                                                                                      t_Rule)
                                                                                    Alloc.Alloc.t_Global
                                                                                ))
                                                                            (fun state ->
                                                                                let state:Alloc.Boxed.t_Box
                                                                                  (Pest.Parser_state.t_ParserState
                                                                                    t_Rule)
                                                                                  Alloc.Alloc.t_Global
                                                                                =
                                                                                  state
                                                                                in
                                                                                f_parse__impl_1__t_rules__t_visible__v_NEWLINE
                                                                                  state
                                                                                <:
                                                                                Core.Result.t_Result
                                                                                  (Alloc.Boxed.t_Box
                                                                                      (Pest.Parser_state.t_ParserState
                                                                                        t_Rule)
                                                                                      Alloc.Alloc.t_Global
                                                                                  )
                                                                                  (Alloc.Boxed.t_Box
                                                                                      (Pest.Parser_state.t_ParserState
                                                                                        t_Rule)
                                                                                      Alloc.Alloc.t_Global
                                                                                  ))
                                                                          <:
                                                                          Core.Result.t_Result
                                                                            (Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            )
                                                                            (Alloc.Boxed.t_Box
                                                                                (Pest.Parser_state.t_ParserState
                                                                                  t_Rule)
                                                                                Alloc.Alloc.t_Global
                                                                            ))
                                                                    <:
                                                                    Core.Result.t_Result
                                                                      (Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global)
                                                                      (Alloc.Boxed.t_Box
                                                                          (Pest.Parser_state.t_ParserState
                                                                            t_Rule)
                                                                          Alloc.Alloc.t_Global))
                                                              <:
                                                              Core.Result.t_Result
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global))
                                                        <:
                                                        Core.Result.t_Result
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global)
                                                          (Alloc.Boxed.t_Box
                                                              (Pest.Parser_state.t_ParserState
                                                                t_Rule) Alloc.Alloc.t_Global))
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                      <:
                                      Core.Result.t_Result
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global)
                                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global))
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        f_parse__impl_1__t_rules__t_hidden__skip state
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                                (fun state ->
                                    let state:Alloc.Boxed.t_Box
                                      (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                                    =
                                      state
                                    in
                                    Core.Result.impl__or_else #(Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      #(Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Core.Result.impl__or_else #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Core.Result.impl__or_else #(Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              #(Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              #(Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (f_parse__impl_1__t_rules__t_visible__cli state
                                                <:
                                                Core.Result.t_Result
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global)
                                                  (Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global))
                                              (fun state ->
                                                  let state:Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global =
                                                    state
                                                  in
                                                  f_parse__impl_1__t_rules__t_visible__backend_directive
                                                    state
                                                  <:
                                                  Core.Result.t_Result
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global)
                                                    (Alloc.Boxed.t_Box
                                                        (Pest.Parser_state.t_ParserState t_Rule)
                                                        Alloc.Alloc.t_Global))
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                          (fun state ->
                                              let state:Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global =
                                                state
                                              in
                                              f_parse__impl_1__t_rules__t_visible__off state
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                      (fun state ->
                                          let state:Alloc.Boxed.t_Box
                                            (Pest.Parser_state.t_ParserState t_Rule)
                                            Alloc.Alloc.t_Global =
                                            state
                                          in
                                          f_parse__impl_1__t_rules__t_visible__fail state
                                          <:
                                          Core.Result.t_Result
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global)
                                            (Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global))
                                    <:
                                    Core.Result.t_Result
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global)
                                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global))
                              <:
                              Core.Result.t_Result
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global)
                                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                    Alloc.Alloc.t_Global))
                            (fun state ->
                                let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global =
                                  state
                                in
                                f_parse__impl_1__t_rules__t_hidden__skip state
                                <:
                                Core.Result.t_Result
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global)
                                  (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                      Alloc.Alloc.t_Global))
                          <:
                          Core.Result.t_Result
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global)
                            (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                Alloc.Alloc.t_Global))
                        (fun state ->
                            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global =
                              state
                            in
                            Pest.Parser_state.impl_10__sequence #t_Rule
                              state
                              (fun state ->
                                  let state:Alloc.Boxed.t_Box
                                    (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global =
                                    state
                                  in
                                  Pest.Parser_state.impl_10__optional #t_Rule
                                    state
                                    (fun state ->
                                        let state:Alloc.Boxed.t_Box
                                          (Pest.Parser_state.t_ParserState t_Rule)
                                          Alloc.Alloc.t_Global =
                                          state
                                        in
                                        Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          #(Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (f_parse__impl_1__t_rules__t_visible__v_NEWLINE state
                                            <:
                                            Core.Result.t_Result
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global)
                                              (Alloc.Boxed.t_Box
                                                  (Pest.Parser_state.t_ParserState t_Rule)
                                                  Alloc.Alloc.t_Global))
                                          (fun state ->
                                              let state:Alloc.Boxed.t_Box
                                                (Pest.Parser_state.t_ParserState t_Rule)
                                                Alloc.Alloc.t_Global =
                                                state
                                              in
                                              Pest.Parser_state.impl_10__repeat #t_Rule
                                                state
                                                (fun state ->
                                                    let state:Alloc.Boxed.t_Box
                                                      (Pest.Parser_state.t_ParserState t_Rule)
                                                      Alloc.Alloc.t_Global =
                                                      state
                                                    in
                                                    Pest.Parser_state.impl_10__sequence #t_Rule
                                                      state
                                                      (fun state ->
                                                          let state:Alloc.Boxed.t_Box
                                                            (Pest.Parser_state.t_ParserState t_Rule)
                                                            Alloc.Alloc.t_Global =
                                                            state
                                                          in
                                                          Core.Result.impl__and_then #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            #(Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (f_parse__impl_1__t_rules__t_hidden__skip
                                                                state
                                                              <:
                                                              Core.Result.t_Result
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global)
                                                                (Alloc.Boxed.t_Box
                                                                    (Pest.Parser_state.t_ParserState
                                                                      t_Rule) Alloc.Alloc.t_Global))
                                                            (fun state ->
                                                                let state:Alloc.Boxed.t_Box
                                                                  (Pest.Parser_state.t_ParserState
                                                                    t_Rule) Alloc.Alloc.t_Global =
                                                                  state
                                                                in
                                                                f_parse__impl_1__t_rules__t_visible__v_NEWLINE
                                                                  state
                                                                <:
                                                                Core.Result.t_Result
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  )
                                                                  (Alloc.Boxed.t_Box
                                                                      (Pest.Parser_state.t_ParserState
                                                                        t_Rule) Alloc.Alloc.t_Global
                                                                  ))
                                                          <:
                                                          Core.Result.t_Result
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global)
                                                            (Alloc.Boxed.t_Box
                                                                (Pest.Parser_state.t_ParserState
                                                                  t_Rule) Alloc.Alloc.t_Global))
                                                    <:
                                                    Core.Result.t_Result
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global)
                                                      (Alloc.Boxed.t_Box
                                                          (Pest.Parser_state.t_ParserState t_Rule)
                                                          Alloc.Alloc.t_Global))
                                              <:
                                              Core.Result.t_Result
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global)
                                                (Alloc.Boxed.t_Box
                                                    (Pest.Parser_state.t_ParserState t_Rule)
                                                    Alloc.Alloc.t_Global))
                                        <:
                                        Core.Result.t_Result
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global)
                                          (Alloc.Boxed.t_Box
                                              (Pest.Parser_state.t_ParserState t_Rule)
                                              Alloc.Alloc.t_Global))
                                  <:
                                  Core.Result.t_Result
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global)
                                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                        Alloc.Alloc.t_Global))
                            <:
                            Core.Result.t_Result
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global)
                              (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                                  Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global)
                        (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                            Alloc.Alloc.t_Global))
                    (fun state ->
                        let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global =
                          state
                        in
                        f_parse__impl_1__t_rules__t_hidden__skip state
                        <:
                        Core.Result.t_Result
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global)
                          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                              Alloc.Alloc.t_Global))
                  <:
                  Core.Result.t_Result
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    )
                    (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global
                    ))
                (fun state ->
                    let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                      Alloc.Alloc.t_Global =
                      state
                    in
                    f_parse__impl_1__t_rules__t_visible__v_EOI state
                    <:
                    Core.Result.t_Result
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global)
                      (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
                          Alloc.Alloc.t_Global))
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
        <:
        Core.Result.t_Result
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
          (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__parser: Pest.Parser.t_Parser t_DirectivesParser t_Rule =
  {
    f_parse_pre = (fun (rule: t_Rule) (input: string) -> true);
    f_parse_post
    =
    (fun
        (rule: t_Rule)
        (input: string)
        (out:
          Core.Result.t_Result (Pest.Iterators.Pairs.t_Pairs t_Rule) (Pest.Error.t_Error t_Rule))
        ->
        true);
    f_parse
    =
    fun (rule: t_Rule) (input: string) ->
      Pest.Parser_state.state #t_Rule
        input
        (fun state ->
            let state:Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule)
              Alloc.Alloc.t_Global =
              state
            in
            match rule <: t_Rule with
            | Rule_WHITESPACE  ->
              f_parse__impl_1__t_rules__t_visible__v_WHITESPACE state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_NEWLINE  ->
              f_parse__impl_1__t_rules__t_visible__v_NEWLINE state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_directive  ->
              f_parse__impl_1__t_rules__t_visible__directive state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_cli  ->
              f_parse__impl_1__t_rules__t_visible__cli state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_backend_directive  ->
              f_parse__impl_1__t_rules__t_visible__backend_directive state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_off  ->
              f_parse__impl_1__t_rules__t_visible__off state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_fail  ->
              f_parse__impl_1__t_rules__t_visible__fail state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_backend_fail  ->
              f_parse__impl_1__t_rules__t_visible__backend_fail state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_backend  ->
              f_parse__impl_1__t_rules__t_visible__backend state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_errcode  ->
              f_parse__impl_1__t_rules__t_visible__errcode state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_fail_kind  ->
              f_parse__impl_1__t_rules__t_visible__fail_kind state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_line_text  ->
              f_parse__impl_1__t_rules__t_visible__line_text state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
            | Rule_EOI  ->
              f_parse__impl_1__t_rules__t_visible__v_EOI state
              <:
              Core.Result.t_Result
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global)
                (Alloc.Boxed.t_Box (Pest.Parser_state.t_ParserState t_Rule) Alloc.Alloc.t_Global))
  }

type t_FailEntry = {
  f_backend:Alloc.String.t_String;
  f_errcodes:Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global
}

type t_Directive__from__parser =
  | Directive_Cli { f_flags:Alloc.String.t_String }: t_Directive__from__parser
  | Directive_Backend {
    f_backend:Alloc.String.t_String;
    f_value:Alloc.String.t_String
  }: t_Directive__from__parser
  | Directive_Off { f_backends:Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global }: t_Directive__from__parser
  | Directive_Fail {
    f_kind:t_FailureKind;
    f_entries:Alloc.Vec.t_Vec t_FailEntry Alloc.Alloc.t_Global
  }: t_Directive__from__parser

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_TryFrom t_Directive t_Directive__from__parser =
  {
    f_Error = Anyhow.t_Error;
    f_try_from_pre = (fun (value: t_Directive__from__parser) -> true);
    f_try_from_post
    =
    (fun
        (value: t_Directive__from__parser)
        (out: Core.Result.t_Result t_Directive Anyhow.t_Error)
        ->
        true);
    f_try_from
    =
    fun (value: t_Directive__from__parser) ->
      match value <: t_Directive__from__parser with
      | Directive_Cli { f_flags = flags } ->
        (match
            parse_cli (Core.Ops.Deref.f_deref #Alloc.String.t_String
                  #FStar.Tactics.Typeclasses.solve
                  flags
                <:
                string)
            <:
            Core.Result.t_Result
              (Hax_types.Cli_options.t_BackendName &
                Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global &
                Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) Anyhow.t_Error
          with
          | Core.Result.Result_Ok (backend, into_flags, backend_flags) ->
            Core.Result.Result_Ok
            (Directive_Test
              (TestDirective_SetCli
                ({ f_backend = backend; f_into_flags = into_flags; f_backend_flags = backend_flags }
                )
                <:
                t_TestDirective)
              <:
              t_Directive)
            <:
            Core.Result.t_Result t_Directive Anyhow.t_Error
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Directive Anyhow.t_Error)
      | Directive_Backend { f_backend = backend ; f_value = value } ->
        (match
            parse_backend_name (Core.Ops.Deref.f_deref #Alloc.String.t_String
                  #FStar.Tactics.Typeclasses.solve
                  backend
                <:
                string)
            <:
            Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error
          with
          | Core.Result.Result_Ok hoist20 ->
            Core.Result.Result_Ok
            (Directive_Test
              (TestDirective_BackendDirective ({ f_backend = hoist20; f_directive = value })
                <:
                t_TestDirective)
              <:
              t_Directive)
            <:
            Core.Result.t_Result t_Directive Anyhow.t_Error
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Directive Anyhow.t_Error)
      | Directive_Off { f_backends = backends } ->
        (match
            Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
                  (Alloc.Vec.Into_iter.t_IntoIter Alloc.String.t_String Alloc.Alloc.t_Global)
                  (Alloc.String.t_String
                      -> Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error))
              #FStar.Tactics.Typeclasses.solve
              #(Core.Result.t_Result
                  (Std.Collections.Hash.Set.t_HashSet Hax_types.Cli_options.t_BackendName
                      Std.Hash.Random.t_RandomState) Anyhow.t_Error)
              (Core.Iter.Traits.Iterator.f_map #(Alloc.Vec.Into_iter.t_IntoIter
                      Alloc.String.t_String Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  #(Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error)
                  (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec Alloc.String.t_String
                          Alloc.Alloc.t_Global)
                      #FStar.Tactics.Typeclasses.solve
                      backends
                    <:
                    Alloc.Vec.Into_iter.t_IntoIter Alloc.String.t_String Alloc.Alloc.t_Global)
                  (fun s ->
                      let s:Alloc.String.t_String = s in
                      parse_backend_name (Alloc.String.impl_String__as_str s <: string)
                      <:
                      Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error)
                <:
                Core.Iter.Adapters.Map.t_Map
                  (Alloc.Vec.Into_iter.t_IntoIter Alloc.String.t_String Alloc.Alloc.t_Global)
                  (Alloc.String.t_String
                      -> Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error))
            <:
            Core.Result.t_Result
              (Std.Collections.Hash.Set.t_HashSet Hax_types.Cli_options.t_BackendName
                  Std.Hash.Random.t_RandomState) Anyhow.t_Error
          with
          | Core.Result.Result_Ok hoist22 ->
            Core.Result.Result_Ok
            (Directive_Test (TestDirective_Off ({ f_backends = hoist22 }) <: t_TestDirective)
              <:
              t_Directive)
            <:
            Core.Result.t_Result t_Directive Anyhow.t_Error
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Directive Anyhow.t_Error)
      | Directive_Fail { f_kind = kind ; f_entries = entries } ->
        match
          Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
                (Alloc.Vec.Into_iter.t_IntoIter t_FailEntry Alloc.Alloc.t_Global)
                (t_FailEntry
                    -> Core.Result.t_Result
                        (Hax_types.Cli_options.t_BackendName &
                          Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global) Anyhow.t_Error))
            #FStar.Tactics.Typeclasses.solve
            #(Core.Result.t_Result
                (Std.Collections.Hash.Map.t_HashMap Hax_types.Cli_options.t_BackendName
                    (Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global)
                    Std.Hash.Random.t_RandomState) Anyhow.t_Error)
            (Core.Iter.Traits.Iterator.f_map #(Alloc.Vec.Into_iter.t_IntoIter t_FailEntry
                    Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                #(Core.Result.t_Result
                    (Hax_types.Cli_options.t_BackendName &
                      Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global) Anyhow.t_Error)
                (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec t_FailEntry
                        Alloc.Alloc.t_Global)
                    #FStar.Tactics.Typeclasses.solve
                    entries
                  <:
                  Alloc.Vec.Into_iter.t_IntoIter t_FailEntry Alloc.Alloc.t_Global)
                (fun temp_0_ ->
                    let { f_backend = backend ; f_errcodes = errcodes }:t_FailEntry = temp_0_ in
                    match
                      parse_backend_name (Core.Ops.Deref.f_deref #Alloc.String.t_String
                            #FStar.Tactics.Typeclasses.solve
                            backend
                          <:
                          string)
                      <:
                      Core.Result.t_Result Hax_types.Cli_options.t_BackendName Anyhow.t_Error
                    with
                    | Core.Result.Result_Ok hoist24 ->
                      Core.Result.Result_Ok
                      (hoist24,
                        (Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
                                (Alloc.Vec.Into_iter.t_IntoIter Alloc.String.t_String
                                    Alloc.Alloc.t_Global) (Alloc.String.t_String -> t_ErrorCode))
                            #FStar.Tactics.Typeclasses.solve
                            #(Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global)
                            (Core.Iter.Traits.Iterator.f_map #(Alloc.Vec.Into_iter.t_IntoIter
                                    Alloc.String.t_String Alloc.Alloc.t_Global)
                                #FStar.Tactics.Typeclasses.solve
                                #t_ErrorCode
                                (Core.Iter.Traits.Collect.f_into_iter #(Alloc.Vec.t_Vec
                                        Alloc.String.t_String Alloc.Alloc.t_Global)
                                    #FStar.Tactics.Typeclasses.solve
                                    errcodes
                                  <:
                                  Alloc.Vec.Into_iter.t_IntoIter Alloc.String.t_String
                                    Alloc.Alloc.t_Global)
                                ErrorCode
                              <:
                              Core.Iter.Adapters.Map.t_Map
                                (Alloc.Vec.Into_iter.t_IntoIter Alloc.String.t_String
                                    Alloc.Alloc.t_Global) (Alloc.String.t_String -> t_ErrorCode))
                          <:
                          Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global)
                        <:
                        (Hax_types.Cli_options.t_BackendName &
                          Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global))
                      <:
                      Core.Result.t_Result
                        (Hax_types.Cli_options.t_BackendName &
                          Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global) Anyhow.t_Error
                    | Core.Result.Result_Err err ->
                      Core.Result.Result_Err err
                      <:
                      Core.Result.t_Result
                        (Hax_types.Cli_options.t_BackendName &
                          Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global) Anyhow.t_Error)
              <:
              Core.Iter.Adapters.Map.t_Map
                (Alloc.Vec.Into_iter.t_IntoIter t_FailEntry Alloc.Alloc.t_Global)
                (t_FailEntry
                    -> Core.Result.t_Result
                        (Hax_types.Cli_options.t_BackendName &
                          Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global) Anyhow.t_Error))
          <:
          Core.Result.t_Result
            (Std.Collections.Hash.Map.t_HashMap Hax_types.Cli_options.t_BackendName
                (Alloc.Vec.t_Vec t_ErrorCode Alloc.Alloc.t_Global)
                Std.Hash.Random.t_RandomState) Anyhow.t_Error
        with
        | Core.Result.Result_Ok hoist26 ->
          Core.Result.Result_Ok
          (Directive_Item
            (ItemDirective_Failure ({ f_kind = kind; f_backends = hoist26 }) <: t_ItemDirective)
            <:
            t_Directive)
          <:
          Core.Result.t_Result t_Directive Anyhow.t_Error
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err <: Core.Result.t_Result t_Directive Anyhow.t_Error
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11__from__parser': Core.Fmt.t_Debug t_Directive__from__parser

unfold
let impl_11__from__parser = impl_11__from__parser'

let impl_12__from__parser: Core.Clone.t_Clone t_Directive__from__parser =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13__from__parser': Core.Marker.t_StructuralPartialEq t_Directive__from__parser

unfold
let impl_13__from__parser = impl_13__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14__from__parser': Core.Cmp.t_PartialEq t_Directive__from__parser t_Directive__from__parser

unfold
let impl_14__from__parser = impl_14__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15__from__parser': Core.Cmp.t_Eq t_Directive__from__parser

unfold
let impl_15__from__parser = impl_15__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16__from__parser': Core.Fmt.t_Debug t_FailEntry

unfold
let impl_16__from__parser = impl_16__from__parser'

let impl_17__from__parser: Core.Clone.t_Clone t_FailEntry =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18__from__parser': Core.Marker.t_StructuralPartialEq t_FailEntry

unfold
let impl_18__from__parser = impl_18__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19__from__parser': Core.Cmp.t_PartialEq t_FailEntry t_FailEntry

unfold
let impl_19__from__parser = impl_19__from__parser'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_20__from__parser': Core.Cmp.t_Eq t_FailEntry

unfold
let impl_20__from__parser = impl_20__from__parser'

let extract_line_text (pairs: Pest.Iterators.Pairs.t_Pairs t_Rule) : Alloc.String.t_String =
  let s:Alloc.String.t_String = Alloc.String.impl_String__new () in
  let s:Alloc.String.t_String =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Pest.Iterators.Pairs.t_Pairs
            t_Rule)
          #FStar.Tactics.Typeclasses.solve
          pairs
        <:
        Pest.Iterators.Pairs.t_Pairs t_Rule)
      s
      (fun s p ->
          let s:Alloc.String.t_String = s in
          let p:Pest.Iterators.Pair.t_Pair t_Rule = p in
          if
            (Pest.Iterators.Pair.impl__as_rule #t_Rule p <: t_Rule) =. (Rule_line_text <: t_Rule)
            <:
            bool
          then
            let s:Alloc.String.t_String =
              Alloc.String.f_to_string #string
                #FStar.Tactics.Typeclasses.solve
                (Core.Str.impl_str__trim (Pest.Iterators.Pair.impl__as_str #t_Rule p <: string)
                  <:
                  string)
            in
            s
          else s)
  in
  s

let parse_backend_fail (pair: Pest.Iterators.Pair.t_Pair t_Rule)
    : Core.Result.t_Result t_FailEntry Anyhow.t_Error =
  let backend:Core.Option.t_Option Alloc.String.t_String =
    Core.Option.Option_None <: Core.Option.t_Option Alloc.String.t_String
  in
  let errcodes:Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global =
    Alloc.Vec.impl__new #Alloc.String.t_String ()
  in
  let backend, errcodes:(Core.Option.t_Option Alloc.String.t_String &
    Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Pest.Iterators.Pairs.t_Pairs
            t_Rule)
          #FStar.Tactics.Typeclasses.solve
          (Pest.Iterators.Pair.impl__into_inner #t_Rule pair <: Pest.Iterators.Pairs.t_Pairs t_Rule)
        <:
        Pest.Iterators.Pairs.t_Pairs t_Rule)
      (backend, errcodes
        <:
        (Core.Option.t_Option Alloc.String.t_String &
          Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
      (fun temp_0_ p ->
          let backend, errcodes:(Core.Option.t_Option Alloc.String.t_String &
            Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global) =
            temp_0_
          in
          let p:Pest.Iterators.Pair.t_Pair t_Rule = p in
          match Pest.Iterators.Pair.impl__as_rule #t_Rule p <: t_Rule with
          | Rule_backend  ->
            (Core.Option.Option_Some
              (Alloc.String.f_to_string #string
                  #FStar.Tactics.Typeclasses.solve
                  (Pest.Iterators.Pair.impl__as_str #t_Rule p <: string)
                <:
                Alloc.String.t_String)
              <:
              Core.Option.t_Option Alloc.String.t_String),
            errcodes
            <:
            (Core.Option.t_Option Alloc.String.t_String &
              Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
          | Rule_errcode  ->
            backend,
            (Alloc.Vec.impl_1__push #Alloc.String.t_String
                #Alloc.Alloc.t_Global
                errcodes
                (Alloc.String.f_to_string #string
                    #FStar.Tactics.Typeclasses.solve
                    (Pest.Iterators.Pair.impl__as_str #t_Rule p <: string)
                  <:
                  Alloc.String.t_String)
              <:
              Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
            <:
            (Core.Option.t_Option Alloc.String.t_String &
              Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
          | _ ->
            backend, errcodes
            <:
            (Core.Option.t_Option Alloc.String.t_String &
              Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global))
  in
  match
    Anyhow.f_context #(Core.Option.t_Option Alloc.String.t_String)
      #Alloc.String.t_String
      #Core.Convert.t_Infallible
      #FStar.Tactics.Typeclasses.solve
      #string
      backend
      "backend missing in backend_fail"
    <:
    Core.Result.t_Result Alloc.String.t_String Anyhow.t_Error
  with
  | Core.Result.Result_Ok hoist13 ->
    Core.Result.Result_Ok ({ f_backend = hoist13; f_errcodes = errcodes } <: t_FailEntry)
    <:
    Core.Result.t_Result t_FailEntry Anyhow.t_Error
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_FailEntry Anyhow.t_Error

let convert_directive (pair: Pest.Iterators.Pair.t_Pair t_Rule)
    : Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error =
  let inner:Pest.Iterators.Pairs.t_Pairs t_Rule =
    Pest.Iterators.Pair.impl__into_inner #t_Rule pair
  in
  let tmp0, out:(Pest.Iterators.Pairs.t_Pairs t_Rule &
    Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule)) =
    Core.Iter.Traits.Iterator.f_next #(Pest.Iterators.Pairs.t_Pairs t_Rule)
      #FStar.Tactics.Typeclasses.solve
      inner
  in
  let inner:Pest.Iterators.Pairs.t_Pairs t_Rule = tmp0 in
  match
    Anyhow.f_context #(Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule))
      #(Pest.Iterators.Pair.t_Pair t_Rule)
      #Core.Convert.t_Infallible
      #FStar.Tactics.Typeclasses.solve
      #string
      out
      "empty directive"
    <:
    Core.Result.t_Result (Pest.Iterators.Pair.t_Pair t_Rule) Anyhow.t_Error
  with
  | Core.Result.Result_Ok first ->
    (match Pest.Iterators.Pair.impl__as_rule #t_Rule first <: t_Rule with
      | Rule_cli  ->
        Core.Result.Result_Ok
        (Directive_Cli
          ({
              f_flags
              =
              extract_line_text (Pest.Iterators.Pair.impl__into_inner #t_Rule first
                  <:
                  Pest.Iterators.Pairs.t_Pairs t_Rule)
            })
          <:
          t_Directive__from__parser)
        <:
        Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error
      | Rule_backend_directive  ->
        let i:Pest.Iterators.Pairs.t_Pairs t_Rule =
          Pest.Iterators.Pair.impl__into_inner #t_Rule first
        in
        let tmp0, out:(Pest.Iterators.Pairs.t_Pairs t_Rule &
          Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule)) =
          Core.Iter.Traits.Iterator.f_next #(Pest.Iterators.Pairs.t_Pairs t_Rule)
            #FStar.Tactics.Typeclasses.solve
            i
        in
        let i:Pest.Iterators.Pairs.t_Pairs t_Rule = tmp0 in
        (match
            Anyhow.f_context #(Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule))
              #(Pest.Iterators.Pair.t_Pair t_Rule)
              #Core.Convert.t_Infallible
              #FStar.Tactics.Typeclasses.solve
              #string
              out
              "backend missing"
            <:
            Core.Result.t_Result (Pest.Iterators.Pair.t_Pair t_Rule) Anyhow.t_Error
          with
          | Core.Result.Result_Ok hoist7 ->
            let backend:Alloc.String.t_String =
              Alloc.String.f_to_string #string
                #FStar.Tactics.Typeclasses.solve
                (Pest.Iterators.Pair.impl__as_str #t_Rule hoist7 <: string)
            in
            let value:Alloc.String.t_String = extract_line_text i in
            Core.Result.Result_Ok
            (Directive_Backend ({ f_backend = backend; f_value = value })
              <:
              t_Directive__from__parser)
            <:
            Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
      | Rule_off  ->
        let backends:Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global =
          Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
                (Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                    (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                (Pest.Iterators.Pair.t_Pair t_Rule -> Alloc.String.t_String))
            #FStar.Tactics.Typeclasses.solve
            #(Alloc.Vec.t_Vec Alloc.String.t_String Alloc.Alloc.t_Global)
            (Core.Iter.Traits.Iterator.f_map #(Core.Iter.Adapters.Filter.t_Filter
                    (Pest.Iterators.Pairs.t_Pairs t_Rule)
                    (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                #FStar.Tactics.Typeclasses.solve
                #Alloc.String.t_String
                (Core.Iter.Traits.Iterator.f_filter #(Pest.Iterators.Pairs.t_Pairs t_Rule)
                    #FStar.Tactics.Typeclasses.solve
                    (Pest.Iterators.Pair.impl__into_inner #t_Rule first
                      <:
                      Pest.Iterators.Pairs.t_Pairs t_Rule)
                    (fun p ->
                        let p:Pest.Iterators.Pair.t_Pair t_Rule = p in
                        (Pest.Iterators.Pair.impl__as_rule #t_Rule p <: t_Rule) =.
                        (Rule_backend <: t_Rule)
                        <:
                        bool)
                  <:
                  Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                    (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                (fun p ->
                    let p:Pest.Iterators.Pair.t_Pair t_Rule = p in
                    Alloc.String.f_to_string #string
                      #FStar.Tactics.Typeclasses.solve
                      (Pest.Iterators.Pair.impl__as_str #t_Rule p <: string)
                    <:
                    Alloc.String.t_String)
              <:
              Core.Iter.Adapters.Map.t_Map
                (Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                    (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                (Pest.Iterators.Pair.t_Pair t_Rule -> Alloc.String.t_String))
        in
        Core.Result.Result_Ok
        (Directive_Off ({ f_backends = backends }) <: t_Directive__from__parser)
        <:
        Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error
      | Rule_fail  ->
        let i:Pest.Iterators.Pairs.t_Pairs t_Rule =
          Pest.Iterators.Pair.impl__into_inner #t_Rule first
        in
        let tmp0, out:(Pest.Iterators.Pairs.t_Pairs t_Rule &
          Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule)) =
          Core.Iter.Traits.Iterator.f_next #(Pest.Iterators.Pairs.t_Pairs t_Rule)
            #FStar.Tactics.Typeclasses.solve
            i
        in
        let i:Pest.Iterators.Pairs.t_Pairs t_Rule = tmp0 in
        (match
            Anyhow.f_context #(Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule))
              #(Pest.Iterators.Pair.t_Pair t_Rule)
              #Core.Convert.t_Infallible
              #FStar.Tactics.Typeclasses.solve
              #string
              out
              "fail kind missing"
            <:
            Core.Result.t_Result (Pest.Iterators.Pair.t_Pair t_Rule) Anyhow.t_Error
          with
          | Core.Result.Result_Ok kind_pair ->
            (match Pest.Iterators.Pair.impl__as_str #t_Rule kind_pair <: string with
              | "tc" ->
                let kind:t_FailureKind = FailureKind_Typecheck <: t_FailureKind in
                (match
                    Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
                          (Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          (Pest.Iterators.Pair.t_Pair t_Rule
                              -> Core.Result.t_Result t_FailEntry Anyhow.t_Error))
                      #FStar.Tactics.Typeclasses.solve
                      #(Core.Result.t_Result (Alloc.Vec.t_Vec t_FailEntry Alloc.Alloc.t_Global)
                          Anyhow.t_Error)
                      (Core.Iter.Traits.Iterator.f_map #(Core.Iter.Adapters.Filter.t_Filter
                              (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          #FStar.Tactics.Typeclasses.solve
                          #(Core.Result.t_Result t_FailEntry Anyhow.t_Error)
                          (Core.Iter.Traits.Iterator.f_filter #(Pest.Iterators.Pairs.t_Pairs t_Rule)
                              #FStar.Tactics.Typeclasses.solve
                              i
                              (fun p ->
                                  let p:Pest.Iterators.Pair.t_Pair t_Rule = p in
                                  (Pest.Iterators.Pair.impl__as_rule #t_Rule p <: t_Rule) =.
                                  (Rule_backend_fail <: t_Rule)
                                  <:
                                  bool)
                            <:
                            Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          parse_backend_fail
                        <:
                        Core.Iter.Adapters.Map.t_Map
                          (Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          (Pest.Iterators.Pair.t_Pair t_Rule
                              -> Core.Result.t_Result t_FailEntry Anyhow.t_Error))
                    <:
                    Core.Result.t_Result (Alloc.Vec.t_Vec t_FailEntry Alloc.Alloc.t_Global)
                      Anyhow.t_Error
                  with
                  | Core.Result.Result_Ok entries ->
                    Core.Result.Result_Ok
                    (Directive_Fail ({ f_kind = kind; f_entries = entries })
                      <:
                      t_Directive__from__parser)
                    <:
                    Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
              | "extraction" ->
                let kind:t_FailureKind = FailureKind_Extract <: t_FailureKind in
                (match
                    Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map
                          (Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          (Pest.Iterators.Pair.t_Pair t_Rule
                              -> Core.Result.t_Result t_FailEntry Anyhow.t_Error))
                      #FStar.Tactics.Typeclasses.solve
                      #(Core.Result.t_Result (Alloc.Vec.t_Vec t_FailEntry Alloc.Alloc.t_Global)
                          Anyhow.t_Error)
                      (Core.Iter.Traits.Iterator.f_map #(Core.Iter.Adapters.Filter.t_Filter
                              (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          #FStar.Tactics.Typeclasses.solve
                          #(Core.Result.t_Result t_FailEntry Anyhow.t_Error)
                          (Core.Iter.Traits.Iterator.f_filter #(Pest.Iterators.Pairs.t_Pairs t_Rule)
                              #FStar.Tactics.Typeclasses.solve
                              i
                              (fun p ->
                                  let p:Pest.Iterators.Pair.t_Pair t_Rule = p in
                                  (Pest.Iterators.Pair.impl__as_rule #t_Rule p <: t_Rule) =.
                                  (Rule_backend_fail <: t_Rule)
                                  <:
                                  bool)
                            <:
                            Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          parse_backend_fail
                        <:
                        Core.Iter.Adapters.Map.t_Map
                          (Core.Iter.Adapters.Filter.t_Filter (Pest.Iterators.Pairs.t_Pairs t_Rule)
                              (Pest.Iterators.Pair.t_Pair t_Rule -> bool))
                          (Pest.Iterators.Pair.t_Pair t_Rule
                              -> Core.Result.t_Result t_FailEntry Anyhow.t_Error))
                    <:
                    Core.Result.t_Result (Alloc.Vec.t_Vec t_FailEntry Alloc.Alloc.t_Global)
                      Anyhow.t_Error
                  with
                  | Core.Result.Result_Ok entries ->
                    Core.Result.Result_Ok
                    (Directive_Fail ({ f_kind = kind; f_entries = entries })
                      <:
                      t_Directive__from__parser)
                    <:
                    Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error
                  | Core.Result.Result_Err err ->
                    Core.Result.Result_Err err
                    <:
                    Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
              | _ ->
                let error:Anyhow.t_Error =
                  Anyhow.__private.format_err (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["unknown fail kind"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                Core.Result.Result_Err error
                <:
                Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
      | _ ->
        let error:Anyhow.t_Error =
          Anyhow.__private.format_err (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                (let list = ["unexpected directive node"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Core.Fmt.t_Arguments)
        in
        Core.Result.Result_Err error
        <:
        Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error

let parse_directive (input: string) : Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error =
  match
    Pest.Parser.f_parse #t_DirectivesParser
      #t_Rule
      #FStar.Tactics.Typeclasses.solve
      (Rule_directive <: t_Rule)
      input
    <:
    Core.Result.t_Result (Pest.Iterators.Pairs.t_Pairs t_Rule) (Pest.Error.t_Error t_Rule)
  with
  | Core.Result.Result_Ok pairs ->
    let tmp0, out:(Pest.Iterators.Pairs.t_Pairs t_Rule &
      Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule)) =
      Core.Iter.Traits.Iterator.f_next #(Pest.Iterators.Pairs.t_Pairs t_Rule)
        #FStar.Tactics.Typeclasses.solve
        pairs
    in
    let pairs:Pest.Iterators.Pairs.t_Pairs t_Rule = tmp0 in
    (match
        Anyhow.f_context #(Core.Option.t_Option (Pest.Iterators.Pair.t_Pair t_Rule))
          #(Pest.Iterators.Pair.t_Pair t_Rule)
          #Core.Convert.t_Infallible
          #FStar.Tactics.Typeclasses.solve
          #string
          out
          "directive parse produced no pairs"
        <:
        Core.Result.t_Result (Pest.Iterators.Pair.t_Pair t_Rule) Anyhow.t_Error
      with
      | Core.Result.Result_Ok directive_pair -> convert_directive directive_pair
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error)
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err
    (Core.Convert.f_from #Anyhow.t_Error
        #(Pest.Error.t_Error t_Rule)
        #FStar.Tactics.Typeclasses.solve
        err)
    <:
    Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Str.Traits.t_FromStr t_Directive =
  {
    f_Err = Anyhow.t_Error;
    f_from_str_pre = (fun (s: string) -> true);
    f_from_str_post
    =
    (fun (s: string) (out: Core.Result.t_Result t_Directive Anyhow.t_Error) -> true);
    f_from_str
    =
    fun (s: string) ->
      match parse_directive s <: Core.Result.t_Result t_Directive__from__parser Anyhow.t_Error with
      | Core.Result.Result_Ok hoist29 ->
        (match
            Core.Convert.f_try_from #t_Directive
              #t_Directive__from__parser
              #FStar.Tactics.Typeclasses.solve
              hoist29
            <:
            Core.Result.t_Result t_Directive Anyhow.t_Error
          with
          | Core.Result.Result_Ok hoist31 ->
            Core.Result.Result_Ok hoist31 <: Core.Result.t_Result t_Directive Anyhow.t_Error
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err <: Core.Result.t_Result t_Directive Anyhow.t_Error)
      | Core.Result.Result_Err err ->
        Core.Result.Result_Err err <: Core.Result.t_Result t_Directive Anyhow.t_Error
  }

let directive_of_attribute (attribute: Hax_frontend_exporter.Types.Hir.t_Attribute)
    : Core.Result.t_Result (Core.Option.t_Option t_Directive) Anyhow.t_Error =
  match attribute <: Hax_frontend_exporter.Types.Hir.t_Attribute with
  | Hax_frontend_exporter.Types.Hir.Attribute_Parsed
    (Hax_frontend_exporter.Types.Attributes.AttributeKind_DocComment
        { Hax_frontend_exporter.Types.Attributes.f_comment = comment }) ->
    let comment:string =
      Core.Str.impl_str__trim (Core.Ops.Deref.f_deref #Alloc.String.t_String
            #FStar.Tactics.Typeclasses.solve
            comment
          <:
          string)
    in
    (match Core.Str.impl_str__strip_prefix #string comment "@" <: Core.Option.t_Option string with
      | Core.Option.Option_Some directive ->
        (match
            Core.Str.Traits.f_from_str #t_Directive
              #FStar.Tactics.Typeclasses.solve
              (Core.Str.impl_str__trim directive <: string)
            <:
            Core.Result.t_Result t_Directive Anyhow.t_Error
          with
          | Core.Result.Result_Ok hoist32 ->
            Core.Result.Result_Ok
            (Core.Option.Option_Some hoist32 <: Core.Option.t_Option t_Directive)
            <:
            Core.Result.t_Result (Core.Option.t_Option t_Directive) Anyhow.t_Error
          | Core.Result.Result_Err err ->
            Core.Result.Result_Err err
            <:
            Core.Result.t_Result (Core.Option.t_Option t_Directive) Anyhow.t_Error)
      | _ ->
        Core.Result.Result_Ok (Core.Option.Option_None <: Core.Option.t_Option t_Directive)
        <:
        Core.Result.t_Result (Core.Option.t_Option t_Directive) Anyhow.t_Error)
  | _ ->
    Core.Result.Result_Ok (Core.Option.Option_None <: Core.Option.t_Option t_Directive)
    <:
    Core.Result.t_Result (Core.Option.t_Option t_Directive) Anyhow.t_Error
