module Coverage.Loops_branches
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_DebugTest = | DebugTest : t_DebugTest

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Fmt.t_Debug t_DebugTest =
  {
    f_fmt_pre = (fun (self: t_DebugTest) (f: Core.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_DebugTest)
        (f: Core.Fmt.t_Formatter)
        (out1: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_DebugTest) (f: Core.Fmt.t_Formatter) ->
      if true
      then
        let _:Prims.unit =
          if false
          then
            Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
              "{\n while true {\n Tuple0\n }\n }"
        in
        let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
          Core.Fmt.impl_11__write_fmt f
            (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                (let list = ["cool"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Core.Fmt.t_Arguments)
        in
        let f:Core.Fmt.t_Formatter = tmp0 in
        match out <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error with
        | Core.Result.Result_Ok _ ->
          (match
              Rust_primitives.Hax.Folds.fold_range_return (mk_i32 0)
                (mk_i32 10)
                (fun f temp_1_ ->
                    let f:Core.Fmt.t_Formatter = f in
                    let _:i32 = temp_1_ in
                    true)
                f
                (fun f i ->
                    let f:Core.Fmt.t_Formatter = f in
                    let i:i32 = i in
                    if true
                    then
                      let _:Prims.unit =
                        if false
                        then
                          Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
                            "{\n while true {\n Tuple0\n }\n }"
                      in
                      let tmp0, out:(Core.Fmt.t_Formatter &
                        Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
                        Core.Fmt.impl_11__write_fmt f
                          (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                              (let list = ["cool"] in
                                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                                Rust_primitives.Hax.array_of_list 1 list)
                            <:
                            Core.Fmt.t_Arguments)
                      in
                      let f:Core.Fmt.t_Formatter = tmp0 in
                      match out <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error with
                      | Core.Result.Result_Ok _ ->
                        Core.Ops.Control_flow.ControlFlow_Continue f
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Ops.Control_flow.t_ControlFlow
                              (Core.Fmt.t_Formatter &
                                Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                              (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                      | Core.Result.Result_Err err ->
                        Core.Ops.Control_flow.ControlFlow_Break
                        (Core.Ops.Control_flow.ControlFlow_Break
                          (f,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                            <:
                            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error
                            ))
                          <:
                          Core.Ops.Control_flow.t_ControlFlow
                            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error
                            ) (Prims.unit & Core.Fmt.t_Formatter))
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Ops.Control_flow.t_ControlFlow
                              (Core.Fmt.t_Formatter &
                                Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                              (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                    else
                      Core.Ops.Control_flow.ControlFlow_Continue f
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (Core.Ops.Control_flow.t_ControlFlow
                            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error
                            ) (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                Core.Fmt.t_Formatter
            with
            | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
            | Core.Ops.Control_flow.ControlFlow_Continue f ->
              let hax_temp_output:Core.Result.t_Result Prims.unit Core.Fmt.t_Error =
                Core.Result.Result_Ok (() <: Prims.unit)
                <:
                Core.Result.t_Result Prims.unit Core.Fmt.t_Error
              in
              f, hax_temp_output
              <:
              (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        | Core.Result.Result_Err err ->
          f, (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
          <:
          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
      else
        match
          Rust_primitives.Hax.Folds.fold_range_return (mk_i32 0)
            (mk_i32 10)
            (fun f temp_1_ ->
                let f:Core.Fmt.t_Formatter = f in
                let _:i32 = temp_1_ in
                true)
            f
            (fun f i ->
                let f:Core.Fmt.t_Formatter = f in
                let i:i32 = i in
                if true
                then
                  let _:Prims.unit =
                    if false
                    then
                      Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
                        "{\n while true {\n Tuple0\n }\n }"
                  in
                  let tmp0, out:(Core.Fmt.t_Formatter &
                    Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
                    Core.Fmt.impl_11__write_fmt f
                      (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                          (let list = ["cool"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        Core.Fmt.t_Arguments)
                  in
                  let f:Core.Fmt.t_Formatter = tmp0 in
                  match out <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error with
                  | Core.Result.Result_Ok _ ->
                    Core.Ops.Control_flow.ControlFlow_Continue f
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Ops.Control_flow.t_ControlFlow
                          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                          (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                  | Core.Result.Result_Err err ->
                    Core.Ops.Control_flow.ControlFlow_Break
                    (Core.Ops.Control_flow.ControlFlow_Break
                      (f,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                        <:
                        (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                        (Prims.unit & Core.Fmt.t_Formatter))
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Ops.Control_flow.t_ControlFlow
                          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                          (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                else
                  Core.Ops.Control_flow.ControlFlow_Continue f
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (Core.Ops.Control_flow.t_ControlFlow
                        (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                        (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
            Core.Fmt.t_Formatter
        with
        | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
        | Core.Ops.Control_flow.ControlFlow_Continue f ->
          let hax_temp_output:Core.Result.t_Result Prims.unit Core.Fmt.t_Error =
            Core.Result.Result_Ok (() <: Prims.unit)
            <:
            Core.Result.t_Result Prims.unit Core.Fmt.t_Error
          in
          f, hax_temp_output
          <:
          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
  }

type t_DisplayTest = | DisplayTest : t_DisplayTest

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Fmt.t_Display t_DisplayTest =
  {
    f_fmt_pre = (fun (self: t_DisplayTest) (f: Core.Fmt.t_Formatter) -> true);
    f_fmt_post
    =
    (fun
        (self: t_DisplayTest)
        (f: Core.Fmt.t_Formatter)
        (out1: (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        ->
        true);
    f_fmt
    =
    fun (self: t_DisplayTest) (f: Core.Fmt.t_Formatter) ->
      if false
      then
        match
          Rust_primitives.Hax.Folds.fold_range_return (mk_i32 0)
            (mk_i32 10)
            (fun f temp_1_ ->
                let f:Core.Fmt.t_Formatter = f in
                let _:i32 = temp_1_ in
                true)
            f
            (fun f i ->
                let f:Core.Fmt.t_Formatter = f in
                let i:i32 = i in
                if false
                then
                  Core.Ops.Control_flow.ControlFlow_Continue f
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (Core.Ops.Control_flow.t_ControlFlow
                        (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                        (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                else
                  let _:Prims.unit =
                    if false
                    then
                      Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
                        "{\n while true {\n Tuple0\n }\n }"
                  in
                  let tmp0, out:(Core.Fmt.t_Formatter &
                    Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
                    Core.Fmt.impl_11__write_fmt f
                      (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                          (let list = ["cool"] in
                            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                            Rust_primitives.Hax.array_of_list 1 list)
                        <:
                        Core.Fmt.t_Arguments)
                  in
                  let f:Core.Fmt.t_Formatter = tmp0 in
                  match out <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error with
                  | Core.Result.Result_Ok _ ->
                    Core.Ops.Control_flow.ControlFlow_Continue f
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Ops.Control_flow.t_ControlFlow
                          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                          (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                  | Core.Result.Result_Err err ->
                    Core.Ops.Control_flow.ControlFlow_Break
                    (Core.Ops.Control_flow.ControlFlow_Break
                      (f,
                        (Core.Result.Result_Err err
                          <:
                          Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                        <:
                        (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                        (Prims.unit & Core.Fmt.t_Formatter))
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Ops.Control_flow.t_ControlFlow
                          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                          (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter)
          <:
          Core.Ops.Control_flow.t_ControlFlow
            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
            Core.Fmt.t_Formatter
        with
        | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
        | Core.Ops.Control_flow.ControlFlow_Continue f ->
          let hax_temp_output:Core.Result.t_Result Prims.unit Core.Fmt.t_Error =
            Core.Result.Result_Ok (() <: Prims.unit)
            <:
            Core.Result.t_Result Prims.unit Core.Fmt.t_Error
          in
          f, hax_temp_output
          <:
          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
      else
        let _:Prims.unit =
          if false
          then
            Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
              "{\n while true {\n Tuple0\n }\n }"
        in
        let tmp0, out:(Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
          Core.Fmt.impl_11__write_fmt f
            (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                (let list = ["cool"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Core.Fmt.t_Arguments)
        in
        let f:Core.Fmt.t_Formatter = tmp0 in
        match out <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error with
        | Core.Result.Result_Ok _ ->
          (match
              Rust_primitives.Hax.Folds.fold_range_return (mk_i32 0)
                (mk_i32 10)
                (fun f temp_1_ ->
                    let f:Core.Fmt.t_Formatter = f in
                    let _:i32 = temp_1_ in
                    true)
                f
                (fun f i ->
                    let f:Core.Fmt.t_Formatter = f in
                    let i:i32 = i in
                    if false
                    then
                      Core.Ops.Control_flow.ControlFlow_Continue f
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (Core.Ops.Control_flow.t_ControlFlow
                            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error
                            ) (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                    else
                      let _:Prims.unit =
                        if false
                        then
                          Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
                            "{\n while true {\n Tuple0\n }\n }"
                      in
                      let tmp0, out:(Core.Fmt.t_Formatter &
                        Core.Result.t_Result Prims.unit Core.Fmt.t_Error) =
                        Core.Fmt.impl_11__write_fmt f
                          (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                              (let list = ["cool"] in
                                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                                Rust_primitives.Hax.array_of_list 1 list)
                            <:
                            Core.Fmt.t_Arguments)
                      in
                      let f:Core.Fmt.t_Formatter = tmp0 in
                      match out <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error with
                      | Core.Result.Result_Ok _ ->
                        Core.Ops.Control_flow.ControlFlow_Continue f
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Ops.Control_flow.t_ControlFlow
                              (Core.Fmt.t_Formatter &
                                Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                              (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter
                      | Core.Result.Result_Err err ->
                        Core.Ops.Control_flow.ControlFlow_Break
                        (Core.Ops.Control_flow.ControlFlow_Break
                          (f,
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                            <:
                            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error
                            ))
                          <:
                          Core.Ops.Control_flow.t_ControlFlow
                            (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error
                            ) (Prims.unit & Core.Fmt.t_Formatter))
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Ops.Control_flow.t_ControlFlow
                              (Core.Fmt.t_Formatter &
                                Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                              (Prims.unit & Core.Fmt.t_Formatter)) Core.Fmt.t_Formatter)
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
                Core.Fmt.t_Formatter
            with
            | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
            | Core.Ops.Control_flow.ControlFlow_Continue f ->
              let hax_temp_output:Core.Result.t_Result Prims.unit Core.Fmt.t_Error =
                Core.Result.Result_Ok (() <: Prims.unit)
                <:
                Core.Result.t_Result Prims.unit Core.Fmt.t_Error
              in
              f, hax_temp_output
              <:
              (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error))
        | Core.Result.Result_Err err ->
          f, (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
          <:
          (Core.Fmt.t_Formatter & Core.Result.t_Result Prims.unit Core.Fmt.t_Error)
  }

let main (_: Prims.unit) : Prims.unit =
  let debug_test:t_DebugTest = DebugTest <: t_DebugTest in
  let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
    let list = [Core.Fmt.Rt.impl__new_debug #t_DebugTest debug_test] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          args
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  let display_test:t_DisplayTest = DisplayTest <: t_DisplayTest in
  let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
    let list = [Core.Fmt.Rt.impl__new_display #t_DisplayTest display_test] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
    Rust_primitives.Hax.array_of_list 1 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          args
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()
