module Coverage.Try_error_result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let call (return_error: bool) : Core.Result.t_Result Prims.unit Prims.unit =
  if return_error
  then Core.Result.Result_Err (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit
  else Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit

let test1 (_: Prims.unit) : Core.Result.t_Result Prims.unit Prims.unit =
  let countdown:i32 = mk_i32 10 in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_i32 0)
      (mk_i32 10)
      (fun countdown temp_1_ ->
          let countdown:i32 = countdown in
          let _:i32 = temp_1_ in
          true)
      countdown
      (fun countdown temp_1_ ->
          let countdown:i32 = countdown in
          let _:i32 = temp_1_ in
          let countdown:i32 = countdown -! mk_i32 1 in
          if countdown <. mk_i32 5
          then
            match call true <: Core.Result.t_Result Prims.unit Prims.unit with
            | Core.Result.Result_Ok _ ->
              (match call false <: Core.Result.t_Result Prims.unit Prims.unit with
                | Core.Result.Result_Ok _ ->
                  Core.Ops.Control_flow.ControlFlow_Continue countdown
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (Core.Ops.Control_flow.t_ControlFlow
                        (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32
                | Core.Result.Result_Err err ->
                  Core.Ops.Control_flow.ControlFlow_Break
                  (Core.Ops.Control_flow.ControlFlow_Break
                    (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                    <:
                    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                      (Prims.unit & i32))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (Core.Ops.Control_flow.t_ControlFlow
                        (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32)
            | Core.Result.Result_Err err ->
              Core.Ops.Control_flow.ControlFlow_Break
              (Core.Ops.Control_flow.ControlFlow_Break
                (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                <:
                Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                  (Prims.unit & i32))
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                    (Prims.unit & i32)) i32
          else
            match call false <: Core.Result.t_Result Prims.unit Prims.unit with
            | Core.Result.Result_Ok _ ->
              Core.Ops.Control_flow.ControlFlow_Continue countdown
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                    (Prims.unit & i32)) i32
            | Core.Result.Result_Err err ->
              Core.Ops.Control_flow.ControlFlow_Break
              (Core.Ops.Control_flow.ControlFlow_Break
                (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                <:
                Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                  (Prims.unit & i32))
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                    (Prims.unit & i32)) i32)
    <:
    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit) i32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue countdown ->
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit

type t_Thing1 = | Thing1 : t_Thing1

type t_Thing2 = | Thing2 : t_Thing2

let impl_Thing1__get_thing_2_ (self: t_Thing1) (return_error: bool)
    : Core.Result.t_Result t_Thing2 Prims.unit =
  if return_error
  then Core.Result.Result_Err (() <: Prims.unit) <: Core.Result.t_Result t_Thing2 Prims.unit
  else Core.Result.Result_Ok (Thing2 <: t_Thing2) <: Core.Result.t_Result t_Thing2 Prims.unit

let impl_Thing2__call (self: t_Thing2) (return_error: bool) : Core.Result.t_Result u32 Prims.unit =
  if return_error
  then Core.Result.Result_Err (() <: Prims.unit) <: Core.Result.t_Result u32 Prims.unit
  else Core.Result.Result_Ok (mk_u32 57) <: Core.Result.t_Result u32 Prims.unit

let test2 (_: Prims.unit) : Core.Result.t_Result Prims.unit Prims.unit =
  let thing1:t_Thing1 = Thing1 <: t_Thing1 in
  let countdown:i32 = mk_i32 10 in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_i32 0)
      (mk_i32 10)
      (fun countdown temp_1_ ->
          let countdown:i32 = countdown in
          let _:i32 = temp_1_ in
          true)
      countdown
      (fun countdown temp_1_ ->
          let countdown:i32 = countdown in
          let _:i32 = temp_1_ in
          let countdown:i32 = countdown -! mk_i32 1 in
          if countdown <. mk_i32 5
          then
            match
              impl_Thing1__get_thing_2_ thing1 false <: Core.Result.t_Result t_Thing2 Prims.unit
            with
            | Core.Result.Result_Ok hoist1 ->
              let _:Prims.unit =
                Core.Result.impl__expect_err #u32
                  #Prims.unit
                  (impl_Thing2__call hoist1 true <: Core.Result.t_Result u32 Prims.unit)
                  "call should fail"
              in
              (match
                  impl_Thing1__get_thing_2_ thing1 false <: Core.Result.t_Result t_Thing2 Prims.unit
                with
                | Core.Result.Result_Ok hoist3 ->
                  let _:Prims.unit =
                    Core.Result.impl__expect_err #u32
                      #Prims.unit
                      (impl_Thing2__call hoist3 true <: Core.Result.t_Result u32 Prims.unit)
                      "call should fail"
                  in
                  (match
                      impl_Thing1__get_thing_2_ thing1 true
                      <:
                      Core.Result.t_Result t_Thing2 Prims.unit
                    with
                    | Core.Result.Result_Ok hoist5 ->
                      (match
                          impl_Thing2__call hoist5 true <: Core.Result.t_Result u32 Prims.unit
                        with
                        | Core.Result.Result_Ok v_val ->
                          let _:Prims.unit =
                            match v_val, mk_u32 57 <: (u32 & u32) with
                            | left_val, right_val ->
                              Hax_lib.v_assert (left_val =. right_val <: bool)
                          in
                          (match
                              impl_Thing1__get_thing_2_ thing1 true
                              <:
                              Core.Result.t_Result t_Thing2 Prims.unit
                            with
                            | Core.Result.Result_Ok hoist7 ->
                              (match
                                  impl_Thing2__call hoist7 false
                                  <:
                                  Core.Result.t_Result u32 Prims.unit
                                with
                                | Core.Result.Result_Ok v_val ->
                                  let _:Prims.unit =
                                    match v_val, mk_u32 57 <: (u32 & u32) with
                                    | left_val, right_val ->
                                      Hax_lib.v_assert (left_val =. right_val <: bool)
                                  in
                                  Core.Ops.Control_flow.ControlFlow_Continue countdown
                                  <:
                                  Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Ops.Control_flow.t_ControlFlow
                                        (Core.Result.t_Result Prims.unit Prims.unit)
                                        (Prims.unit & i32)) i32
                                | Core.Result.Result_Err err ->
                                  Core.Ops.Control_flow.ControlFlow_Break
                                  (Core.Ops.Control_flow.ControlFlow_Break
                                    (Core.Result.Result_Err err
                                      <:
                                      Core.Result.t_Result Prims.unit Prims.unit)
                                    <:
                                    Core.Ops.Control_flow.t_ControlFlow
                                      (Core.Result.t_Result Prims.unit Prims.unit)
                                      (Prims.unit & i32))
                                  <:
                                  Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Ops.Control_flow.t_ControlFlow
                                        (Core.Result.t_Result Prims.unit Prims.unit)
                                        (Prims.unit & i32)) i32)
                            | Core.Result.Result_Err err ->
                              Core.Ops.Control_flow.ControlFlow_Break
                              (Core.Ops.Control_flow.ControlFlow_Break
                                (Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result Prims.unit Prims.unit)
                                <:
                                Core.Ops.Control_flow.t_ControlFlow
                                  (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                              <:
                              Core.Ops.Control_flow.t_ControlFlow
                                (Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                                i32)
                        | Core.Result.Result_Err err ->
                          Core.Ops.Control_flow.ControlFlow_Break
                          (Core.Ops.Control_flow.ControlFlow_Break
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result Prims.unit Prims.unit)
                            <:
                            Core.Ops.Control_flow.t_ControlFlow
                              (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                          <:
                          Core.Ops.Control_flow.t_ControlFlow
                            (Core.Ops.Control_flow.t_ControlFlow
                                (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32
                      )
                    | Core.Result.Result_Err err ->
                      Core.Ops.Control_flow.ControlFlow_Break
                      (Core.Ops.Control_flow.ControlFlow_Break
                        (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (Core.Ops.Control_flow.t_ControlFlow
                            (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32)
                | Core.Result.Result_Err err ->
                  Core.Ops.Control_flow.ControlFlow_Break
                  (Core.Ops.Control_flow.ControlFlow_Break
                    (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                    <:
                    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                      (Prims.unit & i32))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (Core.Ops.Control_flow.t_ControlFlow
                        (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32)
            | Core.Result.Result_Err err ->
              Core.Ops.Control_flow.ControlFlow_Break
              (Core.Ops.Control_flow.ControlFlow_Break
                (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                <:
                Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                  (Prims.unit & i32))
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                    (Prims.unit & i32)) i32
          else
            match
              impl_Thing1__get_thing_2_ thing1 false <: Core.Result.t_Result t_Thing2 Prims.unit
            with
            | Core.Result.Result_Ok hoist9 ->
              (match impl_Thing2__call hoist9 false <: Core.Result.t_Result u32 Prims.unit with
                | Core.Result.Result_Ok v_val ->
                  let _:Prims.unit =
                    match v_val, mk_u32 57 <: (u32 & u32) with
                    | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
                  in
                  (match
                      impl_Thing1__get_thing_2_ thing1 false
                      <:
                      Core.Result.t_Result t_Thing2 Prims.unit
                    with
                    | Core.Result.Result_Ok hoist11 ->
                      (match
                          impl_Thing2__call hoist11 false <: Core.Result.t_Result u32 Prims.unit
                        with
                        | Core.Result.Result_Ok v_val ->
                          let _:Prims.unit =
                            match v_val, mk_u32 57 <: (u32 & u32) with
                            | left_val, right_val ->
                              Hax_lib.v_assert (left_val =. right_val <: bool)
                          in
                          (match
                              impl_Thing1__get_thing_2_ thing1 false
                              <:
                              Core.Result.t_Result t_Thing2 Prims.unit
                            with
                            | Core.Result.Result_Ok hoist13 ->
                              (match
                                  impl_Thing2__call hoist13 false
                                  <:
                                  Core.Result.t_Result u32 Prims.unit
                                with
                                | Core.Result.Result_Ok v_val ->
                                  let _:Prims.unit =
                                    match v_val, mk_u32 57 <: (u32 & u32) with
                                    | left_val, right_val ->
                                      Hax_lib.v_assert (left_val =. right_val <: bool)
                                  in
                                  Core.Ops.Control_flow.ControlFlow_Continue countdown
                                  <:
                                  Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Ops.Control_flow.t_ControlFlow
                                        (Core.Result.t_Result Prims.unit Prims.unit)
                                        (Prims.unit & i32)) i32
                                | Core.Result.Result_Err err ->
                                  Core.Ops.Control_flow.ControlFlow_Break
                                  (Core.Ops.Control_flow.ControlFlow_Break
                                    (Core.Result.Result_Err err
                                      <:
                                      Core.Result.t_Result Prims.unit Prims.unit)
                                    <:
                                    Core.Ops.Control_flow.t_ControlFlow
                                      (Core.Result.t_Result Prims.unit Prims.unit)
                                      (Prims.unit & i32))
                                  <:
                                  Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Ops.Control_flow.t_ControlFlow
                                        (Core.Result.t_Result Prims.unit Prims.unit)
                                        (Prims.unit & i32)) i32)
                            | Core.Result.Result_Err err ->
                              Core.Ops.Control_flow.ControlFlow_Break
                              (Core.Ops.Control_flow.ControlFlow_Break
                                (Core.Result.Result_Err err
                                  <:
                                  Core.Result.t_Result Prims.unit Prims.unit)
                                <:
                                Core.Ops.Control_flow.t_ControlFlow
                                  (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                              <:
                              Core.Ops.Control_flow.t_ControlFlow
                                (Core.Ops.Control_flow.t_ControlFlow
                                    (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                                i32)
                        | Core.Result.Result_Err err ->
                          Core.Ops.Control_flow.ControlFlow_Break
                          (Core.Ops.Control_flow.ControlFlow_Break
                            (Core.Result.Result_Err err
                              <:
                              Core.Result.t_Result Prims.unit Prims.unit)
                            <:
                            Core.Ops.Control_flow.t_ControlFlow
                              (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                          <:
                          Core.Ops.Control_flow.t_ControlFlow
                            (Core.Ops.Control_flow.t_ControlFlow
                                (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32
                      )
                    | Core.Result.Result_Err err ->
                      Core.Ops.Control_flow.ControlFlow_Break
                      (Core.Ops.Control_flow.ControlFlow_Break
                        (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                        <:
                        Core.Ops.Control_flow.t_ControlFlow
                          (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32))
                      <:
                      Core.Ops.Control_flow.t_ControlFlow
                        (Core.Ops.Control_flow.t_ControlFlow
                            (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32)
                | Core.Result.Result_Err err ->
                  Core.Ops.Control_flow.ControlFlow_Break
                  (Core.Ops.Control_flow.ControlFlow_Break
                    (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                    <:
                    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                      (Prims.unit & i32))
                  <:
                  Core.Ops.Control_flow.t_ControlFlow
                    (Core.Ops.Control_flow.t_ControlFlow
                        (Core.Result.t_Result Prims.unit Prims.unit) (Prims.unit & i32)) i32)
            | Core.Result.Result_Err err ->
              Core.Ops.Control_flow.ControlFlow_Break
              (Core.Ops.Control_flow.ControlFlow_Break
                (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
                <:
                Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                  (Prims.unit & i32))
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit)
                    (Prims.unit & i32)) i32)
    <:
    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit Prims.unit) i32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue countdown ->
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit

let main (_: Prims.unit) : Core.Result.t_Result Prims.unit Prims.unit =
  let _:Prims.unit =
    Core.Result.impl__expect_err #Prims.unit
      #Prims.unit
      (test1 () <: Core.Result.t_Result Prims.unit Prims.unit)
      "test1 should fail"
  in
  match test2 () <: Core.Result.t_Result Prims.unit Prims.unit with
  | Core.Result.Result_Ok _ ->
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit
