module Tests.Legacy__loops.Control_flow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// @fail(extraction): ssprove(HAX0001), coq(HAX0001)
/// @fail(extraction): proverif(HAX0008)
let double_sum (_: Prims.unit) : i32 =
  let sum:i32 = mk_i32 0 in
  let sum:i32 =
    Rust_primitives.Hax.Folds.fold_range_cf (mk_i32 1)
      (mk_i32 10)
      (fun sum temp_1_ ->
          let sum:i32 = sum in
          let _:i32 = temp_1_ in
          true)
      sum
      (fun sum i ->
          let sum:i32 = sum in
          let i:i32 = i in
          if i <. mk_i32 0 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break ((), sum <: (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (sum +! i <: i32)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32)
  in
  sum *! mk_i32 2

/// @fail(extraction): ssprove(HAX0001), coq(HAX0001)
/// @fail(extraction): proverif(HAX0008)
let double_sum2 (_: Prims.unit) : i32 =
  let sum:i32 = mk_i32 0 in
  let sum2:i32 = mk_i32 0 in
  let sum, sum2:(i32 & i32) =
    Rust_primitives.Hax.Folds.fold_range_cf (mk_i32 1)
      (mk_i32 10)
      (fun temp_0_ temp_1_ ->
          let sum, sum2:(i32 & i32) = temp_0_ in
          let _:i32 = temp_1_ in
          true)
      (sum, sum2 <: (i32 & i32))
      (fun temp_0_ i ->
          let sum, sum2:(i32 & i32) = temp_0_ in
          let i:i32 = i in
          if i <. mk_i32 0 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            ((), (sum, sum2 <: (i32 & i32)) <: (Prims.unit & (i32 & i32)))
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & (i32 & i32)) (i32 & i32)
          else
            let sum:i32 = sum +! i in
            Core.Ops.Control_flow.ControlFlow_Continue (sum, sum2 +! i <: (i32 & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & (i32 & i32)) (i32 & i32))
  in
  sum +! sum2

/// @fail(extraction): proverif(HAX0008)
let double_sum_return (v: t_Slice i32) : i32 =
  let sum:i32 = mk_i32 0 in
  match
    Rust_primitives.Hax.Folds.fold_return (Core.Iter.Traits.Collect.f_into_iter #(t_Slice i32)
          #FStar.Tactics.Typeclasses.solve
          v
        <:
        Core.Slice.Iter.t_Iter i32)
      sum
      (fun sum i ->
          let sum:i32 = sum in
          let i:i32 = i in
          if i <. mk_i32 0 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break (mk_i32 0)
              <:
              Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32)) i32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (sum +! i <: i32)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32)) i32)
    <:
    Core.Ops.Control_flow.t_ControlFlow i32 i32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue sum -> sum *! mk_i32 2

/// @fail(extraction): proverif(HAX0008)
let double_sum2_return (v: t_Slice i32) : i32 =
  let sum:i32 = mk_i32 0 in
  let sum2:i32 = mk_i32 0 in
  match
    Rust_primitives.Hax.Folds.fold_return (Core.Iter.Traits.Collect.f_into_iter #(t_Slice i32)
          #FStar.Tactics.Typeclasses.solve
          v
        <:
        Core.Slice.Iter.t_Iter i32)
      (sum, sum2 <: (i32 & i32))
      (fun temp_0_ i ->
          let sum, sum2:(i32 & i32) = temp_0_ in
          let i:i32 = i in
          if i <. mk_i32 0 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break (mk_i32 0)
              <:
              Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & (i32 & i32)))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & (i32 & i32))) (i32 & i32)
          else
            let sum:i32 = sum +! i in
            Core.Ops.Control_flow.ControlFlow_Continue (sum, sum2 +! i <: (i32 & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & (i32 & i32))) (i32 & i32))
    <:
    Core.Ops.Control_flow.t_ControlFlow i32 (i32 & i32)
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue (sum, sum2) -> sum +! sum2

/// @fail(extraction): ssprove(HAX0001, HAX0001), coq(HAX0001, HAX0001, HAX0001)
/// @fail(extraction): proverif(HAX0008)
let bigger_power_2_ (x: i32) : i32 =
  let pow:i32 = mk_i32 1 in
  Rust_primitives.Hax.while_loop_cf (fun pow ->
        let pow:i32 = pow in
        pow <. mk_i32 1000000 <: bool)
    (fun pow ->
        let pow:i32 = pow in
        true)
    (fun pow ->
        let pow:i32 = pow in
        Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
    pow
    (fun pow ->
        let pow:i32 = pow in
        let pow:i32 = pow *! mk_i32 2 in
        if pow <. x
        then
          let pow:i32 = pow *! mk_i32 3 in
          if true
          then
            Core.Ops.Control_flow.ControlFlow_Break ((), pow <: (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (pow *! mk_i32 2)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
        else
          Core.Ops.Control_flow.ControlFlow_Continue (pow *! mk_i32 2)
          <:
          Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32)

type t_M = { f_m:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global }

let impl_M__decoded_message (self: t_M)
    : Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_usize 0)
      (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global self.f_m <: usize)
      (fun temp_0_ temp_1_ ->
          let _:Prims.unit = temp_0_ in
          let _:usize = temp_1_ in
          true)
      ()
      (fun temp_0_ i ->
          let _:Prims.unit = temp_0_ in
          let i:usize = i in
          if i >. mk_usize 5 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break
              (Core.Option.Option_None
                <:
                Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
              <:
              Core.Ops.Control_flow.t_ControlFlow
                (Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                (Prims.unit & Prims.unit))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow
                  (Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                  (Prims.unit & Prims.unit)) Prims.unit
          else
            Core.Ops.Control_flow.ControlFlow_Continue ()
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow
                  (Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
                  (Prims.unit & Prims.unit)) Prims.unit)
    <:
    Core.Ops.Control_flow.t_ControlFlow
      (Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)) Prims.unit
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue _ ->
    Core.Option.Option_Some
    (Core.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        self.f_m)
    <:
    Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

/// @fail(extraction): coq(HAX0001), ssprove(HAX0001)
/// @fail(extraction): proverif(HAX0008)
let nested (_: Prims.unit) : i32 =
  let sum:i32 = mk_i32 0 in
  let sum:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 1)
      (mk_i32 10)
      (fun sum temp_1_ ->
          let sum:i32 = sum in
          let _:i32 = temp_1_ in
          true)
      sum
      (fun sum i ->
          let sum:i32 = sum in
          let i:i32 = i in
          let sum:i32 =
            Rust_primitives.Hax.Folds.fold_range_cf (mk_i32 1)
              (mk_i32 10)
              (fun sum temp_1_ ->
                  let sum:i32 = sum in
                  let _:i32 = temp_1_ in
                  true)
              sum
              (fun sum j ->
                  let sum:i32 = sum in
                  let j:i32 = j in
                  if j <. mk_i32 0 <: bool
                  then
                    Core.Ops.Control_flow.ControlFlow_Break ((), sum <: (Prims.unit & i32))
                    <:
                    Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
                  else
                    Core.Ops.Control_flow.ControlFlow_Continue (sum +! j <: i32)
                    <:
                    Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32)
          in
          sum +! i)
  in
  sum *! mk_i32 2

/// @fail(extraction): proverif(HAX0008)
let nested_return (_: Prims.unit) : i32 =
  let sum:i32 = mk_i32 0 in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_i32 1)
      (mk_i32 10)
      (fun sum temp_1_ ->
          let sum:i32 = sum in
          let _:i32 = temp_1_ in
          true)
      sum
      (fun sum i ->
          let sum:i32 = sum in
          let i:i32 = i in
          match
            Rust_primitives.Hax.Folds.fold_range_return (mk_i32 1)
              (mk_i32 10)
              (fun sum temp_1_ ->
                  let sum:i32 = sum in
                  let _:i32 = temp_1_ in
                  true)
              sum
              (fun sum j ->
                  let sum:i32 = sum in
                  let j:i32 = j in
                  if j <. mk_i32 0 <: bool
                  then
                    Core.Ops.Control_flow.ControlFlow_Break
                    (Core.Ops.Control_flow.ControlFlow_Break (mk_i32 0)
                      <:
                      Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32))
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32)) i32
                  else
                    Core.Ops.Control_flow.ControlFlow_Continue (sum +! j <: i32)
                    <:
                    Core.Ops.Control_flow.t_ControlFlow
                      (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32)) i32)
            <:
            Core.Ops.Control_flow.t_ControlFlow i32 i32
          with
          | Core.Ops.Control_flow.ControlFlow_Break ret ->
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break ret
              <:
              Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32)) i32
          | Core.Ops.Control_flow.ControlFlow_Continue sum ->
            Core.Ops.Control_flow.ControlFlow_Continue (sum +! i <: i32)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow i32 (Prims.unit & i32)) i32)
    <:
    Core.Ops.Control_flow.t_ControlFlow i32 i32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue sum -> sum *! mk_i32 2

/// @fail(extraction): ssprove(HAX0008), coq(HAX0008)
/// @fail(extraction): proverif(HAX0008, HAX0008)
let continue_only (x: t_Slice i32) : (i32 & Prims.unit) =
  let product:i32 = mk_i32 1 in
  Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(t_Slice i32)
        #FStar.Tactics.Typeclasses.solve
        x
      <:
      Core.Slice.Iter.t_Iter i32)
    product
    (fun product i ->
        let product:i32 = product in
        let i:i32 = i in
        if i =. mk_i32 0 <: bool
        then product
        else Core.Ops.Arith.f_mul_assign #i32 #i32 #FStar.Tactics.Typeclasses.solve product i <: i32
    ),
  ()
  <:
  (i32 & Prims.unit)

/// @fail(extraction): coq(HAX0001, HAX0008), ssprove(HAX0008, HAX0001)
/// @fail(extraction): proverif(HAX0008, HAX0008)
let continue_and_break (x: t_Slice i32) : (i32 & Prims.unit) =
  let product:i32 = mk_i32 1 in
  Rust_primitives.Hax.Folds.fold_cf (Core.Iter.Traits.Collect.f_into_iter #(t_Slice i32)
        #FStar.Tactics.Typeclasses.solve
        x
      <:
      Core.Slice.Iter.t_Iter i32)
    product
    (fun product i ->
        let product:i32 = product in
        let i:i32 = i in
        if i =. mk_i32 0 <: bool
        then
          Core.Ops.Control_flow.ControlFlow_Continue product
          <:
          Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
        else
          if i <. mk_i32 0 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break ((), product <: (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
          else
            Core.Ops.Control_flow.ControlFlow_Continue
            (Core.Ops.Arith.f_mul_assign #i32 #i32 #FStar.Tactics.Typeclasses.solve product i <: i32
            )
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32),
  ()
  <:
  (i32 & Prims.unit)
