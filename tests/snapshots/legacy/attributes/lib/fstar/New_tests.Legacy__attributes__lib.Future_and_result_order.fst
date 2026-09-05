module New_tests.Legacy__attributes__lib.Future_and_result_order
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

/// One `&mut` input, non-unit result: `(u32, bool)` in the engine lanes,
/// `(bool, u32)` in the aeneas/Lean lane.
let one_mut_and_result (x: u32)
    : Prims.Pure (u32 & bool)
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let (x_future: u32), (result: bool) = temp_0_ in
          x_future =. (Core_models.Num.impl_u32__wrapping_add x (mk_u32 1) <: u32) &&
          result =. (x_future =. mk_u32 0 <: bool)) =
  let x:u32 = Core_models.Num.impl_u32__wrapping_add x (mk_u32 1) in
  let hax_temp_output:bool = x =. mk_u32 0 in
  x, hax_temp_output <: (u32 & bool)

/// Two `&mut` inputs: pins the futures\' order relative to each other as
/// well as relative to the result. `(u8, u64, bool)` in the engine lanes,
/// `(bool, u8, u64)` in the aeneas/Lean lane.
let two_mut_and_result (a: u8) (b: u64)
    : Prims.Pure (u8 & u64 & bool)
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let (a_future: u8), (b_future: u64), (result: bool) = temp_0_ in
          a_future =. (Core_models.Num.impl_u8__wrapping_add a (mk_u8 1) <: u8) &&
          b_future =. (Core_models.Num.impl_u64__wrapping_add b (mk_u64 2) <: u64) &&
          result =. (a_future =. mk_u8 0 <: bool)) =
  let a:u8 = Core_models.Num.impl_u8__wrapping_add a (mk_u8 1) in
  let b:u64 = Core_models.Num.impl_u64__wrapping_add b (mk_u64 2) in
  let hax_temp_output:bool = a =. mk_u8 0 in
  a, b, hax_temp_output <: (u8 & u64 & bool)

/// One `&mut` input, unit result: the result binder is dropped altogether,
/// so what is left is futures-only and the reordering is a no-op — both
/// lanes agree here.
let one_mut_no_result (x: u32)
    : Prims.Pure u32
      Prims.l_True
      (ensures
        fun x_future ->
          let x_future:u32 = x_future in
          x_future =. (Core_models.Num.impl_u32__wrapping_add x (mk_u32 1) <: u32)) =
  let x:u32 = Core_models.Num.impl_u32__wrapping_add x (mk_u32 1) in
  x
