module Core.Time
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v_NANOS_PER_SEC: u32

val v_NANOS_PER_MILLI: u32

val v_NANOS_PER_MICRO: u32

val v_MILLIS_PER_SEC: u64

val v_MICROS_PER_SEC: u64

val v_SECS_PER_MINUTE: u64

val v_MINS_PER_HOUR: u64

val v_HOURS_PER_DAY: u64

val v_DAYS_PER_WEEK: u64

type t_Duration = {
  f_secs:u64;
  f_nanos:Core.Num.Niche_types.t_Nanoseconds
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_16:Core.Clone.t_Clone t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_17:Core.Marker.t_Copy t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_18:Core.Marker.t_StructuralPartialEq t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_19:Core.Cmp.t_PartialEq t_Duration t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_20:Core.Cmp.t_Eq t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_21:Core.Cmp.t_PartialOrd t_Duration t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_22:Core.Cmp.t_Ord t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_23:Core.Hash.t_Hash t_Duration

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_24:Core.Default.t_Default t_Duration

val impl_Duration__SECOND: t_Duration

val impl_Duration__MILLISECOND: t_Duration

val impl_Duration__MICROSECOND: t_Duration

val impl_Duration__NANOSECOND: t_Duration

val impl_Duration__ZERO: t_Duration

val impl_Duration__MAX: t_Duration

val impl_Duration__new (secs: u64) (nanos: u32)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_secs (secs: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_millis (millis: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_micros (micros: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_nanos (nanos: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_weeks (weeks: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_days (days: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_hours (hours: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_mins (mins: u64)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__is_zero (self: t_Duration) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_secs (self: t_Duration) : Prims.Pure u64 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__subsec_millis (self: t_Duration)
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__subsec_micros (self: t_Duration)
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__subsec_nanos (self: t_Duration)
    : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_millis (self: t_Duration)
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_micros (self: t_Duration)
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_nanos (self: t_Duration)
    : Prims.Pure u128 Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__abs_diff (self other: t_Duration)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__checked_add (self rhs: t_Duration)
    : Prims.Pure (Core.Option.t_Option t_Duration) Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__saturating_add (self rhs: t_Duration)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__checked_sub (self rhs: t_Duration)
    : Prims.Pure (Core.Option.t_Option t_Duration) Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__saturating_sub (self rhs: t_Duration)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__checked_mul (self: t_Duration) (rhs: u32)
    : Prims.Pure (Core.Option.t_Option t_Duration) Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__saturating_mul (self: t_Duration) (rhs: u32)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__checked_div (self: t_Duration) (rhs: u32)
    : Prims.Pure (Core.Option.t_Option t_Duration) Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_secs_f64 (self: t_Duration)
    : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_secs_f32 (self: t_Duration)
    : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_millis_f64 (self: t_Duration)
    : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__as_millis_f32 (self: t_Duration)
    : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_secs_f64 (secs: float)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_secs_f32 (secs: float)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__mul_f64 (self: t_Duration) (rhs: float)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__mul_f32 (self: t_Duration) (rhs: float)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__div_f64 (self: t_Duration) (rhs: float)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__div_f32 (self: t_Duration) (rhs: float)
    : Prims.Pure t_Duration Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__div_duration_f64 (self rhs: t_Duration)
    : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__div_duration_f32 (self rhs: t_Duration)
    : Prims.Pure float Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_nanos__v_NANOS_PER_SEC: u64

val impl_Duration__from_secs_f64__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__from_secs_f32__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__mul_f64__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__mul_f32__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__div_f64__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__div_f32__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_add__impl_1__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Ops.Arith.t_AddAssign t_Duration t_Duration

val f_add_assign__impl_2__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_sub__impl_3__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4:Core.Ops.Arith.t_SubAssign t_Duration t_Duration

val f_sub_assign__impl_4__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_mul__impl_5__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_mul__impl_6__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:Core.Ops.Arith.t_MulAssign t_Duration u32

val f_mul_assign__impl_7__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_div__impl_8__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core.Ops.Arith.t_DivAssign t_Duration u32

val f_div_assign__impl_9__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

(* [@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core.Iter.Traits.Accum.t_Sum t_Duration t_Duration *)

val f_sum__impl_10__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

(* [@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11:Core.Iter.Traits.Accum.t_Sum t_Duration t_Duration *)

val f_sum__impl_11__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12:Core.Fmt.t_Debug t_Duration

val f_fmt__impl_12__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_fmt__impl_14__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

type t_TryFromFloatSecsErrorKind =
  | TryFromFloatSecsErrorKind_Negative : t_TryFromFloatSecsErrorKind
  | TryFromFloatSecsErrorKind_OverflowOrNan : t_TryFromFloatSecsErrorKind

type t_TryFromFloatSecsError = { f_kind:t_TryFromFloatSecsErrorKind }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_25:Core.Fmt.t_Debug t_TryFromFloatSecsError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_26:Core.Clone.t_Clone t_TryFromFloatSecsError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_27:Core.Marker.t_StructuralPartialEq t_TryFromFloatSecsError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_28:Core.Cmp.t_PartialEq t_TryFromFloatSecsError t_TryFromFloatSecsError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_29:Core.Cmp.t_Eq t_TryFromFloatSecsError

val impl_TryFromFloatSecsError__description (self: t_TryFromFloatSecsError)
    : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14:Core.Fmt.t_Display t_TryFromFloatSecsError

val t_TryFromFloatSecsErrorKind_cast_to_repr (x: t_TryFromFloatSecsErrorKind)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_30:Core.Fmt.t_Debug t_TryFromFloatSecsErrorKind

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_31:Core.Clone.t_Clone t_TryFromFloatSecsErrorKind

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_32:Core.Marker.t_StructuralPartialEq t_TryFromFloatSecsErrorKind

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_33:Core.Cmp.t_PartialEq t_TryFromFloatSecsErrorKind t_TryFromFloatSecsErrorKind

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_34:Core.Cmp.t_Eq t_TryFromFloatSecsErrorKind

val impl_Duration__try_from_secs_f32 (secs: float)
    : Prims.Pure (Core.Result.t_Result t_Duration t_TryFromFloatSecsError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_Duration__try_from_secs_f64 (secs: float)
    : Prims.Pure (Core.Result.t_Result t_Duration t_TryFromFloatSecsError)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_Duration__try_from_secs_f32__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_Duration__try_from_secs_f64__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

(* [@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Arith.t_Add t_Duration t_Duration =
  {
    f_Output = t_Duration;
    f_Output_11695847888444666345 = FStar.Tactics.Typeclasses.solve;
    f_add_pre = (fun (self: t_Duration) (rhs: t_Duration) -> true);
    f_add_post = (fun (self: t_Duration) (rhs: t_Duration) (out: t_Duration) -> true);
    f_add = fun (self: t_Duration) (rhs: t_Duration) -> () <: t_Duration
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Sub t_Duration t_Duration =
  {
    f_Output = t_Duration;
    f_Output_9381071510542709353 = FStar.Tactics.Typeclasses.solve;
    f_sub_pre = (fun (self: t_Duration) (rhs: t_Duration) -> true);
    f_sub_post = (fun (self: t_Duration) (rhs: t_Duration) (out: t_Duration) -> true);
    f_sub = fun (self: t_Duration) (rhs: t_Duration) -> () <: t_Duration
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Ops.Arith.t_Mul t_Duration u32 =
  {
    f_Output = t_Duration;
    f_Output_11167888388700478202 = FStar.Tactics.Typeclasses.solve;
    f_mul_pre = (fun (self: t_Duration) (rhs: u32) -> true);
    f_mul_post = (fun (self: t_Duration) (rhs: u32) (out: t_Duration) -> true);
    f_mul = fun (self: t_Duration) (rhs: u32) -> () <: t_Duration
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Ops.Arith.t_Mul u32 t_Duration =
  {
    f_Output = t_Duration;
    f_Output_11167888388700478202 = FStar.Tactics.Typeclasses.solve;
    f_mul_pre = (fun (self: u32) (rhs: t_Duration) -> true);
    f_mul_post = (fun (self: u32) (rhs: t_Duration) (out: t_Duration) -> true);
    f_mul = fun (self: u32) (rhs: t_Duration) -> () <: t_Duration
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Arith.t_Div t_Duration u32 =
  {
    f_Output = t_Duration;
    f_Output_10117503193521621741 = FStar.Tactics.Typeclasses.solve;
    f_div_pre = (fun (self: t_Duration) (rhs: u32) -> true);
    f_div_post = (fun (self: t_Duration) (rhs: u32) (out: t_Duration) -> true);
    f_div = fun (self: t_Duration) (rhs: u32) -> () <: t_Duration
  } *)
