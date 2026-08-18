module Core_models.Num.Nonzero
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::num::NonZero`]
type t_NonZero (v_T: Type0) = | NonZero : v_T -> t_NonZero v_T

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_u8__BITS: u32 = Core_models.Num.impl_u8__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_u8__MIN: t_NonZero u8 = NonZero (mk_u8 1) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_u8__MAX: t_NonZero u8 = NonZero Core_models.Num.impl_u8__MAX <: t_NonZero u8

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_u8__new (n: u8) : Core_models.Option.t_Option (t_NonZero u8) =
  if n =. mk_u8 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u8)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero u8)
    <:
    Core_models.Option.t_Option (t_NonZero u8)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_u8__get (self: t_NonZero u8) : u8 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_u8__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero u8) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_u8__from_str_radix = impl_NonZero_of_u8__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_u8__leading_zeros (self: t_NonZero u8) : u32 =
  Core_models.Num.impl_u8__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_u8__trailing_zeros (self: t_NonZero u8) : u32 =
  Core_models.Num.impl_u8__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u8__lowest_one (self: t_NonZero u8) : u32 =
  Core_models.Num.impl_u8__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_u8__count_ones (self: t_NonZero u8) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u8__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_u8__isolate_highest_one (self: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__isolate_highest_one self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u8__isolate_lowest_one (self: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__isolate_lowest_one self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_u8__rotate_left (self: t_NonZero u8) (n: u32) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__rotate_left self._0 n) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_u8__rotate_right (self: t_NonZero u8) (n: u32) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__rotate_right self._0 n) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_u8__reverse_bits (self: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__reverse_bits self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_u8__swap_bytes (self: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__swap_bytes self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_u8__to_be (self: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__to_be self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_u8__to_le (self: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__to_le self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_u8__from_be (x: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__from_be x._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_u8__from_le (x: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__from_le x._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_u8__checked_mul (self other: t_NonZero u8)
    : Core_models.Option.t_Option (t_NonZero u8) =
  let (result: u8), (overflowed: bool) =
    Core_models.Num.impl_u8__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u8)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u8)
    <:
    Core_models.Option.t_Option (t_NonZero u8)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_u8__saturating_mul (self other: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__saturating_mul self._0 other._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_u8__checked_pow (self: t_NonZero u8) (other: u32)
    : Core_models.Option.t_Option (t_NonZero u8) =
  let (result: u8), (overflowed: bool) = Core_models.Num.impl_u8__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u8)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u8)
    <:
    Core_models.Option.t_Option (t_NonZero u8)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_u8__saturating_pow (self: t_NonZero u8) (other: u32) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__saturating_pow self._0 other) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__highest_one (self: t_NonZero u8) : u32 =
  Core_models.Num.impl_u8__ilog2 self._0

/// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__ilog2 (self: t_NonZero u8) : u32 = Core_models.Num.impl_u8__ilog2 self._0

/// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__bit_width (self: t_NonZero u8) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u8__bit_width self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__checked_add (self: t_NonZero u8) (other: u8)
    : Core_models.Option.t_Option (t_NonZero u8) =
  let (result: u8), (overflowed: bool) = Core_models.Num.impl_u8__overflowing_add self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u8)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u8)
    <:
    Core_models.Option.t_Option (t_NonZero u8)

/// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__saturating_add (self: t_NonZero u8) (other: u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__saturating_add self._0 other) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__checked_next_power_of_two (self: t_NonZero u8)
    : Core_models.Option.t_Option (t_NonZero u8) =
  match
    Core_models.Num.impl_u8__checked_next_power_of_two self._0 <: Core_models.Option.t_Option u8
  with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u8)
    <:
    Core_models.Option.t_Option (t_NonZero u8)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u8)

/// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__midpoint (self rhs: t_NonZero u8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_u8__midpoint self._0 rhs._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__is_power_of_two (self: t_NonZero u8) : bool =
  (Core_models.Num.impl_u8__count_ones self._0 <: u32) <. mk_u32 2

/// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__cast_signed (self: t_NonZero u8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_u8__cast_signed self._0) <: t_NonZero i8

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_u8__new_unchecked (n: u8)
    : Prims.Pure (t_NonZero u8) (requires n <>. mk_u8 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__unchecked_add (self: t_NonZero u8) (other: u8)
    : Prims.Pure (t_NonZero u8)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine other <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u8__unchecked_add self._0 other) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__unchecked_mul (self other: t_NonZero u8)
    : Prims.Pure (t_NonZero u8)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u8__unchecked_mul self._0 other._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
let impl_NonZero_of_u8__div_ceil (self rhs: t_NonZero u8)
    : Prims.Pure (t_NonZero u8) (requires rhs._0 <>. mk_u8 0) (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u8__div_ceil self._0 rhs._0) <: t_NonZero u8

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_u16__BITS: u32 = Core_models.Num.impl_u16__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_u16__MIN: t_NonZero u16 = NonZero (mk_u16 1) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_u16__MAX: t_NonZero u16 = NonZero Core_models.Num.impl_u16__MAX <: t_NonZero u16

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_u16__new (n: u16) : Core_models.Option.t_Option (t_NonZero u16) =
  if n =. mk_u16 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u16)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero u16)
    <:
    Core_models.Option.t_Option (t_NonZero u16)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_u16__get (self: t_NonZero u16) : u16 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_u16__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero u16) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_u16__from_str_radix = impl_NonZero_of_u16__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_u16__leading_zeros (self: t_NonZero u16) : u32 =
  Core_models.Num.impl_u16__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_u16__trailing_zeros (self: t_NonZero u16) : u32 =
  Core_models.Num.impl_u16__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u16__lowest_one (self: t_NonZero u16) : u32 =
  Core_models.Num.impl_u16__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_u16__count_ones (self: t_NonZero u16) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u16__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_u16__isolate_highest_one (self: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__isolate_highest_one self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u16__isolate_lowest_one (self: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__isolate_lowest_one self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_u16__rotate_left (self: t_NonZero u16) (n: u32) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__rotate_left self._0 n) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_u16__rotate_right (self: t_NonZero u16) (n: u32) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__rotate_right self._0 n) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_u16__reverse_bits (self: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__reverse_bits self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_u16__swap_bytes (self: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__swap_bytes self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_u16__to_be (self: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__to_be self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_u16__to_le (self: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__to_le self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_u16__from_be (x: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__from_be x._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_u16__from_le (x: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__from_le x._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_u16__checked_mul (self other: t_NonZero u16)
    : Core_models.Option.t_Option (t_NonZero u16) =
  let (result: u16), (overflowed: bool) =
    Core_models.Num.impl_u16__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u16)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u16)
    <:
    Core_models.Option.t_Option (t_NonZero u16)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_u16__saturating_mul (self other: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__saturating_mul self._0 other._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_u16__checked_pow (self: t_NonZero u16) (other: u32)
    : Core_models.Option.t_Option (t_NonZero u16) =
  let (result: u16), (overflowed: bool) = Core_models.Num.impl_u16__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u16)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u16)
    <:
    Core_models.Option.t_Option (t_NonZero u16)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_u16__saturating_pow (self: t_NonZero u16) (other: u32) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__saturating_pow self._0 other) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__highest_one (self: t_NonZero u16) : u32 =
  Core_models.Num.impl_u16__ilog2 self._0

/// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__ilog2 (self: t_NonZero u16) : u32 = Core_models.Num.impl_u16__ilog2 self._0

/// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__bit_width (self: t_NonZero u16) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u16__bit_width self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__checked_add (self: t_NonZero u16) (other: u16)
    : Core_models.Option.t_Option (t_NonZero u16) =
  let (result: u16), (overflowed: bool) = Core_models.Num.impl_u16__overflowing_add self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u16)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u16)
    <:
    Core_models.Option.t_Option (t_NonZero u16)

/// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__saturating_add (self: t_NonZero u16) (other: u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__saturating_add self._0 other) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__checked_next_power_of_two (self: t_NonZero u16)
    : Core_models.Option.t_Option (t_NonZero u16) =
  match
    Core_models.Num.impl_u16__checked_next_power_of_two self._0 <: Core_models.Option.t_Option u16
  with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u16)
    <:
    Core_models.Option.t_Option (t_NonZero u16)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u16)

/// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__midpoint (self rhs: t_NonZero u16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_u16__midpoint self._0 rhs._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__is_power_of_two (self: t_NonZero u16) : bool =
  (Core_models.Num.impl_u16__count_ones self._0 <: u32) <. mk_u32 2

/// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__cast_signed (self: t_NonZero u16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_u16__cast_signed self._0) <: t_NonZero i16

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_u16__new_unchecked (n: u16)
    : Prims.Pure (t_NonZero u16) (requires n <>. mk_u16 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__unchecked_add (self: t_NonZero u16) (other: u16)
    : Prims.Pure (t_NonZero u16)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine other <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u16__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u16__unchecked_add self._0 other) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__unchecked_mul (self other: t_NonZero u16)
    : Prims.Pure (t_NonZero u16)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u16__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u16__unchecked_mul self._0 other._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
let impl_NonZero_of_u16__div_ceil (self rhs: t_NonZero u16)
    : Prims.Pure (t_NonZero u16) (requires rhs._0 <>. mk_u16 0) (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u16__div_ceil self._0 rhs._0) <: t_NonZero u16

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_u32__BITS: u32 = Core_models.Num.impl_u32__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_u32__MIN: t_NonZero u32 = NonZero (mk_u32 1) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_u32__MAX: t_NonZero u32 = NonZero Core_models.Num.impl_u32__MAX <: t_NonZero u32

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_u32__new (n: u32) : Core_models.Option.t_Option (t_NonZero u32) =
  if n =. mk_u32 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u32)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero u32)
    <:
    Core_models.Option.t_Option (t_NonZero u32)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_u32__get (self: t_NonZero u32) : u32 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_u32__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero u32) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_u32__from_str_radix = impl_NonZero_of_u32__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_u32__leading_zeros (self: t_NonZero u32) : u32 =
  Core_models.Num.impl_u32__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_u32__trailing_zeros (self: t_NonZero u32) : u32 =
  Core_models.Num.impl_u32__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u32__lowest_one (self: t_NonZero u32) : u32 =
  Core_models.Num.impl_u32__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_u32__count_ones (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_u32__isolate_highest_one (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__isolate_highest_one self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u32__isolate_lowest_one (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__isolate_lowest_one self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_u32__rotate_left (self: t_NonZero u32) (n: u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__rotate_left self._0 n) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_u32__rotate_right (self: t_NonZero u32) (n: u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__rotate_right self._0 n) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_u32__reverse_bits (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__reverse_bits self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_u32__swap_bytes (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__swap_bytes self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_u32__to_be (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__to_be self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_u32__to_le (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__to_le self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_u32__from_be (x: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__from_be x._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_u32__from_le (x: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__from_le x._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_u32__checked_mul (self other: t_NonZero u32)
    : Core_models.Option.t_Option (t_NonZero u32) =
  let (result: u32), (overflowed: bool) =
    Core_models.Num.impl_u32__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u32)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u32)
    <:
    Core_models.Option.t_Option (t_NonZero u32)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_u32__saturating_mul (self other: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__saturating_mul self._0 other._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_u32__checked_pow (self: t_NonZero u32) (other: u32)
    : Core_models.Option.t_Option (t_NonZero u32) =
  let (result: u32), (overflowed: bool) = Core_models.Num.impl_u32__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u32)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u32)
    <:
    Core_models.Option.t_Option (t_NonZero u32)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_u32__saturating_pow (self: t_NonZero u32) (other: u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__saturating_pow self._0 other) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__highest_one (self: t_NonZero u32) : u32 =
  Core_models.Num.impl_u32__ilog2 self._0

/// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__ilog2 (self: t_NonZero u32) : u32 = Core_models.Num.impl_u32__ilog2 self._0

/// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__bit_width (self: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__bit_width self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__checked_add (self: t_NonZero u32) (other: u32)
    : Core_models.Option.t_Option (t_NonZero u32) =
  let (result: u32), (overflowed: bool) = Core_models.Num.impl_u32__overflowing_add self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u32)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u32)
    <:
    Core_models.Option.t_Option (t_NonZero u32)

/// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__saturating_add (self: t_NonZero u32) (other: u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__saturating_add self._0 other) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__checked_next_power_of_two (self: t_NonZero u32)
    : Core_models.Option.t_Option (t_NonZero u32) =
  match
    Core_models.Num.impl_u32__checked_next_power_of_two self._0 <: Core_models.Option.t_Option u32
  with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u32)
    <:
    Core_models.Option.t_Option (t_NonZero u32)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u32)

/// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__midpoint (self rhs: t_NonZero u32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u32__midpoint self._0 rhs._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__is_power_of_two (self: t_NonZero u32) : bool =
  (Core_models.Num.impl_u32__count_ones self._0 <: u32) <. mk_u32 2

/// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__cast_signed (self: t_NonZero u32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_u32__cast_signed self._0) <: t_NonZero i32

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_u32__new_unchecked (n: u32)
    : Prims.Pure (t_NonZero u32) (requires n <>. mk_u32 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__unchecked_add (self: t_NonZero u32) (other: u32)
    : Prims.Pure (t_NonZero u32)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine other <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u32__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u32__unchecked_add self._0 other) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__unchecked_mul (self other: t_NonZero u32)
    : Prims.Pure (t_NonZero u32)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u32__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u32__unchecked_mul self._0 other._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
let impl_NonZero_of_u32__div_ceil (self rhs: t_NonZero u32)
    : Prims.Pure (t_NonZero u32) (requires rhs._0 <>. mk_u32 0) (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u32__div_ceil self._0 rhs._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_u64__BITS: u32 = Core_models.Num.impl_u64__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_u64__MIN: t_NonZero u64 = NonZero (mk_u64 1) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_u64__MAX: t_NonZero u64 = NonZero Core_models.Num.impl_u64__MAX <: t_NonZero u64

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_u64__new (n: u64) : Core_models.Option.t_Option (t_NonZero u64) =
  if n =. mk_u64 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u64)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero u64)
    <:
    Core_models.Option.t_Option (t_NonZero u64)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_u64__get (self: t_NonZero u64) : u64 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_u64__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero u64) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_u64__from_str_radix = impl_NonZero_of_u64__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_u64__leading_zeros (self: t_NonZero u64) : u32 =
  Core_models.Num.impl_u64__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_u64__trailing_zeros (self: t_NonZero u64) : u32 =
  Core_models.Num.impl_u64__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u64__lowest_one (self: t_NonZero u64) : u32 =
  Core_models.Num.impl_u64__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_u64__count_ones (self: t_NonZero u64) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u64__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_u64__isolate_highest_one (self: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__isolate_highest_one self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u64__isolate_lowest_one (self: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__isolate_lowest_one self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_u64__rotate_left (self: t_NonZero u64) (n: u32) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__rotate_left self._0 n) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_u64__rotate_right (self: t_NonZero u64) (n: u32) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__rotate_right self._0 n) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_u64__reverse_bits (self: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__reverse_bits self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_u64__swap_bytes (self: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__swap_bytes self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_u64__to_be (self: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__to_be self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_u64__to_le (self: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__to_le self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_u64__from_be (x: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__from_be x._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_u64__from_le (x: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__from_le x._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_u64__checked_mul (self other: t_NonZero u64)
    : Core_models.Option.t_Option (t_NonZero u64) =
  let (result: u64), (overflowed: bool) =
    Core_models.Num.impl_u64__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u64)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u64)
    <:
    Core_models.Option.t_Option (t_NonZero u64)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_u64__saturating_mul (self other: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__saturating_mul self._0 other._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_u64__checked_pow (self: t_NonZero u64) (other: u32)
    : Core_models.Option.t_Option (t_NonZero u64) =
  let (result: u64), (overflowed: bool) = Core_models.Num.impl_u64__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u64)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u64)
    <:
    Core_models.Option.t_Option (t_NonZero u64)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_u64__saturating_pow (self: t_NonZero u64) (other: u32) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__saturating_pow self._0 other) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__highest_one (self: t_NonZero u64) : u32 =
  Core_models.Num.impl_u64__ilog2 self._0

/// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__ilog2 (self: t_NonZero u64) : u32 = Core_models.Num.impl_u64__ilog2 self._0

/// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__bit_width (self: t_NonZero u64) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u64__bit_width self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__checked_add (self: t_NonZero u64) (other: u64)
    : Core_models.Option.t_Option (t_NonZero u64) =
  let (result: u64), (overflowed: bool) = Core_models.Num.impl_u64__overflowing_add self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u64)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u64)
    <:
    Core_models.Option.t_Option (t_NonZero u64)

/// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__saturating_add (self: t_NonZero u64) (other: u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__saturating_add self._0 other) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__checked_next_power_of_two (self: t_NonZero u64)
    : Core_models.Option.t_Option (t_NonZero u64) =
  match
    Core_models.Num.impl_u64__checked_next_power_of_two self._0 <: Core_models.Option.t_Option u64
  with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u64)
    <:
    Core_models.Option.t_Option (t_NonZero u64)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u64)

/// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__midpoint (self rhs: t_NonZero u64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_u64__midpoint self._0 rhs._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__is_power_of_two (self: t_NonZero u64) : bool =
  (Core_models.Num.impl_u64__count_ones self._0 <: u32) <. mk_u32 2

/// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__cast_signed (self: t_NonZero u64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_u64__cast_signed self._0) <: t_NonZero i64

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_u64__new_unchecked (n: u64)
    : Prims.Pure (t_NonZero u64) (requires n <>. mk_u64 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__unchecked_add (self: t_NonZero u64) (other: u64)
    : Prims.Pure (t_NonZero u64)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine other <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u64__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u64__unchecked_add self._0 other) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__unchecked_mul (self other: t_NonZero u64)
    : Prims.Pure (t_NonZero u64)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u64__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u64__unchecked_mul self._0 other._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
let impl_NonZero_of_u64__div_ceil (self rhs: t_NonZero u64)
    : Prims.Pure (t_NonZero u64) (requires rhs._0 <>. mk_u64 0) (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u64__div_ceil self._0 rhs._0) <: t_NonZero u64

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_u128__BITS: u32 = Core_models.Num.impl_u128__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_u128__MIN: t_NonZero u128 = NonZero (mk_u128 1) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_u128__MAX: t_NonZero u128 =
  NonZero Core_models.Num.impl_u128__MAX <: t_NonZero u128

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_u128__new (n: u128) : Core_models.Option.t_Option (t_NonZero u128) =
  if n =. mk_u128 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u128)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero u128)
    <:
    Core_models.Option.t_Option (t_NonZero u128)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_u128__get (self: t_NonZero u128) : u128 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_u128__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero u128) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_u128__from_str_radix = impl_NonZero_of_u128__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_u128__leading_zeros (self: t_NonZero u128) : u32 =
  Core_models.Num.impl_u128__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_u128__trailing_zeros (self: t_NonZero u128) : u32 =
  Core_models.Num.impl_u128__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u128__lowest_one (self: t_NonZero u128) : u32 =
  Core_models.Num.impl_u128__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_u128__count_ones (self: t_NonZero u128) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u128__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_u128__isolate_highest_one (self: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__isolate_highest_one self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_u128__isolate_lowest_one (self: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__isolate_lowest_one self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_u128__rotate_left (self: t_NonZero u128) (n: u32) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__rotate_left self._0 n) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_u128__rotate_right (self: t_NonZero u128) (n: u32) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__rotate_right self._0 n) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_u128__reverse_bits (self: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__reverse_bits self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_u128__swap_bytes (self: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__swap_bytes self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_u128__to_be (self: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__to_be self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_u128__to_le (self: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__to_le self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_u128__from_be (x: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__from_be x._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_u128__from_le (x: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__from_le x._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_u128__checked_mul (self other: t_NonZero u128)
    : Core_models.Option.t_Option (t_NonZero u128) =
  let (result: u128), (overflowed: bool) =
    Core_models.Num.impl_u128__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u128)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u128)
    <:
    Core_models.Option.t_Option (t_NonZero u128)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_u128__saturating_mul (self other: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__saturating_mul self._0 other._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_u128__checked_pow (self: t_NonZero u128) (other: u32)
    : Core_models.Option.t_Option (t_NonZero u128) =
  let (result: u128), (overflowed: bool) =
    Core_models.Num.impl_u128__overflowing_pow self._0 other
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u128)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u128)
    <:
    Core_models.Option.t_Option (t_NonZero u128)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_u128__saturating_pow (self: t_NonZero u128) (other: u32) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__saturating_pow self._0 other) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__highest_one (self: t_NonZero u128) : u32 =
  Core_models.Num.impl_u128__ilog2 self._0

/// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__ilog2 (self: t_NonZero u128) : u32 =
  Core_models.Num.impl_u128__ilog2 self._0

/// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__bit_width (self: t_NonZero u128) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_u128__bit_width self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__checked_add (self: t_NonZero u128) (other: u128)
    : Core_models.Option.t_Option (t_NonZero u128) =
  let (result: u128), (overflowed: bool) =
    Core_models.Num.impl_u128__overflowing_add self._0 other
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u128)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u128)
    <:
    Core_models.Option.t_Option (t_NonZero u128)

/// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__saturating_add (self: t_NonZero u128) (other: u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__saturating_add self._0 other) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__checked_next_power_of_two (self: t_NonZero u128)
    : Core_models.Option.t_Option (t_NonZero u128) =
  match
    Core_models.Num.impl_u128__checked_next_power_of_two self._0 <: Core_models.Option.t_Option u128
  with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero u128)
    <:
    Core_models.Option.t_Option (t_NonZero u128)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero u128)

/// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__midpoint (self rhs: t_NonZero u128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_u128__midpoint self._0 rhs._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__is_power_of_two (self: t_NonZero u128) : bool =
  (Core_models.Num.impl_u128__count_ones self._0 <: u32) <. mk_u32 2

/// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__cast_signed (self: t_NonZero u128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_u128__cast_signed self._0) <: t_NonZero i128

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_u128__new_unchecked (n: u128)
    : Prims.Pure (t_NonZero u128) (requires n <>. mk_u128 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__unchecked_add (self: t_NonZero u128) (other: u128)
    : Prims.Pure (t_NonZero u128)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine other <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u128__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u128__unchecked_add self._0 other) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__unchecked_mul (self other: t_NonZero u128)
    : Prims.Pure (t_NonZero u128)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_u128__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u128__unchecked_mul self._0 other._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
let impl_NonZero_of_u128__div_ceil (self rhs: t_NonZero u128)
    : Prims.Pure (t_NonZero u128) (requires rhs._0 <>. mk_u128 0) (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_u128__div_ceil self._0 rhs._0) <: t_NonZero u128

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_usize__BITS: u32 = Core_models.Num.impl_usize__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_usize__MIN: t_NonZero usize = NonZero (mk_usize 1) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_usize__MAX: t_NonZero usize =
  NonZero Core_models.Num.impl_usize__MAX <: t_NonZero usize

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_usize__new (n: usize) : Core_models.Option.t_Option (t_NonZero usize) =
  if n =. mk_usize 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero usize)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero usize)
    <:
    Core_models.Option.t_Option (t_NonZero usize)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_usize__get (self: t_NonZero usize) : usize = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_usize__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero usize) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_usize__from_str_radix = impl_NonZero_of_usize__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_usize__leading_zeros (self: t_NonZero usize) : u32 =
  Core_models.Num.impl_usize__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_usize__trailing_zeros (self: t_NonZero usize) : u32 =
  Core_models.Num.impl_usize__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_usize__lowest_one (self: t_NonZero usize) : u32 =
  Core_models.Num.impl_usize__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_usize__count_ones (self: t_NonZero usize) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_usize__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_usize__isolate_highest_one (self: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__isolate_highest_one self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_usize__isolate_lowest_one (self: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__isolate_lowest_one self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_usize__rotate_left (self: t_NonZero usize) (n: u32) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__rotate_left self._0 n) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_usize__rotate_right (self: t_NonZero usize) (n: u32) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__rotate_right self._0 n) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_usize__reverse_bits (self: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__reverse_bits self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_usize__swap_bytes (self: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__swap_bytes self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_usize__to_be (self: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__to_be self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_usize__to_le (self: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__to_le self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_usize__from_be (x: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__from_be x._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_usize__from_le (x: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__from_le x._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_usize__checked_mul (self other: t_NonZero usize)
    : Core_models.Option.t_Option (t_NonZero usize) =
  let (result: usize), (overflowed: bool) =
    Core_models.Num.impl_usize__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero usize)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero usize)
    <:
    Core_models.Option.t_Option (t_NonZero usize)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_usize__saturating_mul (self other: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__saturating_mul self._0 other._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_usize__checked_pow (self: t_NonZero usize) (other: u32)
    : Core_models.Option.t_Option (t_NonZero usize) =
  let (result: usize), (overflowed: bool) =
    Core_models.Num.impl_usize__overflowing_pow self._0 other
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero usize)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero usize)
    <:
    Core_models.Option.t_Option (t_NonZero usize)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_usize__saturating_pow (self: t_NonZero usize) (other: u32) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__saturating_pow self._0 other) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::highest_one`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__highest_one (self: t_NonZero usize) : u32 =
  Core_models.Num.impl_usize__ilog2 self._0

/// See [`std::num::NonZero::<u8>::ilog2`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__ilog2 (self: t_NonZero usize) : u32 =
  Core_models.Num.impl_usize__ilog2 self._0

/// See [`std::num::NonZero::<u8>::bit_width`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__bit_width (self: t_NonZero usize) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_usize__bit_width self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::checked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__checked_add (self: t_NonZero usize) (other: usize)
    : Core_models.Option.t_Option (t_NonZero usize) =
  let (result: usize), (overflowed: bool) =
    Core_models.Num.impl_usize__overflowing_add self._0 other
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero usize)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero usize)
    <:
    Core_models.Option.t_Option (t_NonZero usize)

/// See [`std::num::NonZero::<u8>::saturating_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__saturating_add (self: t_NonZero usize) (other: usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__saturating_add self._0 other) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__checked_next_power_of_two (self: t_NonZero usize)
    : Core_models.Option.t_Option (t_NonZero usize) =
  match
    Core_models.Num.impl_usize__checked_next_power_of_two self._0
    <:
    Core_models.Option.t_Option usize
  with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero usize)
    <:
    Core_models.Option.t_Option (t_NonZero usize)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero usize)

/// See [`std::num::NonZero::<u8>::midpoint`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__midpoint (self rhs: t_NonZero usize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_usize__midpoint self._0 rhs._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::is_power_of_two`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__is_power_of_two (self: t_NonZero usize) : bool =
  (Core_models.Num.impl_usize__count_ones self._0 <: u32) <. mk_u32 2

/// See [`std::num::NonZero::<u8>::cast_signed`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__cast_signed (self: t_NonZero usize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_usize__cast_signed self._0) <: t_NonZero isize

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_usize__new_unchecked (n: usize)
    : Prims.Pure (t_NonZero usize) (requires n <>. mk_usize 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::unchecked_add`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__unchecked_add (self: t_NonZero usize) (other: usize)
    : Prims.Pure (t_NonZero usize)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine other <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_usize__unchecked_add self._0 other) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::unchecked_mul`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__unchecked_mul (self other: t_NonZero usize)
    : Prims.Pure (t_NonZero usize)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_usize__unchecked_mul self._0 other._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::div_ceil`] (and similar for other unsigned integer types)
let impl_NonZero_of_usize__div_ceil (self rhs: t_NonZero usize)
    : Prims.Pure (t_NonZero usize) (requires rhs._0 <>. mk_usize 0) (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_usize__div_ceil self._0 rhs._0) <: t_NonZero usize

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_i8__BITS: u32 = Core_models.Num.impl_i8__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_i8__MIN: t_NonZero i8 = NonZero Core_models.Num.impl_i8__MIN <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_i8__MAX: t_NonZero i8 = NonZero Core_models.Num.impl_i8__MAX <: t_NonZero i8

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_i8__new (n: i8) : Core_models.Option.t_Option (t_NonZero i8) =
  if n =. mk_i8 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i8)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero i8)
    <:
    Core_models.Option.t_Option (t_NonZero i8)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_i8__get (self: t_NonZero i8) : i8 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_i8__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero i8) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_i8__from_str_radix = impl_NonZero_of_i8__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_i8__leading_zeros (self: t_NonZero i8) : u32 =
  Core_models.Num.impl_i8__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_i8__trailing_zeros (self: t_NonZero i8) : u32 =
  Core_models.Num.impl_i8__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i8__lowest_one (self: t_NonZero i8) : u32 =
  Core_models.Num.impl_i8__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_i8__count_ones (self: t_NonZero i8) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i8__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_i8__isolate_highest_one (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__isolate_highest_one self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i8__isolate_lowest_one (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__isolate_lowest_one self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_i8__rotate_left (self: t_NonZero i8) (n: u32) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__rotate_left self._0 n) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_i8__rotate_right (self: t_NonZero i8) (n: u32) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__rotate_right self._0 n) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_i8__reverse_bits (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__reverse_bits self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_i8__swap_bytes (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__swap_bytes self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_i8__to_be (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__to_be self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_i8__to_le (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__to_le self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_i8__from_be (x: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__from_be x._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_i8__from_le (x: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__from_le x._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_i8__checked_mul (self other: t_NonZero i8)
    : Core_models.Option.t_Option (t_NonZero i8) =
  let (result: i8), (overflowed: bool) =
    Core_models.Num.impl_i8__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i8)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i8)
    <:
    Core_models.Option.t_Option (t_NonZero i8)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_i8__saturating_mul (self other: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__saturating_mul self._0 other._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_i8__checked_pow (self: t_NonZero i8) (other: u32)
    : Core_models.Option.t_Option (t_NonZero i8) =
  let (result: i8), (overflowed: bool) = Core_models.Num.impl_i8__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i8)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i8)
    <:
    Core_models.Option.t_Option (t_NonZero i8)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_i8__saturating_pow (self: t_NonZero i8) (other: u32) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__saturating_pow self._0 other) <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
assume
val impl_NonZero_of_i8__highest_one': self: t_NonZero i8 -> u32

unfold
let impl_NonZero_of_i8__highest_one = impl_NonZero_of_i8__highest_one'

/// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i8__checked_abs (self: t_NonZero i8)
    : Core_models.Option.t_Option (t_NonZero i8) =
  match Core_models.Num.impl_i8__checked_abs self._0 <: Core_models.Option.t_Option i8 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i8)
    <:
    Core_models.Option.t_Option (t_NonZero i8)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i8)

/// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i8__overflowing_abs (self: t_NonZero i8) : (t_NonZero i8 & bool) =
  let (result: i8), (overflowed: bool) = Core_models.Num.impl_i8__overflowing_abs self._0 in
  (NonZero result <: t_NonZero i8), overflowed <: (t_NonZero i8 & bool)

/// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i8__saturating_abs (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__saturating_abs self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i8__wrapping_abs (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__wrapping_abs self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i8__unsigned_abs (self: t_NonZero i8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_i8__unsigned_abs self._0) <: t_NonZero u8

/// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
let impl_NonZero_of_i8__is_positive (self: t_NonZero i8) : bool =
  Core_models.Num.impl_i8__is_positive self._0

/// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
let impl_NonZero_of_i8__is_negative (self: t_NonZero i8) : bool =
  Core_models.Num.impl_i8__is_negative self._0

/// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i8__checked_neg (self: t_NonZero i8)
    : Core_models.Option.t_Option (t_NonZero i8) =
  match Core_models.Num.impl_i8__checked_neg self._0 <: Core_models.Option.t_Option i8 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i8)
    <:
    Core_models.Option.t_Option (t_NonZero i8)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i8)

/// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i8__overflowing_neg (self: t_NonZero i8) : (t_NonZero i8 & bool) =
  let (result: i8), (overflowed: bool) = Core_models.Num.impl_i8__overflowing_neg self._0 in
  (NonZero result <: t_NonZero i8), overflowed <: (t_NonZero i8 & bool)

/// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i8__saturating_neg (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__saturating_neg self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i8__wrapping_neg (self: t_NonZero i8) : t_NonZero i8 =
  NonZero (Core_models.Num.impl_i8__wrapping_neg self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
let impl_NonZero_of_i8__cast_unsigned (self: t_NonZero i8) : t_NonZero u8 =
  NonZero (Core_models.Num.impl_i8__cast_unsigned self._0) <: t_NonZero u8

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_i8__new_unchecked (n: i8)
    : Prims.Pure (t_NonZero i8) (requires n <>. mk_i8 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
let impl_NonZero_of_i8__unchecked_mul (self other: t_NonZero i8)
    : Prims.Pure (t_NonZero i8)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i8__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i8__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_i8__unchecked_mul self._0 other._0) <: t_NonZero i8

/// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
let impl_NonZero_of_i8__abs (self: t_NonZero i8)
    : Prims.Pure (t_NonZero i8)
      (requires self._0 >. Core_models.Num.impl_i8__MIN)
      (fun _ -> Prims.l_True) = NonZero (Core_models.Num.impl_i8__abs self._0) <: t_NonZero i8

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_i16__BITS: u32 = Core_models.Num.impl_i16__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_i16__MIN: t_NonZero i16 = NonZero Core_models.Num.impl_i16__MIN <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_i16__MAX: t_NonZero i16 = NonZero Core_models.Num.impl_i16__MAX <: t_NonZero i16

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_i16__new (n: i16) : Core_models.Option.t_Option (t_NonZero i16) =
  if n =. mk_i16 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i16)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero i16)
    <:
    Core_models.Option.t_Option (t_NonZero i16)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_i16__get (self: t_NonZero i16) : i16 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_i16__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero i16) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_i16__from_str_radix = impl_NonZero_of_i16__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_i16__leading_zeros (self: t_NonZero i16) : u32 =
  Core_models.Num.impl_i16__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_i16__trailing_zeros (self: t_NonZero i16) : u32 =
  Core_models.Num.impl_i16__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i16__lowest_one (self: t_NonZero i16) : u32 =
  Core_models.Num.impl_i16__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_i16__count_ones (self: t_NonZero i16) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i16__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_i16__isolate_highest_one (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__isolate_highest_one self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i16__isolate_lowest_one (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__isolate_lowest_one self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_i16__rotate_left (self: t_NonZero i16) (n: u32) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__rotate_left self._0 n) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_i16__rotate_right (self: t_NonZero i16) (n: u32) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__rotate_right self._0 n) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_i16__reverse_bits (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__reverse_bits self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_i16__swap_bytes (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__swap_bytes self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_i16__to_be (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__to_be self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_i16__to_le (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__to_le self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_i16__from_be (x: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__from_be x._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_i16__from_le (x: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__from_le x._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_i16__checked_mul (self other: t_NonZero i16)
    : Core_models.Option.t_Option (t_NonZero i16) =
  let (result: i16), (overflowed: bool) =
    Core_models.Num.impl_i16__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i16)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i16)
    <:
    Core_models.Option.t_Option (t_NonZero i16)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_i16__saturating_mul (self other: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__saturating_mul self._0 other._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_i16__checked_pow (self: t_NonZero i16) (other: u32)
    : Core_models.Option.t_Option (t_NonZero i16) =
  let (result: i16), (overflowed: bool) = Core_models.Num.impl_i16__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i16)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i16)
    <:
    Core_models.Option.t_Option (t_NonZero i16)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_i16__saturating_pow (self: t_NonZero i16) (other: u32) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__saturating_pow self._0 other) <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
assume
val impl_NonZero_of_i16__highest_one': self: t_NonZero i16 -> u32

unfold
let impl_NonZero_of_i16__highest_one = impl_NonZero_of_i16__highest_one'

/// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i16__checked_abs (self: t_NonZero i16)
    : Core_models.Option.t_Option (t_NonZero i16) =
  match Core_models.Num.impl_i16__checked_abs self._0 <: Core_models.Option.t_Option i16 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i16)
    <:
    Core_models.Option.t_Option (t_NonZero i16)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i16)

/// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i16__overflowing_abs (self: t_NonZero i16) : (t_NonZero i16 & bool) =
  let (result: i16), (overflowed: bool) = Core_models.Num.impl_i16__overflowing_abs self._0 in
  (NonZero result <: t_NonZero i16), overflowed <: (t_NonZero i16 & bool)

/// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i16__saturating_abs (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__saturating_abs self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i16__wrapping_abs (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__wrapping_abs self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i16__unsigned_abs (self: t_NonZero i16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_i16__unsigned_abs self._0) <: t_NonZero u16

/// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
let impl_NonZero_of_i16__is_positive (self: t_NonZero i16) : bool =
  Core_models.Num.impl_i16__is_positive self._0

/// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
let impl_NonZero_of_i16__is_negative (self: t_NonZero i16) : bool =
  Core_models.Num.impl_i16__is_negative self._0

/// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i16__checked_neg (self: t_NonZero i16)
    : Core_models.Option.t_Option (t_NonZero i16) =
  match Core_models.Num.impl_i16__checked_neg self._0 <: Core_models.Option.t_Option i16 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i16)
    <:
    Core_models.Option.t_Option (t_NonZero i16)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i16)

/// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i16__overflowing_neg (self: t_NonZero i16) : (t_NonZero i16 & bool) =
  let (result: i16), (overflowed: bool) = Core_models.Num.impl_i16__overflowing_neg self._0 in
  (NonZero result <: t_NonZero i16), overflowed <: (t_NonZero i16 & bool)

/// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i16__saturating_neg (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__saturating_neg self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i16__wrapping_neg (self: t_NonZero i16) : t_NonZero i16 =
  NonZero (Core_models.Num.impl_i16__wrapping_neg self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
let impl_NonZero_of_i16__cast_unsigned (self: t_NonZero i16) : t_NonZero u16 =
  NonZero (Core_models.Num.impl_i16__cast_unsigned self._0) <: t_NonZero u16

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_i16__new_unchecked (n: i16)
    : Prims.Pure (t_NonZero i16) (requires n <>. mk_i16 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
let impl_NonZero_of_i16__unchecked_mul (self other: t_NonZero i16)
    : Prims.Pure (t_NonZero i16)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_i16__unchecked_mul self._0 other._0) <: t_NonZero i16

/// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
let impl_NonZero_of_i16__abs (self: t_NonZero i16)
    : Prims.Pure (t_NonZero i16)
      (requires self._0 >. Core_models.Num.impl_i16__MIN)
      (fun _ -> Prims.l_True) = NonZero (Core_models.Num.impl_i16__abs self._0) <: t_NonZero i16

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_i32__BITS: u32 = Core_models.Num.impl_i32__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_i32__MIN: t_NonZero i32 = NonZero Core_models.Num.impl_i32__MIN <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_i32__MAX: t_NonZero i32 = NonZero Core_models.Num.impl_i32__MAX <: t_NonZero i32

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_i32__new (n: i32) : Core_models.Option.t_Option (t_NonZero i32) =
  if n =. mk_i32 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i32)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero i32)
    <:
    Core_models.Option.t_Option (t_NonZero i32)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_i32__get (self: t_NonZero i32) : i32 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_i32__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero i32) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_i32__from_str_radix = impl_NonZero_of_i32__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_i32__leading_zeros (self: t_NonZero i32) : u32 =
  Core_models.Num.impl_i32__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_i32__trailing_zeros (self: t_NonZero i32) : u32 =
  Core_models.Num.impl_i32__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i32__lowest_one (self: t_NonZero i32) : u32 =
  Core_models.Num.impl_i32__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_i32__count_ones (self: t_NonZero i32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i32__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_i32__isolate_highest_one (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__isolate_highest_one self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i32__isolate_lowest_one (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__isolate_lowest_one self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_i32__rotate_left (self: t_NonZero i32) (n: u32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__rotate_left self._0 n) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_i32__rotate_right (self: t_NonZero i32) (n: u32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__rotate_right self._0 n) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_i32__reverse_bits (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__reverse_bits self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_i32__swap_bytes (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__swap_bytes self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_i32__to_be (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__to_be self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_i32__to_le (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__to_le self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_i32__from_be (x: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__from_be x._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_i32__from_le (x: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__from_le x._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_i32__checked_mul (self other: t_NonZero i32)
    : Core_models.Option.t_Option (t_NonZero i32) =
  let (result: i32), (overflowed: bool) =
    Core_models.Num.impl_i32__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i32)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i32)
    <:
    Core_models.Option.t_Option (t_NonZero i32)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_i32__saturating_mul (self other: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__saturating_mul self._0 other._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_i32__checked_pow (self: t_NonZero i32) (other: u32)
    : Core_models.Option.t_Option (t_NonZero i32) =
  let (result: i32), (overflowed: bool) = Core_models.Num.impl_i32__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i32)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i32)
    <:
    Core_models.Option.t_Option (t_NonZero i32)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_i32__saturating_pow (self: t_NonZero i32) (other: u32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__saturating_pow self._0 other) <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
assume
val impl_NonZero_of_i32__highest_one': self: t_NonZero i32 -> u32

unfold
let impl_NonZero_of_i32__highest_one = impl_NonZero_of_i32__highest_one'

/// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i32__checked_abs (self: t_NonZero i32)
    : Core_models.Option.t_Option (t_NonZero i32) =
  match Core_models.Num.impl_i32__checked_abs self._0 <: Core_models.Option.t_Option i32 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i32)
    <:
    Core_models.Option.t_Option (t_NonZero i32)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i32)

/// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i32__overflowing_abs (self: t_NonZero i32) : (t_NonZero i32 & bool) =
  let (result: i32), (overflowed: bool) = Core_models.Num.impl_i32__overflowing_abs self._0 in
  (NonZero result <: t_NonZero i32), overflowed <: (t_NonZero i32 & bool)

/// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i32__saturating_abs (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__saturating_abs self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i32__wrapping_abs (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__wrapping_abs self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i32__unsigned_abs (self: t_NonZero i32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i32__unsigned_abs self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
let impl_NonZero_of_i32__is_positive (self: t_NonZero i32) : bool =
  Core_models.Num.impl_i32__is_positive self._0

/// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
let impl_NonZero_of_i32__is_negative (self: t_NonZero i32) : bool =
  Core_models.Num.impl_i32__is_negative self._0

/// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i32__checked_neg (self: t_NonZero i32)
    : Core_models.Option.t_Option (t_NonZero i32) =
  match Core_models.Num.impl_i32__checked_neg self._0 <: Core_models.Option.t_Option i32 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i32)
    <:
    Core_models.Option.t_Option (t_NonZero i32)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i32)

/// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i32__overflowing_neg (self: t_NonZero i32) : (t_NonZero i32 & bool) =
  let (result: i32), (overflowed: bool) = Core_models.Num.impl_i32__overflowing_neg self._0 in
  (NonZero result <: t_NonZero i32), overflowed <: (t_NonZero i32 & bool)

/// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i32__saturating_neg (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__saturating_neg self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i32__wrapping_neg (self: t_NonZero i32) : t_NonZero i32 =
  NonZero (Core_models.Num.impl_i32__wrapping_neg self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
let impl_NonZero_of_i32__cast_unsigned (self: t_NonZero i32) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i32__cast_unsigned self._0) <: t_NonZero u32

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_i32__new_unchecked (n: i32)
    : Prims.Pure (t_NonZero i32) (requires n <>. mk_i32 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
let impl_NonZero_of_i32__unchecked_mul (self other: t_NonZero i32)
    : Prims.Pure (t_NonZero i32)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i32__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i32__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_i32__unchecked_mul self._0 other._0) <: t_NonZero i32

/// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
let impl_NonZero_of_i32__abs (self: t_NonZero i32)
    : Prims.Pure (t_NonZero i32)
      (requires self._0 >. Core_models.Num.impl_i32__MIN)
      (fun _ -> Prims.l_True) = NonZero (Core_models.Num.impl_i32__abs self._0) <: t_NonZero i32

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_i64__BITS: u32 = Core_models.Num.impl_i64__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_i64__MIN: t_NonZero i64 = NonZero Core_models.Num.impl_i64__MIN <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_i64__MAX: t_NonZero i64 = NonZero Core_models.Num.impl_i64__MAX <: t_NonZero i64

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_i64__new (n: i64) : Core_models.Option.t_Option (t_NonZero i64) =
  if n =. mk_i64 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i64)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero i64)
    <:
    Core_models.Option.t_Option (t_NonZero i64)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_i64__get (self: t_NonZero i64) : i64 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_i64__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero i64) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_i64__from_str_radix = impl_NonZero_of_i64__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_i64__leading_zeros (self: t_NonZero i64) : u32 =
  Core_models.Num.impl_i64__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_i64__trailing_zeros (self: t_NonZero i64) : u32 =
  Core_models.Num.impl_i64__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i64__lowest_one (self: t_NonZero i64) : u32 =
  Core_models.Num.impl_i64__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_i64__count_ones (self: t_NonZero i64) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i64__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_i64__isolate_highest_one (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__isolate_highest_one self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i64__isolate_lowest_one (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__isolate_lowest_one self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_i64__rotate_left (self: t_NonZero i64) (n: u32) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__rotate_left self._0 n) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_i64__rotate_right (self: t_NonZero i64) (n: u32) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__rotate_right self._0 n) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_i64__reverse_bits (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__reverse_bits self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_i64__swap_bytes (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__swap_bytes self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_i64__to_be (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__to_be self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_i64__to_le (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__to_le self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_i64__from_be (x: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__from_be x._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_i64__from_le (x: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__from_le x._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_i64__checked_mul (self other: t_NonZero i64)
    : Core_models.Option.t_Option (t_NonZero i64) =
  let (result: i64), (overflowed: bool) =
    Core_models.Num.impl_i64__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i64)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i64)
    <:
    Core_models.Option.t_Option (t_NonZero i64)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_i64__saturating_mul (self other: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__saturating_mul self._0 other._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_i64__checked_pow (self: t_NonZero i64) (other: u32)
    : Core_models.Option.t_Option (t_NonZero i64) =
  let (result: i64), (overflowed: bool) = Core_models.Num.impl_i64__overflowing_pow self._0 other in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i64)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i64)
    <:
    Core_models.Option.t_Option (t_NonZero i64)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_i64__saturating_pow (self: t_NonZero i64) (other: u32) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__saturating_pow self._0 other) <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
assume
val impl_NonZero_of_i64__highest_one': self: t_NonZero i64 -> u32

unfold
let impl_NonZero_of_i64__highest_one = impl_NonZero_of_i64__highest_one'

/// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i64__checked_abs (self: t_NonZero i64)
    : Core_models.Option.t_Option (t_NonZero i64) =
  match Core_models.Num.impl_i64__checked_abs self._0 <: Core_models.Option.t_Option i64 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i64)
    <:
    Core_models.Option.t_Option (t_NonZero i64)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i64)

/// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i64__overflowing_abs (self: t_NonZero i64) : (t_NonZero i64 & bool) =
  let (result: i64), (overflowed: bool) = Core_models.Num.impl_i64__overflowing_abs self._0 in
  (NonZero result <: t_NonZero i64), overflowed <: (t_NonZero i64 & bool)

/// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i64__saturating_abs (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__saturating_abs self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i64__wrapping_abs (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__wrapping_abs self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i64__unsigned_abs (self: t_NonZero i64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_i64__unsigned_abs self._0) <: t_NonZero u64

/// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
let impl_NonZero_of_i64__is_positive (self: t_NonZero i64) : bool =
  Core_models.Num.impl_i64__is_positive self._0

/// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
let impl_NonZero_of_i64__is_negative (self: t_NonZero i64) : bool =
  Core_models.Num.impl_i64__is_negative self._0

/// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i64__checked_neg (self: t_NonZero i64)
    : Core_models.Option.t_Option (t_NonZero i64) =
  match Core_models.Num.impl_i64__checked_neg self._0 <: Core_models.Option.t_Option i64 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i64)
    <:
    Core_models.Option.t_Option (t_NonZero i64)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i64)

/// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i64__overflowing_neg (self: t_NonZero i64) : (t_NonZero i64 & bool) =
  let (result: i64), (overflowed: bool) = Core_models.Num.impl_i64__overflowing_neg self._0 in
  (NonZero result <: t_NonZero i64), overflowed <: (t_NonZero i64 & bool)

/// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i64__saturating_neg (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__saturating_neg self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i64__wrapping_neg (self: t_NonZero i64) : t_NonZero i64 =
  NonZero (Core_models.Num.impl_i64__wrapping_neg self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
let impl_NonZero_of_i64__cast_unsigned (self: t_NonZero i64) : t_NonZero u64 =
  NonZero (Core_models.Num.impl_i64__cast_unsigned self._0) <: t_NonZero u64

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_i64__new_unchecked (n: i64)
    : Prims.Pure (t_NonZero i64) (requires n <>. mk_i64 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
let impl_NonZero_of_i64__unchecked_mul (self other: t_NonZero i64)
    : Prims.Pure (t_NonZero i64)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i64__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i64__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_i64__unchecked_mul self._0 other._0) <: t_NonZero i64

/// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
let impl_NonZero_of_i64__abs (self: t_NonZero i64)
    : Prims.Pure (t_NonZero i64)
      (requires self._0 >. Core_models.Num.impl_i64__MIN)
      (fun _ -> Prims.l_True) = NonZero (Core_models.Num.impl_i64__abs self._0) <: t_NonZero i64

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_i128__BITS: u32 = Core_models.Num.impl_i128__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_i128__MIN: t_NonZero i128 =
  NonZero Core_models.Num.impl_i128__MIN <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_i128__MAX: t_NonZero i128 =
  NonZero Core_models.Num.impl_i128__MAX <: t_NonZero i128

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_i128__new (n: i128) : Core_models.Option.t_Option (t_NonZero i128) =
  if n =. mk_i128 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i128)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero i128)
    <:
    Core_models.Option.t_Option (t_NonZero i128)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_i128__get (self: t_NonZero i128) : i128 = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_i128__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero i128) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_i128__from_str_radix = impl_NonZero_of_i128__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_i128__leading_zeros (self: t_NonZero i128) : u32 =
  Core_models.Num.impl_i128__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_i128__trailing_zeros (self: t_NonZero i128) : u32 =
  Core_models.Num.impl_i128__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i128__lowest_one (self: t_NonZero i128) : u32 =
  Core_models.Num.impl_i128__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_i128__count_ones (self: t_NonZero i128) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_i128__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_i128__isolate_highest_one (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__isolate_highest_one self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_i128__isolate_lowest_one (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__isolate_lowest_one self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_i128__rotate_left (self: t_NonZero i128) (n: u32) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__rotate_left self._0 n) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_i128__rotate_right (self: t_NonZero i128) (n: u32) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__rotate_right self._0 n) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_i128__reverse_bits (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__reverse_bits self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_i128__swap_bytes (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__swap_bytes self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_i128__to_be (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__to_be self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_i128__to_le (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__to_le self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_i128__from_be (x: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__from_be x._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_i128__from_le (x: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__from_le x._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_i128__checked_mul (self other: t_NonZero i128)
    : Core_models.Option.t_Option (t_NonZero i128) =
  let (result: i128), (overflowed: bool) =
    Core_models.Num.impl_i128__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i128)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i128)
    <:
    Core_models.Option.t_Option (t_NonZero i128)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_i128__saturating_mul (self other: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__saturating_mul self._0 other._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_i128__checked_pow (self: t_NonZero i128) (other: u32)
    : Core_models.Option.t_Option (t_NonZero i128) =
  let (result: i128), (overflowed: bool) =
    Core_models.Num.impl_i128__overflowing_pow self._0 other
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i128)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i128)
    <:
    Core_models.Option.t_Option (t_NonZero i128)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_i128__saturating_pow (self: t_NonZero i128) (other: u32) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__saturating_pow self._0 other) <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
assume
val impl_NonZero_of_i128__highest_one': self: t_NonZero i128 -> u32

unfold
let impl_NonZero_of_i128__highest_one = impl_NonZero_of_i128__highest_one'

/// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i128__checked_abs (self: t_NonZero i128)
    : Core_models.Option.t_Option (t_NonZero i128) =
  match Core_models.Num.impl_i128__checked_abs self._0 <: Core_models.Option.t_Option i128 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i128)
    <:
    Core_models.Option.t_Option (t_NonZero i128)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i128)

/// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i128__overflowing_abs (self: t_NonZero i128) : (t_NonZero i128 & bool) =
  let (result: i128), (overflowed: bool) = Core_models.Num.impl_i128__overflowing_abs self._0 in
  (NonZero result <: t_NonZero i128), overflowed <: (t_NonZero i128 & bool)

/// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i128__saturating_abs (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__saturating_abs self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i128__wrapping_abs (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__wrapping_abs self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
let impl_NonZero_of_i128__unsigned_abs (self: t_NonZero i128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_i128__unsigned_abs self._0) <: t_NonZero u128

/// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
let impl_NonZero_of_i128__is_positive (self: t_NonZero i128) : bool =
  Core_models.Num.impl_i128__is_positive self._0

/// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
let impl_NonZero_of_i128__is_negative (self: t_NonZero i128) : bool =
  Core_models.Num.impl_i128__is_negative self._0

/// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i128__checked_neg (self: t_NonZero i128)
    : Core_models.Option.t_Option (t_NonZero i128) =
  match Core_models.Num.impl_i128__checked_neg self._0 <: Core_models.Option.t_Option i128 with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero i128)
    <:
    Core_models.Option.t_Option (t_NonZero i128)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero i128)

/// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i128__overflowing_neg (self: t_NonZero i128) : (t_NonZero i128 & bool) =
  let (result: i128), (overflowed: bool) = Core_models.Num.impl_i128__overflowing_neg self._0 in
  (NonZero result <: t_NonZero i128), overflowed <: (t_NonZero i128 & bool)

/// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i128__saturating_neg (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__saturating_neg self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
let impl_NonZero_of_i128__wrapping_neg (self: t_NonZero i128) : t_NonZero i128 =
  NonZero (Core_models.Num.impl_i128__wrapping_neg self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
let impl_NonZero_of_i128__cast_unsigned (self: t_NonZero i128) : t_NonZero u128 =
  NonZero (Core_models.Num.impl_i128__cast_unsigned self._0) <: t_NonZero u128

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_i128__new_unchecked (n: i128)
    : Prims.Pure (t_NonZero i128) (requires n <>. mk_i128 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
let impl_NonZero_of_i128__unchecked_mul (self other: t_NonZero i128)
    : Prims.Pure (t_NonZero i128)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i128__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_i128__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_i128__unchecked_mul self._0 other._0) <: t_NonZero i128

/// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
let impl_NonZero_of_i128__abs (self: t_NonZero i128)
    : Prims.Pure (t_NonZero i128)
      (requires self._0 >. Core_models.Num.impl_i128__MIN)
      (fun _ -> Prims.l_True) = NonZero (Core_models.Num.impl_i128__abs self._0) <: t_NonZero i128

/// See [`std::num::NonZero::<u8>::BITS`] (and similar for other integer types)
let impl_NonZero_of_isize__BITS: u32 = Core_models.Num.impl_isize__BITS

/// See [`std::num::NonZero::<u8>::MIN`] (and similar for other integer types)
let impl_NonZero_of_isize__MIN: t_NonZero isize =
  NonZero Core_models.Num.impl_isize__MIN <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::MAX`] (and similar for other integer types)
let impl_NonZero_of_isize__MAX: t_NonZero isize =
  NonZero Core_models.Num.impl_isize__MAX <: t_NonZero isize

/// See [`std::num::NonZero::new`] (and similar for other integer types)
let impl_NonZero_of_isize__new (n: isize) : Core_models.Option.t_Option (t_NonZero isize) =
  if n =. mk_isize 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero isize)
  else
    Core_models.Option.Option_Some (NonZero n <: t_NonZero isize)
    <:
    Core_models.Option.t_Option (t_NonZero isize)

/// See [`std::num::NonZero::get`] (and similar for other integer types)
let impl_NonZero_of_isize__get (self: t_NonZero isize) : isize = self._0

/// See [`std::num::NonZero::<u8>::from_str_radix`] (and similar for other integer types)
assume
val impl_NonZero_of_isize__from_str_radix': src: string -> radix: u32
  -> Core_models.Result.t_Result (t_NonZero isize) Core_models.Num.Error.t_ParseIntError

unfold
let impl_NonZero_of_isize__from_str_radix = impl_NonZero_of_isize__from_str_radix'

/// See [`std::num::NonZero::<u8>::leading_zeros`] (and similar for other integer types)
let impl_NonZero_of_isize__leading_zeros (self: t_NonZero isize) : u32 =
  Core_models.Num.impl_isize__leading_zeros self._0

/// See [`std::num::NonZero::<u8>::trailing_zeros`] (and similar for other integer types)
let impl_NonZero_of_isize__trailing_zeros (self: t_NonZero isize) : u32 =
  Core_models.Num.impl_isize__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::lowest_one`] (and similar for other integer types)
let impl_NonZero_of_isize__lowest_one (self: t_NonZero isize) : u32 =
  Core_models.Num.impl_isize__trailing_zeros self._0

/// See [`std::num::NonZero::<u8>::count_ones`] (and similar for other integer types)
let impl_NonZero_of_isize__count_ones (self: t_NonZero isize) : t_NonZero u32 =
  NonZero (Core_models.Num.impl_isize__count_ones self._0) <: t_NonZero u32

/// See [`std::num::NonZero::<u8>::isolate_highest_one`] (and similar for other integer types)
let impl_NonZero_of_isize__isolate_highest_one (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__isolate_highest_one self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::isolate_lowest_one`] (and similar for other integer types)
let impl_NonZero_of_isize__isolate_lowest_one (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__isolate_lowest_one self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::rotate_left`] (and similar for other integer types)
let impl_NonZero_of_isize__rotate_left (self: t_NonZero isize) (n: u32) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__rotate_left self._0 n) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::rotate_right`] (and similar for other integer types)
let impl_NonZero_of_isize__rotate_right (self: t_NonZero isize) (n: u32) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__rotate_right self._0 n) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::reverse_bits`] (and similar for other integer types)
let impl_NonZero_of_isize__reverse_bits (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__reverse_bits self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::swap_bytes`] (and similar for other integer types)
let impl_NonZero_of_isize__swap_bytes (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__swap_bytes self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::to_be`] (and similar for other integer types)
let impl_NonZero_of_isize__to_be (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__to_be self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::to_le`] (and similar for other integer types)
let impl_NonZero_of_isize__to_le (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__to_le self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::from_be`] (and similar for other integer types)
let impl_NonZero_of_isize__from_be (x: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__from_be x._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::from_le`] (and similar for other integer types)
let impl_NonZero_of_isize__from_le (x: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__from_le x._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::checked_mul`] (and similar for other integer types)
let impl_NonZero_of_isize__checked_mul (self other: t_NonZero isize)
    : Core_models.Option.t_Option (t_NonZero isize) =
  let (result: isize), (overflowed: bool) =
    Core_models.Num.impl_isize__overflowing_mul self._0 other._0
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero isize)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero isize)
    <:
    Core_models.Option.t_Option (t_NonZero isize)

/// See [`std::num::NonZero::<u8>::saturating_mul`] (and similar for other integer types)
let impl_NonZero_of_isize__saturating_mul (self other: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__saturating_mul self._0 other._0) <: t_NonZero isize

/// See [`std::num::NonZero::<u8>::checked_pow`] (and similar for other integer types)
let impl_NonZero_of_isize__checked_pow (self: t_NonZero isize) (other: u32)
    : Core_models.Option.t_Option (t_NonZero isize) =
  let (result: isize), (overflowed: bool) =
    Core_models.Num.impl_isize__overflowing_pow self._0 other
  in
  if overflowed
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero isize)
  else
    Core_models.Option.Option_Some (NonZero result <: t_NonZero isize)
    <:
    Core_models.Option.t_Option (t_NonZero isize)

/// See [`std::num::NonZero::<u8>::saturating_pow`] (and similar for other integer types)
let impl_NonZero_of_isize__saturating_pow (self: t_NonZero isize) (other: u32) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__saturating_pow self._0 other) <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::highest_one`] (and similar for other signed integer types)
assume
val impl_NonZero_of_isize__highest_one': self: t_NonZero isize -> u32

unfold
let impl_NonZero_of_isize__highest_one = impl_NonZero_of_isize__highest_one'

/// See [`std::num::NonZero::<i8>::checked_abs`] (and similar for other signed integer types)
let impl_NonZero_of_isize__checked_abs (self: t_NonZero isize)
    : Core_models.Option.t_Option (t_NonZero isize) =
  match Core_models.Num.impl_isize__checked_abs self._0 <: Core_models.Option.t_Option isize with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero isize)
    <:
    Core_models.Option.t_Option (t_NonZero isize)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero isize)

/// See [`std::num::NonZero::<i8>::overflowing_abs`] (and similar for other signed integer types)
let impl_NonZero_of_isize__overflowing_abs (self: t_NonZero isize) : (t_NonZero isize & bool) =
  let (result: isize), (overflowed: bool) = Core_models.Num.impl_isize__overflowing_abs self._0 in
  (NonZero result <: t_NonZero isize), overflowed <: (t_NonZero isize & bool)

/// See [`std::num::NonZero::<i8>::saturating_abs`] (and similar for other signed integer types)
let impl_NonZero_of_isize__saturating_abs (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__saturating_abs self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::wrapping_abs`] (and similar for other signed integer types)
let impl_NonZero_of_isize__wrapping_abs (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__wrapping_abs self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::unsigned_abs`] (and similar for other signed integer types)
let impl_NonZero_of_isize__unsigned_abs (self: t_NonZero isize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_isize__unsigned_abs self._0) <: t_NonZero usize

/// See [`std::num::NonZero::<i8>::is_positive`] (and similar for other signed integer types)
let impl_NonZero_of_isize__is_positive (self: t_NonZero isize) : bool =
  Core_models.Num.impl_isize__is_positive self._0

/// See [`std::num::NonZero::<i8>::is_negative`] (and similar for other signed integer types)
let impl_NonZero_of_isize__is_negative (self: t_NonZero isize) : bool =
  Core_models.Num.impl_isize__is_negative self._0

/// See [`std::num::NonZero::<i8>::checked_neg`] (and similar for other signed integer types)
let impl_NonZero_of_isize__checked_neg (self: t_NonZero isize)
    : Core_models.Option.t_Option (t_NonZero isize) =
  match Core_models.Num.impl_isize__checked_neg self._0 <: Core_models.Option.t_Option isize with
  | Core_models.Option.Option_Some result ->
    Core_models.Option.Option_Some (NonZero result <: t_NonZero isize)
    <:
    Core_models.Option.t_Option (t_NonZero isize)
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_NonZero isize)

/// See [`std::num::NonZero::<i8>::overflowing_neg`] (and similar for other signed integer types)
let impl_NonZero_of_isize__overflowing_neg (self: t_NonZero isize) : (t_NonZero isize & bool) =
  let (result: isize), (overflowed: bool) = Core_models.Num.impl_isize__overflowing_neg self._0 in
  (NonZero result <: t_NonZero isize), overflowed <: (t_NonZero isize & bool)

/// See [`std::num::NonZero::<i8>::saturating_neg`] (and similar for other signed integer types)
let impl_NonZero_of_isize__saturating_neg (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__saturating_neg self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::wrapping_neg`] (and similar for other signed integer types)
let impl_NonZero_of_isize__wrapping_neg (self: t_NonZero isize) : t_NonZero isize =
  NonZero (Core_models.Num.impl_isize__wrapping_neg self._0) <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::cast_unsigned`] (and similar for other signed integer types)
let impl_NonZero_of_isize__cast_unsigned (self: t_NonZero isize) : t_NonZero usize =
  NonZero (Core_models.Num.impl_isize__cast_unsigned self._0) <: t_NonZero usize

/// See [`std::num::NonZero::new_unchecked`] (and similar for other integer types)
let impl_NonZero_of_isize__new_unchecked (n: isize)
    : Prims.Pure (t_NonZero isize) (requires n <>. mk_isize 0) (fun _ -> Prims.l_True) =
  NonZero n <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::unchecked_mul`] (and similar for other signed integer types)
let impl_NonZero_of_isize__unchecked_mul (self other: t_NonZero isize)
    : Prims.Pure (t_NonZero isize)
      (requires
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_isize__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine self._0 <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine other._0 <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_isize__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  NonZero (Core_models.Num.impl_isize__unchecked_mul self._0 other._0) <: t_NonZero isize

/// See [`std::num::NonZero::<i8>::abs`] (and similar for other signed integer types)
let impl_NonZero_of_isize__abs (self: t_NonZero isize)
    : Prims.Pure (t_NonZero isize)
      (requires self._0 >. Core_models.Num.impl_isize__MIN)
      (fun _ -> Prims.l_True) = NonZero (Core_models.Num.impl_isize__abs self._0) <: t_NonZero isize
