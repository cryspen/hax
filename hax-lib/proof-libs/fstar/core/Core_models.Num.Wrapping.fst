module Core_models.Num.Wrapping
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::num::Wrapping`]
type t_Wrapping (v_T: Type0) = | Wrapping : v_T -> t_Wrapping v_T

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__MIN: t_Wrapping u8 = Wrapping Core_models.Num.impl_u8__MIN <: t_Wrapping u8

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__MAX: t_Wrapping u8 = Wrapping Core_models.Num.impl_u8__MAX <: t_Wrapping u8

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__BITS: u32 = Core_models.Num.impl_u8__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__count_ones (self: t_Wrapping u8) : u32 =
  Core_models.Num.impl_u8__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__count_zeros (self: t_Wrapping u8) : u32 =
  Core_models.Num.impl_u8__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__trailing_zeros (self: t_Wrapping u8) : u32 =
  Core_models.Num.impl_u8__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__leading_zeros (self: t_Wrapping u8) : u32 =
  Core_models.Num.impl_u8__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__rotate_left (self: t_Wrapping u8) (n: u32) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__rotate_left self._0 n) <: t_Wrapping u8

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__rotate_right (self: t_Wrapping u8) (n: u32) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__rotate_right self._0 n) <: t_Wrapping u8

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__swap_bytes (self: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__swap_bytes self._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__to_be (self: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__to_be self._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__to_le (self: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__to_le self._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__from_be (x: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__from_be x._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__from_le (x: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__from_le x._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__reverse_bits (self: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__reverse_bits self._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u8__pow (self: t_Wrapping u8) (exp: u32) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__wrapping_pow self._0 exp) <: t_Wrapping u8

/// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u8__is_power_of_two (self: t_Wrapping u8) : bool =
  Core_models.Num.impl_u8__is_power_of_two self._0

/// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u8__next_power_of_two (self: t_Wrapping u8) : t_Wrapping u8 =
  Wrapping (Core_models.Num.impl_u8__wrapping_next_power_of_two self._0) <: t_Wrapping u8

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__MIN: t_Wrapping u16 =
  Wrapping Core_models.Num.impl_u16__MIN <: t_Wrapping u16

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__MAX: t_Wrapping u16 =
  Wrapping Core_models.Num.impl_u16__MAX <: t_Wrapping u16

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__BITS: u32 = Core_models.Num.impl_u16__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__count_ones (self: t_Wrapping u16) : u32 =
  Core_models.Num.impl_u16__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__count_zeros (self: t_Wrapping u16) : u32 =
  Core_models.Num.impl_u16__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__trailing_zeros (self: t_Wrapping u16) : u32 =
  Core_models.Num.impl_u16__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__leading_zeros (self: t_Wrapping u16) : u32 =
  Core_models.Num.impl_u16__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__rotate_left (self: t_Wrapping u16) (n: u32) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__rotate_left self._0 n) <: t_Wrapping u16

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__rotate_right (self: t_Wrapping u16) (n: u32) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__rotate_right self._0 n) <: t_Wrapping u16

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__swap_bytes (self: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__swap_bytes self._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__to_be (self: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__to_be self._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__to_le (self: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__to_le self._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__from_be (x: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__from_be x._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__from_le (x: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__from_le x._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__reverse_bits (self: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__reverse_bits self._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u16__pow (self: t_Wrapping u16) (exp: u32) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__wrapping_pow self._0 exp) <: t_Wrapping u16

/// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u16__is_power_of_two (self: t_Wrapping u16) : bool =
  Core_models.Num.impl_u16__is_power_of_two self._0

/// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u16__next_power_of_two (self: t_Wrapping u16) : t_Wrapping u16 =
  Wrapping (Core_models.Num.impl_u16__wrapping_next_power_of_two self._0) <: t_Wrapping u16

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__MIN: t_Wrapping u32 =
  Wrapping Core_models.Num.impl_u32__MIN <: t_Wrapping u32

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__MAX: t_Wrapping u32 =
  Wrapping Core_models.Num.impl_u32__MAX <: t_Wrapping u32

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__BITS: u32 = Core_models.Num.impl_u32__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__count_ones (self: t_Wrapping u32) : u32 =
  Core_models.Num.impl_u32__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__count_zeros (self: t_Wrapping u32) : u32 =
  Core_models.Num.impl_u32__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__trailing_zeros (self: t_Wrapping u32) : u32 =
  Core_models.Num.impl_u32__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__leading_zeros (self: t_Wrapping u32) : u32 =
  Core_models.Num.impl_u32__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__rotate_left (self: t_Wrapping u32) (n: u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__rotate_left self._0 n) <: t_Wrapping u32

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__rotate_right (self: t_Wrapping u32) (n: u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__rotate_right self._0 n) <: t_Wrapping u32

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__swap_bytes (self: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__swap_bytes self._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__to_be (self: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__to_be self._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__to_le (self: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__to_le self._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__from_be (x: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__from_be x._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__from_le (x: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__from_le x._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__reverse_bits (self: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__reverse_bits self._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u32__pow (self: t_Wrapping u32) (exp: u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__wrapping_pow self._0 exp) <: t_Wrapping u32

/// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u32__is_power_of_two (self: t_Wrapping u32) : bool =
  Core_models.Num.impl_u32__is_power_of_two self._0

/// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u32__next_power_of_two (self: t_Wrapping u32) : t_Wrapping u32 =
  Wrapping (Core_models.Num.impl_u32__wrapping_next_power_of_two self._0) <: t_Wrapping u32

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__MIN: t_Wrapping u64 =
  Wrapping Core_models.Num.impl_u64__MIN <: t_Wrapping u64

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__MAX: t_Wrapping u64 =
  Wrapping Core_models.Num.impl_u64__MAX <: t_Wrapping u64

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__BITS: u32 = Core_models.Num.impl_u64__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__count_ones (self: t_Wrapping u64) : u32 =
  Core_models.Num.impl_u64__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__count_zeros (self: t_Wrapping u64) : u32 =
  Core_models.Num.impl_u64__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__trailing_zeros (self: t_Wrapping u64) : u32 =
  Core_models.Num.impl_u64__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__leading_zeros (self: t_Wrapping u64) : u32 =
  Core_models.Num.impl_u64__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__rotate_left (self: t_Wrapping u64) (n: u32) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__rotate_left self._0 n) <: t_Wrapping u64

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__rotate_right (self: t_Wrapping u64) (n: u32) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__rotate_right self._0 n) <: t_Wrapping u64

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__swap_bytes (self: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__swap_bytes self._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__to_be (self: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__to_be self._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__to_le (self: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__to_le self._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__from_be (x: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__from_be x._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__from_le (x: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__from_le x._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__reverse_bits (self: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__reverse_bits self._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u64__pow (self: t_Wrapping u64) (exp: u32) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__wrapping_pow self._0 exp) <: t_Wrapping u64

/// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u64__is_power_of_two (self: t_Wrapping u64) : bool =
  Core_models.Num.impl_u64__is_power_of_two self._0

/// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u64__next_power_of_two (self: t_Wrapping u64) : t_Wrapping u64 =
  Wrapping (Core_models.Num.impl_u64__wrapping_next_power_of_two self._0) <: t_Wrapping u64

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__MIN: t_Wrapping u128 =
  Wrapping Core_models.Num.impl_u128__MIN <: t_Wrapping u128

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__MAX: t_Wrapping u128 =
  Wrapping Core_models.Num.impl_u128__MAX <: t_Wrapping u128

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__BITS: u32 = Core_models.Num.impl_u128__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__count_ones (self: t_Wrapping u128) : u32 =
  Core_models.Num.impl_u128__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__count_zeros (self: t_Wrapping u128) : u32 =
  Core_models.Num.impl_u128__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__trailing_zeros (self: t_Wrapping u128) : u32 =
  Core_models.Num.impl_u128__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__leading_zeros (self: t_Wrapping u128) : u32 =
  Core_models.Num.impl_u128__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__rotate_left (self: t_Wrapping u128) (n: u32) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__rotate_left self._0 n) <: t_Wrapping u128

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__rotate_right (self: t_Wrapping u128) (n: u32) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__rotate_right self._0 n) <: t_Wrapping u128

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__swap_bytes (self: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__swap_bytes self._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__to_be (self: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__to_be self._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__to_le (self: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__to_le self._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__from_be (x: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__from_be x._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__from_le (x: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__from_le x._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__reverse_bits (self: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__reverse_bits self._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_u128__pow (self: t_Wrapping u128) (exp: u32) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__wrapping_pow self._0 exp) <: t_Wrapping u128

/// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u128__is_power_of_two (self: t_Wrapping u128) : bool =
  Core_models.Num.impl_u128__is_power_of_two self._0

/// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_u128__next_power_of_two (self: t_Wrapping u128) : t_Wrapping u128 =
  Wrapping (Core_models.Num.impl_u128__wrapping_next_power_of_two self._0) <: t_Wrapping u128

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__MIN: t_Wrapping usize =
  Wrapping Core_models.Num.impl_usize__MIN <: t_Wrapping usize

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__MAX: t_Wrapping usize =
  Wrapping Core_models.Num.impl_usize__MAX <: t_Wrapping usize

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__BITS: u32 = Core_models.Num.impl_usize__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__count_ones (self: t_Wrapping usize) : u32 =
  Core_models.Num.impl_usize__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__count_zeros (self: t_Wrapping usize) : u32 =
  Core_models.Num.impl_usize__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__trailing_zeros (self: t_Wrapping usize) : u32 =
  Core_models.Num.impl_usize__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__leading_zeros (self: t_Wrapping usize) : u32 =
  Core_models.Num.impl_usize__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__rotate_left (self: t_Wrapping usize) (n: u32) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__rotate_left self._0 n) <: t_Wrapping usize

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__rotate_right (self: t_Wrapping usize) (n: u32) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__rotate_right self._0 n) <: t_Wrapping usize

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__swap_bytes (self: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__swap_bytes self._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__to_be (self: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__to_be self._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__to_le (self: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__to_le self._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__from_be (x: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__from_be x._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__from_le (x: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__from_le x._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__reverse_bits (self: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__reverse_bits self._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_usize__pow (self: t_Wrapping usize) (exp: u32) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__wrapping_pow self._0 exp) <: t_Wrapping usize

/// See [`std::num::Wrapping::is_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_usize__is_power_of_two (self: t_Wrapping usize) : bool =
  Core_models.Num.impl_usize__is_power_of_two self._0

/// See [`std::num::Wrapping::next_power_of_two`] (and similar for other unsigned integer types)
let impl_Wrapping_of_usize__next_power_of_two (self: t_Wrapping usize) : t_Wrapping usize =
  Wrapping (Core_models.Num.impl_usize__wrapping_next_power_of_two self._0) <: t_Wrapping usize

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__MIN: t_Wrapping i8 = Wrapping Core_models.Num.impl_i8__MIN <: t_Wrapping i8

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__MAX: t_Wrapping i8 = Wrapping Core_models.Num.impl_i8__MAX <: t_Wrapping i8

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__BITS: u32 = Core_models.Num.impl_i8__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__count_ones (self: t_Wrapping i8) : u32 =
  Core_models.Num.impl_i8__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__count_zeros (self: t_Wrapping i8) : u32 =
  Core_models.Num.impl_i8__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__trailing_zeros (self: t_Wrapping i8) : u32 =
  Core_models.Num.impl_i8__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__leading_zeros (self: t_Wrapping i8) : u32 =
  Core_models.Num.impl_i8__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__rotate_left (self: t_Wrapping i8) (n: u32) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__rotate_left self._0 n) <: t_Wrapping i8

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__rotate_right (self: t_Wrapping i8) (n: u32) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__rotate_right self._0 n) <: t_Wrapping i8

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__swap_bytes (self: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__swap_bytes self._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__to_be (self: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__to_be self._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__to_le (self: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__to_le self._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__from_be (x: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__from_be x._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__from_le (x: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__from_le x._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__reverse_bits (self: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__reverse_bits self._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i8__pow (self: t_Wrapping i8) (exp: u32) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__wrapping_pow self._0 exp) <: t_Wrapping i8

/// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
let impl_Wrapping_of_i8__abs (self: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__wrapping_abs self._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
let impl_Wrapping_of_i8__signum (self: t_Wrapping i8) : t_Wrapping i8 =
  Wrapping (Core_models.Num.impl_i8__signum self._0) <: t_Wrapping i8

/// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
let impl_Wrapping_of_i8__is_positive (self: t_Wrapping i8) : bool =
  Core_models.Num.impl_i8__is_positive self._0

/// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
let impl_Wrapping_of_i8__is_negative (self: t_Wrapping i8) : bool =
  Core_models.Num.impl_i8__is_negative self._0

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__MIN: t_Wrapping i16 =
  Wrapping Core_models.Num.impl_i16__MIN <: t_Wrapping i16

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__MAX: t_Wrapping i16 =
  Wrapping Core_models.Num.impl_i16__MAX <: t_Wrapping i16

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__BITS: u32 = Core_models.Num.impl_i16__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__count_ones (self: t_Wrapping i16) : u32 =
  Core_models.Num.impl_i16__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__count_zeros (self: t_Wrapping i16) : u32 =
  Core_models.Num.impl_i16__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__trailing_zeros (self: t_Wrapping i16) : u32 =
  Core_models.Num.impl_i16__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__leading_zeros (self: t_Wrapping i16) : u32 =
  Core_models.Num.impl_i16__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__rotate_left (self: t_Wrapping i16) (n: u32) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__rotate_left self._0 n) <: t_Wrapping i16

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__rotate_right (self: t_Wrapping i16) (n: u32) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__rotate_right self._0 n) <: t_Wrapping i16

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__swap_bytes (self: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__swap_bytes self._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__to_be (self: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__to_be self._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__to_le (self: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__to_le self._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__from_be (x: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__from_be x._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__from_le (x: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__from_le x._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__reverse_bits (self: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__reverse_bits self._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i16__pow (self: t_Wrapping i16) (exp: u32) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__wrapping_pow self._0 exp) <: t_Wrapping i16

/// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
let impl_Wrapping_of_i16__abs (self: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__wrapping_abs self._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
let impl_Wrapping_of_i16__signum (self: t_Wrapping i16) : t_Wrapping i16 =
  Wrapping (Core_models.Num.impl_i16__signum self._0) <: t_Wrapping i16

/// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
let impl_Wrapping_of_i16__is_positive (self: t_Wrapping i16) : bool =
  Core_models.Num.impl_i16__is_positive self._0

/// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
let impl_Wrapping_of_i16__is_negative (self: t_Wrapping i16) : bool =
  Core_models.Num.impl_i16__is_negative self._0

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__MIN: t_Wrapping i32 =
  Wrapping Core_models.Num.impl_i32__MIN <: t_Wrapping i32

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__MAX: t_Wrapping i32 =
  Wrapping Core_models.Num.impl_i32__MAX <: t_Wrapping i32

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__BITS: u32 = Core_models.Num.impl_i32__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__count_ones (self: t_Wrapping i32) : u32 =
  Core_models.Num.impl_i32__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__count_zeros (self: t_Wrapping i32) : u32 =
  Core_models.Num.impl_i32__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__trailing_zeros (self: t_Wrapping i32) : u32 =
  Core_models.Num.impl_i32__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__leading_zeros (self: t_Wrapping i32) : u32 =
  Core_models.Num.impl_i32__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__rotate_left (self: t_Wrapping i32) (n: u32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__rotate_left self._0 n) <: t_Wrapping i32

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__rotate_right (self: t_Wrapping i32) (n: u32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__rotate_right self._0 n) <: t_Wrapping i32

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__swap_bytes (self: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__swap_bytes self._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__to_be (self: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__to_be self._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__to_le (self: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__to_le self._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__from_be (x: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__from_be x._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__from_le (x: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__from_le x._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__reverse_bits (self: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__reverse_bits self._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i32__pow (self: t_Wrapping i32) (exp: u32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__wrapping_pow self._0 exp) <: t_Wrapping i32

/// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
let impl_Wrapping_of_i32__abs (self: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__wrapping_abs self._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
let impl_Wrapping_of_i32__signum (self: t_Wrapping i32) : t_Wrapping i32 =
  Wrapping (Core_models.Num.impl_i32__signum self._0) <: t_Wrapping i32

/// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
let impl_Wrapping_of_i32__is_positive (self: t_Wrapping i32) : bool =
  Core_models.Num.impl_i32__is_positive self._0

/// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
let impl_Wrapping_of_i32__is_negative (self: t_Wrapping i32) : bool =
  Core_models.Num.impl_i32__is_negative self._0

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__MIN: t_Wrapping i64 =
  Wrapping Core_models.Num.impl_i64__MIN <: t_Wrapping i64

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__MAX: t_Wrapping i64 =
  Wrapping Core_models.Num.impl_i64__MAX <: t_Wrapping i64

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__BITS: u32 = Core_models.Num.impl_i64__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__count_ones (self: t_Wrapping i64) : u32 =
  Core_models.Num.impl_i64__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__count_zeros (self: t_Wrapping i64) : u32 =
  Core_models.Num.impl_i64__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__trailing_zeros (self: t_Wrapping i64) : u32 =
  Core_models.Num.impl_i64__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__leading_zeros (self: t_Wrapping i64) : u32 =
  Core_models.Num.impl_i64__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__rotate_left (self: t_Wrapping i64) (n: u32) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__rotate_left self._0 n) <: t_Wrapping i64

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__rotate_right (self: t_Wrapping i64) (n: u32) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__rotate_right self._0 n) <: t_Wrapping i64

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__swap_bytes (self: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__swap_bytes self._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__to_be (self: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__to_be self._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__to_le (self: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__to_le self._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__from_be (x: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__from_be x._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__from_le (x: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__from_le x._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__reverse_bits (self: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__reverse_bits self._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i64__pow (self: t_Wrapping i64) (exp: u32) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__wrapping_pow self._0 exp) <: t_Wrapping i64

/// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
let impl_Wrapping_of_i64__abs (self: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__wrapping_abs self._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
let impl_Wrapping_of_i64__signum (self: t_Wrapping i64) : t_Wrapping i64 =
  Wrapping (Core_models.Num.impl_i64__signum self._0) <: t_Wrapping i64

/// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
let impl_Wrapping_of_i64__is_positive (self: t_Wrapping i64) : bool =
  Core_models.Num.impl_i64__is_positive self._0

/// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
let impl_Wrapping_of_i64__is_negative (self: t_Wrapping i64) : bool =
  Core_models.Num.impl_i64__is_negative self._0

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__MIN: t_Wrapping i128 =
  Wrapping Core_models.Num.impl_i128__MIN <: t_Wrapping i128

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__MAX: t_Wrapping i128 =
  Wrapping Core_models.Num.impl_i128__MAX <: t_Wrapping i128

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__BITS: u32 = Core_models.Num.impl_i128__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__count_ones (self: t_Wrapping i128) : u32 =
  Core_models.Num.impl_i128__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__count_zeros (self: t_Wrapping i128) : u32 =
  Core_models.Num.impl_i128__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__trailing_zeros (self: t_Wrapping i128) : u32 =
  Core_models.Num.impl_i128__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__leading_zeros (self: t_Wrapping i128) : u32 =
  Core_models.Num.impl_i128__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__rotate_left (self: t_Wrapping i128) (n: u32) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__rotate_left self._0 n) <: t_Wrapping i128

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__rotate_right (self: t_Wrapping i128) (n: u32) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__rotate_right self._0 n) <: t_Wrapping i128

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__swap_bytes (self: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__swap_bytes self._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__to_be (self: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__to_be self._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__to_le (self: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__to_le self._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__from_be (x: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__from_be x._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__from_le (x: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__from_le x._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__reverse_bits (self: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__reverse_bits self._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_i128__pow (self: t_Wrapping i128) (exp: u32) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__wrapping_pow self._0 exp) <: t_Wrapping i128

/// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
let impl_Wrapping_of_i128__abs (self: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__wrapping_abs self._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
let impl_Wrapping_of_i128__signum (self: t_Wrapping i128) : t_Wrapping i128 =
  Wrapping (Core_models.Num.impl_i128__signum self._0) <: t_Wrapping i128

/// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
let impl_Wrapping_of_i128__is_positive (self: t_Wrapping i128) : bool =
  Core_models.Num.impl_i128__is_positive self._0

/// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
let impl_Wrapping_of_i128__is_negative (self: t_Wrapping i128) : bool =
  Core_models.Num.impl_i128__is_negative self._0

/// See [`std::num::Wrapping::MIN`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__MIN: t_Wrapping isize =
  Wrapping Core_models.Num.impl_isize__MIN <: t_Wrapping isize

/// See [`std::num::Wrapping::MAX`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__MAX: t_Wrapping isize =
  Wrapping Core_models.Num.impl_isize__MAX <: t_Wrapping isize

/// See [`std::num::Wrapping::BITS`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__BITS: u32 = Core_models.Num.impl_isize__BITS

/// See [`std::num::Wrapping::count_ones`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__count_ones (self: t_Wrapping isize) : u32 =
  Core_models.Num.impl_isize__count_ones self._0

/// See [`std::num::Wrapping::count_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__count_zeros (self: t_Wrapping isize) : u32 =
  Core_models.Num.impl_isize__count_zeros self._0

/// See [`std::num::Wrapping::trailing_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__trailing_zeros (self: t_Wrapping isize) : u32 =
  Core_models.Num.impl_isize__trailing_zeros self._0

/// See [`std::num::Wrapping::leading_zeros`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__leading_zeros (self: t_Wrapping isize) : u32 =
  Core_models.Num.impl_isize__leading_zeros self._0

/// See [`std::num::Wrapping::rotate_left`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__rotate_left (self: t_Wrapping isize) (n: u32) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__rotate_left self._0 n) <: t_Wrapping isize

/// See [`std::num::Wrapping::rotate_right`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__rotate_right (self: t_Wrapping isize) (n: u32) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__rotate_right self._0 n) <: t_Wrapping isize

/// See [`std::num::Wrapping::swap_bytes`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__swap_bytes (self: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__swap_bytes self._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::to_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__to_be (self: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__to_be self._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::to_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__to_le (self: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__to_le self._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::from_be`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__from_be (x: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__from_be x._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::from_le`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__from_le (x: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__from_le x._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::reverse_bits`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__reverse_bits (self: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__reverse_bits self._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::pow`] (and similar for `Saturating` and other integer types)
let impl_Wrapping_of_isize__pow (self: t_Wrapping isize) (exp: u32) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__wrapping_pow self._0 exp) <: t_Wrapping isize

/// See [`std::num::Wrapping::abs`] (and similar for other signed integer types)
let impl_Wrapping_of_isize__abs (self: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__wrapping_abs self._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::signum`] (and similar for other signed integer types)
let impl_Wrapping_of_isize__signum (self: t_Wrapping isize) : t_Wrapping isize =
  Wrapping (Core_models.Num.impl_isize__signum self._0) <: t_Wrapping isize

/// See [`std::num::Wrapping::is_positive`] (and similar for other signed integer types)
let impl_Wrapping_of_isize__is_positive (self: t_Wrapping isize) : bool =
  Core_models.Num.impl_isize__is_positive self._0

/// See [`std::num::Wrapping::is_negative`] (and similar for other signed integer types)
let impl_Wrapping_of_isize__is_negative (self: t_Wrapping isize) : bool =
  Core_models.Num.impl_isize__is_negative self._0
