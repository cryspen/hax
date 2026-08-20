module Core_models.Slice.Ascii
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

let is_ascii_whitespace_byte (b: u8) : bool =
  b =. mk_u8 32 || b =. mk_u8 9 || b =. mk_u8 10 || b =. mk_u8 12 || b =. mk_u8 13

let to_ascii_lowercase_byte (b: u8) : u8 =
  if b >=. mk_u8 65 && b <=. mk_u8 90 then b +! mk_u8 32 else b

let to_ascii_uppercase_byte (b: u8) : u8 =
  if b >=. mk_u8 97 && b <=. mk_u8 122 then b -! mk_u8 32 else b

/// See [`std::slice::is_ascii`]
assume
val impl__is_ascii': s: t_Slice u8 -> bool

unfold
let impl__is_ascii = impl__is_ascii'

/// See [`std::slice::eq_ignore_ascii_case`]
assume
val impl__eq_ignore_ascii_case': s: t_Slice u8 -> other: t_Slice u8 -> bool

unfold
let impl__eq_ignore_ascii_case = impl__eq_ignore_ascii_case'

/// See [`std::slice::trim_ascii_start`]
assume
val impl__trim_ascii_start': s: t_Slice u8 -> t_Slice u8

unfold
let impl__trim_ascii_start = impl__trim_ascii_start'

/// See [`std::slice::trim_ascii_end`]
assume
val impl__trim_ascii_end': s: t_Slice u8 -> t_Slice u8

unfold
let impl__trim_ascii_end = impl__trim_ascii_end'

/// See [`std::slice::trim_ascii`]
let impl__trim_ascii (s: t_Slice u8) : t_Slice u8 =
  impl__trim_ascii_end (impl__trim_ascii_start s <: t_Slice u8)

/// See [`std::slice::make_ascii_lowercase`]
assume
val impl__make_ascii_lowercase': s: t_Slice u8 -> t_Slice u8

unfold
let impl__make_ascii_lowercase = impl__make_ascii_lowercase'

/// See [`std::slice::make_ascii_uppercase`]
assume
val impl__make_ascii_uppercase': s: t_Slice u8 -> t_Slice u8

unfold
let impl__make_ascii_uppercase = impl__make_ascii_uppercase'
