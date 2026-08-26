module Core_models.Str
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// `b` is one of the five bytes `u8::is_ascii_whitespace` accepts (space, tab,
/// line feed, form feed, carriage return — vertical tab is *not* one of them).
val is_ascii_whitespace_byte (b: u8) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// ASCII-only `to_lowercase` on a single byte; non-ASCII bytes pass through.
val ascii_lowercase_byte (b: u8) : Prims.Pure u8 Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::as_bytes`]
val impl_str__as_bytes (s: string) : Prims.Pure (t_Slice u8) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::len`]
val impl_str__len (s: string) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::is_empty`]
val impl_str__is_empty (s: string) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::as_str`]
val impl_str__as_str (s: string) : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::is_char_boundary`]. A byte index is a
/// boundary unless it points at a UTF-8 continuation byte (`0b10xxxxxx`).
val impl_str__is_char_boundary (s: string) (index: usize)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::floor_char_boundary`]
val impl_str__floor_char_boundary (s: string) (index: usize)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::is_ascii`]
val impl_str__is_ascii (s: string) : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::eq_ignore_ascii_case`]
val impl_str__eq_ignore_ascii_case (s other: string)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::trim_ascii_start`]
val impl_str__trim_ascii_start (s: string) : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::trim_ascii_end`]
val impl_str__trim_ascii_end (s: string) : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::trim_ascii`]
val impl_str__trim_ascii (s: string) : Prims.Pure string Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::parse`]
val impl_str__parse (#v_F: Type0) {| i0: Core_models.Str.Traits.t_FromStr v_F |} (s: string)
    : Prims.Pure (Core_models.Result.t_Result v_F i0.f_Err) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::primitive::str::ceil_char_boundary`]
val impl_str__ceil_char_boundary (s: string) (index: usize)
    : Prims.Pure usize (requires index <=. (impl_str__len s <: usize)) (fun _ -> Prims.l_True)

/// See [`std::primitive::str::split_at`]
val impl_str__split_at (s: string) (mid: usize)
    : Prims.Pure (string & string)
      (requires impl_str__is_char_boundary s mid)
      (fun _ -> Prims.l_True)

/// See [`std::primitive::str::split_at_checked`]
val impl_str__split_at_checked (s: string) (mid: usize)
    : Prims.Pure (Core_models.Option.t_Option (string & string))
      Prims.l_True
      (fun _ -> Prims.l_True)
