module Rust_primitives.String

open Rust_primitives.Integers

val str_concat: string -> string -> string 

val str_of_char: FStar.Char.char -> string

val str_sub: string -> usize -> usize -> string

val str_sub_bytes: string -> usize -> usize -> string

val str_index: string -> usize -> FStar.Char.char

val str_len: string -> usize

val str_char_count: string -> usize

val str_is_char_boundary: string -> usize -> bool

val str_is_utf8: Rust_primitives.Arrays.t_Slice u8 -> bool

val str_from_utf8_lossy: Rust_primitives.Arrays.t_Slice u8 -> string
