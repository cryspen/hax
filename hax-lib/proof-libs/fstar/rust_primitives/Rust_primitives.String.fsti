module Rust_primitives.String

open Rust_primitives.Integers

val str_concat: string -> string -> string 

val str_of_char: FStar.Char.char -> string

val str_sub: string -> usize -> usize -> string

val str_index: string -> usize -> FStar.Char.char
