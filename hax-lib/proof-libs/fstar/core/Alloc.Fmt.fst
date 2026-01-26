module Alloc.Fmt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

assume
val format': args: Core_models.Fmt.t_Arguments -> Alloc.String.t_String

unfold
let format = format'
