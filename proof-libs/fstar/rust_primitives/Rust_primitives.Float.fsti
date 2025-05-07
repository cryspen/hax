module Rust_primitives.Float

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"

type float

val mk_float : string -> float
