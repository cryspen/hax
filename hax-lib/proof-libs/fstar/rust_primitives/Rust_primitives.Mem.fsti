module Rust_primitives.Mem

open FStar.Mul

let replace (#t: Type0) (dest: t) (src: t) = (src, dest)
