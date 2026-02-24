module Rust_primitives.Mem

open FStar.Mul

let copy (#t: Type0) (x: t) = x
let replace (#t: Type0) (dest: t) (src: t) = (src, dest)
