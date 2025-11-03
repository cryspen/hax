module Core_models.Iter.Adapters.Enumerate
open Rust_primitives.Integers

type t_Enumerate t = { iter: t; count: usize }

