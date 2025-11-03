module Core_models.Iter.Adapters.Step_by
open Rust_primitives.Integers

type t_StepBy t = { 
  f_iter: t;
  f_step: n: usize {v n > 0};
  f_first_take: bool;
}

