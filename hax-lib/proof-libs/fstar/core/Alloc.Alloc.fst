module Alloc.Alloc
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Global = | Global : t_Global
