module Std.Io.Impls
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Std.Io.t_Read (t_Slice u8)
