module Std.Io.Impls
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Std.Io.t_Read (t_Slice u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Std.Io.t_Write (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
