module Std.Io.Impls

[@@FStar.Tactics.Typeclasses.tcinstance]
val write_vec: Std.Io.t_Write (Alloc.Vec.t_Vec Rust_primitives.Integers.u8
            Alloc.Alloc.t_Global)

[@@FStar.Tactics.Typeclasses.tcinstance]
val read_slice: Std.Io.t_Read (Rust_primitives.Arrays.t_Slice 
  Rust_primitives.Integers.u8)
