
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Tests.Legacy__literals._.requires (x : Hax_lib.Int.Int) : Result Bool := do
  (← (← Rust_primitives.Hax.Int.gt
        x
        (← Hax_lib.Int.Impl_7._unsafe_from_str "0"))
    &&? (← Rust_primitives.Hax.Int.lt
        x
        (← Hax_lib.Int.Impl_7._unsafe_from_str "16")))

def Tests.Legacy__literals.math_integers (x : Hax_lib.Int.Int) : Result u8 := do
  let _ ← (pure (← Rust_primitives.Hax.Int.from_machine (3 : usize)));
  let _neg_dec : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "-340282366920938463463374607431768211455000"));
  let _pos_dec : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "340282366920938463463374607431768211455000"));
  let _neg_hex : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "-340282366920938463463374607431768211455000"));
  let _pos_hex : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "340282366920938463463374607431768211455000"));
  let _neg_octal : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "-340282366920938463463374607431768211455000"));
  let _pos_octal : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "340282366920938463463374607431768211455000"));
  let _neg_bin : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "-340282366920938463463374607431768211455000"));
  let _pos_bin : Hax_lib.Int.Int ← (pure
    (← Hax_lib.Int.Impl_7._unsafe_from_str
        "340282366920938463463374607431768211455000"));
  let _ ← (pure
    (← Rust_primitives.Hax.Int.gt
        (← Hax_lib.Int.Impl_7._unsafe_from_str
            "-340282366920938463463374607431768211455000")
        (← Hax_lib.Int.Impl_7._unsafe_from_str
            "340282366920938463463374607431768211455000")));
  let _ ← (pure (← Rust_primitives.Hax.Int.lt x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.ge x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.le x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.ne x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.eq x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.add x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.sub x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.mul x x));
  let _ ← (pure (← Rust_primitives.Hax.Int.div x x));
  let _ ← (pure (← Hax_lib.Int.Impl_55.to_i16 x));
  let _ ← (pure (← Hax_lib.Int.Impl_57.to_i32 x));
  let _ ← (pure (← Hax_lib.Int.Impl_59.to_i64 x));
  let _ ← (pure (← Hax_lib.Int.Impl_61.to_i128 x));
  let _ ← (pure (← Hax_lib.Int.Impl_63.to_isize x));
  let _ ← (pure (← Hax_lib.Int.Impl_43.to_u16 x));
  let _ ← (pure (← Hax_lib.Int.Impl_45.to_u32 x));
  let _ ← (pure (← Hax_lib.Int.Impl_47.to_u64 x));
  let _ ← (pure (← Hax_lib.Int.Impl_49.to_u128 x));
  let _ ← (pure (← Hax_lib.Int.Impl_51.to_usize x));
  (← Hax_lib.Int.Impl_41.to_u8
      (← Rust_primitives.Hax.Int.add x (← Rust_primitives.Hax.Int.mul x x)))

def Tests.Legacy__literals.panic_with_msg
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.never_to_any
      (← Core.Panicking.panic_fmt
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["with msg"])))

structure Tests.Legacy__literals.Foo where
  field : u8

instance Tests.Legacy__literals.Impl :
  Core.Marker.StructuralPartialEq Tests.Legacy__literals.Foo
  where


instance Tests.Legacy__literals.Impl_1 :
  Core.Cmp.PartialEq Tests.Legacy__literals.Foo Tests.Legacy__literals.Foo
  where


instance Tests.Legacy__literals.Impl_2 :
  Core.Cmp.Eq Tests.Legacy__literals.Foo
  where


def Tests.Legacy__literals.CONSTANT : Result Tests.Legacy__literals.Foo := do
  (Tests.Legacy__literals.Foo.mk (field := (3 : u8)))

def Tests.Legacy__literals.numeric
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (123 : usize));
  let _ ← (pure (-42 : isize));
  let _ ← (pure (42 : isize));
  let _ ← (pure (-42 : i32));
  let _ ← (pure (22222222222222222222 : u128));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__literals.patterns
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (match (1 : u8) with
      | TODO_LINE_622 => do Rust_primitives.Hax.Tuple0.mk
      | _ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match
      (Rust_primitives.Hax.Tuple2.mk
        "hello" (Rust_primitives.Hax.Tuple2.mk (123 : i32) #v["a", "b"]))
    with
      | ⟨TODO_LINE_622, ⟨TODO_LINE_622, _todo⟩⟩
        => do Rust_primitives.Hax.Tuple0.mk
      | _ => do Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (match (Tests.Legacy__literals.Foo.mk (field := (4 : u8))) with
      | {field := TODO_LINE_622} => do Rust_primitives.Hax.Tuple0.mk
      | _ => do Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__literals.casts
  (x8 : u8)
  (x16 : u16)
  (x32 : u32)
  (x64 : u64)
  (xs : usize)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8)
            +? (← Rust_primitives.Hax.cast_op x16))
          +? (← Rust_primitives.Hax.cast_op x32))
        +? x64)
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8)
            +? (← Rust_primitives.Hax.cast_op x16))
          +? x32)
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8) +? x16)
          +? (← Rust_primitives.Hax.cast_op x32))
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← x8 +? (← Rust_primitives.Hax.cast_op x16))
          +? (← Rust_primitives.Hax.cast_op x32))
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8)
            +? (← Rust_primitives.Hax.cast_op x16))
          +? (← Rust_primitives.Hax.cast_op x32))
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8)
            +? (← Rust_primitives.Hax.cast_op x16))
          +? (← Rust_primitives.Hax.cast_op x32))
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8)
            +? (← Rust_primitives.Hax.cast_op x16))
          +? (← Rust_primitives.Hax.cast_op x32))
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  let _ ← (pure
    (← (← (← (← (← Rust_primitives.Hax.cast_op x8)
            +? (← Rust_primitives.Hax.cast_op x16))
          +? (← Rust_primitives.Hax.cast_op x32))
        +? (← Rust_primitives.Hax.cast_op x64))
      +? (← Rust_primitives.Hax.cast_op xs)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__literals.empty_array
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Rust_primitives.unsize #v[]));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__literals.fn_pointer_cast
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let f ← (pure (fun x => (do x : Result u32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__literals.null : Char := ' '