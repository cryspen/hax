import Hax.Rust_primitives.Num
import Hax.Tactic.Init

/-

# Casts

-/
section Cast

/-- Hax-introduced explicit cast. It is partial (returns a `RustM`) -/
@[simp, spec, hax_bv_decide]
def Core.Convert.From._from (β α) [Coe α (RustM β)] (x:α) : (RustM β) := x

/-- Rust-supported casts on base types -/
class Cast (α β: Type) where
  cast : α → RustM β

attribute [hax_bv_decide] Cast.cast

/-- Wrapping cast, does not fail on overflow -/
@[spec]
instance : Cast i64 i32 where
  cast x := pure (Int64.toInt32 x)

@[spec]
instance : Cast i64 (RustM i32) where
  cast x := pure (x.toInt32)

@[spec]
instance : Cast usize u32 where
  cast x := pure (USize64.toUInt32 x)

@[spec]
instance : Cast String String where
  cast x := pure x

@[simp, spec, hax_bv_decide]
def Rust_primitives.Hax.cast_op {α β} [c: Cast α β] (x:α) : (RustM β) := c.cast x

end Cast
