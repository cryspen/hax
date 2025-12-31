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

-- Macro to generate Cast instances for all integer type pairs.
open Lean in
set_option hygiene false in
macro "declare_Hax_cast_instances" : command => do
  let mut cmds := #[]
  -- (`int_type`, `signedness`)
  let tys : List (Name × Bool) := [
    (`UInt8, false),
    (`UInt16, false),
    (`UInt32, false),
    (`UInt64, false),
    (`USize64, false),
    (`Int8, true),
    (`Int16, true),
    (`Int32, true),
    (`Int64, true),
    (`ISize, true)
  ]
  for (srcName, srcSigned) in tys do
    for (dstName, dstSigned) in tys do
      let srcIdent := mkIdent srcName
      let dstIdent := mkIdent dstName
      let toInt ← if srcSigned then `(x.toInt) else `(Int.ofNat x.toNat)
      let result ←
        if dstSigned then
          `($(mkIdent (dstName ++ `ofInt)) $toInt)
        else
          `($(mkIdent (dstName ++ `ofNat)) (($toInt).emod $(mkIdent (dstName ++ `size))).toNat)
      cmds := cmds.push $ ← `(
        @[spec] instance : Cast $srcIdent $dstIdent where cast x := pure $result
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_cast_instances

@[spec]
instance : Cast String String where
  cast x := pure x

@[simp, spec, hax_bv_decide]
def Rust_primitives.Hax.cast_op {α β} [c: Cast α β] (x:α) : (RustM β) := c.cast x

end Cast
