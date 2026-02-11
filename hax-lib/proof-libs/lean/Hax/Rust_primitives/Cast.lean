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
  let tys : List Name := [`UInt8,`UInt16,`UInt32,`UInt64,`USize64,`Int8,`Int16,`Int32,`Int64,`ISize]
  for srcName in tys do
    for dstName in tys do
      let srcIdent := mkIdent srcName
      let dstIdent := mkIdent dstName
      let result ←
        if dstName == srcName then
          `(x)
        else
          `($(mkIdent (srcName ++ dstName.appendBefore "to")) x)
      cmds := cmds.push $ ← `(
        @[spec] instance : Cast $srcIdent $dstIdent where cast x := pure $result
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_cast_instances

@[spec]
instance : Cast String String where
  cast x := pure x

@[simp, spec, hax_bv_decide]
def rust_primitives.hax.cast_op {α β} [c: Cast α β] (x:α) : (RustM β) := c.cast x

end Cast
