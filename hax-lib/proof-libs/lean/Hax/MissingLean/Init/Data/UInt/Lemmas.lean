import Hax.MissingLean.Init.Data.UInt.Lemmas_UInt128

attribute [grind =_] UInt8.le_ofNat_iff
attribute [grind =_] UInt16.le_ofNat_iff
attribute [grind =_] UInt32.le_ofNat_iff
attribute [grind =_] UInt64.le_ofNat_iff
attribute [grind =_] UInt128.le_ofNat_iff

theorem UInt64.le_self_add {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    a ≤ a + b := by
  rw [le_iff_toNat_le, UInt64.toNat_add_of_lt h]
  exact Nat.le_add_right a.toNat b.toNat

theorem UInt64.succ_le_of_lt {a b : UInt64} (h : a < b) :
    a + 1 ≤ b := by grind

theorem UInt64.add_le_of_le {a b c : UInt64} (habc : a + b ≤ c) (hab : a.toNat + b.toNat < 2 ^ 64):
    a ≤ c := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add_of_lt hab] at *
  omega

open Lean in
set_option hygiene false in
macro "additional_uint_lemmas" typeName:ident _width:term : command => do
  let tyDot (n : Name) := mkIdent (typeName.getId ++ n)
  let tyRw (n : Name) : TSyntax `Lean.Parser.Tactic.rwRule := .mk
    (Syntax.node .none ``Lean.Parser.Tactic.rwRule #[mkNullNode, tyDot n])
  `(
    namespace $typeName

      theorem ofNat_eq_of_toNat_eq {a : Nat} {b : $typeName} (h : b.toNat = a) : ofNat a = b := by
        subst_vars; exact $(mkIdent (typeName.getId ++ `ofNat_toNat))

      theorem sub_add_eq {a b c : $typeName} : a - (b + c) = a - b - c := by grind

      theorem sub_succ_lt_self (a b : $typeName) (h : a < b) :
          (b - (a + 1)).toNat < (b - a).toNat := by
        rw [sub_add_eq]
        rw [$(tyRw `toNat_sub_of_le)]
        try simp only [USize.toNat_one]
        apply Nat.sub_one_lt_of_lt
        · change (0 : $typeName).toNat < (b - a).toNat
          rw [← lt_iff_toNat_lt]
          grind
        · grind

    end $typeName
  )

additional_uint_lemmas UInt8 8
additional_uint_lemmas UInt16 16
additional_uint_lemmas UInt32 32
additional_uint_lemmas UInt64 64
additional_uint_lemmas UInt128 128
