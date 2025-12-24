import Lean.Meta.Tactic.Simp.Attr

initialize do pure () <*
  Lean.Meta.registerSimpAttr `hax_bv_decide "simp rules for hax-specific bv_decide preprocessing"
