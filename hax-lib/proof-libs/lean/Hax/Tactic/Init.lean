import Lean

initialize do pure () <*
  Lean.Meta.registerSimpAttr `hax_bv_decide "simp rules for hax-specific bv_decide preprocessing"

initialize Lean.registerTraceClass `Hax.hax_construct_pure
