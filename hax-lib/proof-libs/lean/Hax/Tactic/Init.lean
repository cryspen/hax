import Lean

initialize do pure () <*
  Lean.Meta.registerSimpAttr `hax_bv_decide "simp rules for hax-specific bv_decide preprocessing"

initialize Lean.registerTraceClass `Hax.hax_construct_pure


register_option hax_mvcgen.specset : String := {
  defValue := "bv"
  descr    := "Identifier of the set of specs used for `hax_mvcgen`"
}
