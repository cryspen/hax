import Lean

open Lean

/-- Environment extension to store `@[purify]` declarations. -/
initialize purifyExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `purifyExt
    addEntryFn := fun state name => state.push name
    addImportedFn := fun states =>
      states.foldl (fun acc st => st.foldl (fun acc name => acc.push name) acc) #[]
  }

initialize registerBuiltinAttribute {
  name := `purify
  descr := "Register a purification lemma for `hax_construct_pure`. \
    These lemmas decompose monadic programs into sub-programs with the same \
    `⦃⌜True⌝⦄ ... ⦃⇓ r => ⌜r = ?⌝⦄` shape, enabling recursive purification."
  add := fun declName _stx _kind => do
    setEnv $ purifyExt.addEntry (← getEnv) declName
}
