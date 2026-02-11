import Lean

open Lean Elab Std

abbrev SpecSetMap := HashMap Name (HashSet Name)

structure SpecSetEntry where
  specSet : Name
  decl : Name

/-- Environment extension to store spec sets, i.e., sets of declarations to use with
`hax_mvcgen`. -/
initialize specSetExt : SimplePersistentEnvExtension SpecSetEntry SpecSetMap ←
  registerSimplePersistentEnvExtension {
    name := `specSetExt
    addEntryFn := fun state {specSet, decl} =>
      let set := state.getD specSet {}
      state.insert specSet (set.insert decl)
    addImportedFn := fun states =>
      states.foldl
        (fun acc st =>
          st.foldl
            (fun acc {specSet, decl} =>
              let merged := (acc.getD specSet {}).insert decl
              acc.insert specSet merged)
            acc)
        {}
  }

initialize
  registerBuiltinAttribute {
    name  := `specset
    descr := "Add a declaration to a given spec set for `hax_mvcgen`. The spec set can be activated
      via `set_option hax_mvcgen.specset`"
    add   := fun decl stx kind => do
      setEnv $ specSetExt.addEntry (← getEnv) {specSet := stx[1][0].getId, decl}
  }
