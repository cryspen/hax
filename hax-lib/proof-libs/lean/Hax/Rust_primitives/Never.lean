namespace rust_primitives.hax

  abbrev Never : Type := Empty
  abbrev never_to_any.{u} {α : Sort u} : Never → α := Empty.elim

end rust_primitives.hax
