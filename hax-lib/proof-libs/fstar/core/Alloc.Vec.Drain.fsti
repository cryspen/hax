module Alloc.Vec.Drain

val t_Drain: Type0 -> unit -> Type0

[@FStar.Tactics.Typeclasses.tcinstance]
val iterator_drain t a: Core_models.Iter.Traits.Iterator.t_Iterator (t_Drain t a)
