module Std.Collections.Hash.Map

val t_HashMap (k v s:Type0): eqtype

val impl__new #k #v: unit -> t_HashMap k v Std.Hash.Random.t_RandomState

val impl_2__get #k #v #s (#y:Type0): t_HashMap k v s -> k -> Core_models.Option.t_Option v

val impl_2__insert #k #v #s: t_HashMap k v s -> k -> v -> (t_HashMap k v s & Core_models.Option.t_Option v)
