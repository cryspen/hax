module Alloc.Boxed

type t_Box t t_Global = t

assume val impl__new #t (v: t) : t
