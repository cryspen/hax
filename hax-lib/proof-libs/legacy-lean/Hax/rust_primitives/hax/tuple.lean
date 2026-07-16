
/-

# Tuples

-/

namespace rust_primitives.hax

structure Tuple0 where
deriving Repr, BEq, DecidableEq

structure Tuple1 (α0: Type) where
  _0 : α0
deriving Repr, BEq, DecidableEq

structure Tuple2 (α0 α1: Type) where
  _0 : α0
  _1 : α1
deriving Repr, BEq, DecidableEq

structure Tuple3 (α0 α1 α2: Type) where
  _0 : α0
  _1 : α1
  _2 : α2
deriving Repr, BEq, DecidableEq

structure Tuple4 (α0 α1 α2 α3 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
deriving Repr, BEq, DecidableEq

structure Tuple5 (α0 α1 α2 α3 α4 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
deriving Repr, BEq, DecidableEq

structure Tuple6 (α0 α1 α2 α3 α4 α5 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
deriving Repr, BEq, DecidableEq

structure Tuple7 (α0 α1 α2 α3 α4 α5 α6 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
deriving Repr, BEq, DecidableEq

structure Tuple8 (α0 α1 α2 α3 α4 α5 α6 α7 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7
deriving Repr, BEq, DecidableEq

structure Tuple9 (α0 α1 α2 α3 α4 α5 α6 α7 α8 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7
  _8 : α8
deriving Repr, BEq, DecidableEq

structure Tuple10 (α0 α1 α2 α3 α4 α5 α6 α7 α8 α9: Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7
  _8 : α8
  _9 : α9
deriving Repr, BEq, DecidableEq

end rust_primitives.hax
