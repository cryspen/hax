
/-

# Tuples

-/

namespace Rust_primitives.Hax

structure Tuple0 where

structure Tuple1 (α0: Type) where
  _0 : α0

structure Tuple2 (α0 α1: Type) where
  _0 : α0
  _1 : α1

structure Tuple3 (α0 α1 α2: Type) where
  _0 : α0
  _1 : α1
  _2 : α2

structure Tuple4 (α0 α1 α2 α3 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3

structure Tuple5 (α0 α1 α2 α3 α4 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4

structure Tuple6 (α0 α1 α2 α3 α4 α5 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5

structure Tuple7 (α0 α1 α2 α3 α4 α5 α6 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6

structure Tuple8 (α0 α1 α2 α3 α4 α5 α6 α7 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7

structure Tuple9 (α0 α1 α2 α3 α4 α5 α6 α7 α8 α9 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7
  _8 : α8

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

def Tuple2.fst {α0 α1 : Type} (t : Tuple2 α0 α1) : α0 := t._0
def Tuple2.snd {α0 α1 : Type} (t : Tuple2 α0 α1) : α1 := t._1

@[simp] theorem Tuple2.fst_mk {α0 α1 : Type} (a : α0) (b : α1) :
  (Tuple2.fst (Tuple2.mk a b)) = a := rfl

@[simp] theorem Tuple2.snd_mk {α0 α1 : Type} (a : α0) (b : α1) :
  (Tuple2.snd (Tuple2.mk a b)) = b := rfl

end Rust_primitives.Hax
