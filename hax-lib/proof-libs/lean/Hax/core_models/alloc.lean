
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
/- import Hax -/
import Hax.core_models.core_models
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace alloc.alloc

structure Global where
  -- no fields

end alloc.alloc


namespace alloc.borrow

structure Cow (T : Type) where
  _0 : T

class ToOwned.AssociatedTypes (Self : Type) where

class ToOwned (Self : Type)
  [associatedTypes : outParam (ToOwned.AssociatedTypes (Self : Type))]
  where
  to_owned (Self) : (Self -> RustM Self)

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  ToOwned.AssociatedTypes T
  where

instance Impl (T : Type) : ToOwned T where
  to_owned := fun (self : T) => do (pure self)

end alloc.borrow


namespace alloc.boxed

structure Box (T : Type) where
  _0 : T

@[spec]
def Impl.new (T : Type) (v : T) : RustM T := do (pure v)

end alloc.boxed


namespace alloc.collections.btree.set

opaque BTreeSet (T : Type) (U : Type) : Type

@[spec]
def Impl_11.new (T : Type) (U : Type) (_ : rust_primitives.hax.Tuple0) :
    RustM (BTreeSet T U) := do
  (pure (BTreeSet.mk core.option.Option.None core.option.Option.None))

end alloc.collections.btree.set


namespace alloc.collections.vec_deque

structure VecDeque (T : Type) (A : Type) where
  _0 : (rust_primitives.sequence.Seq T)
  _1 : (core.marker.PhantomData A)

opaque Impl_5.push_back (T : Type) (A : Type) (self : (VecDeque T A)) (x : T) :
    RustM (VecDeque T A)

@[spec]
def Impl_5.len (T : Type) (A : Type) (self : (VecDeque T A)) : RustM usize := do
  (rust_primitives.sequence.seq_len T (VecDeque._0 self))

@[spec]
def Impl_5.pop_front (T : Type) (A : Type) (self : (VecDeque T A)) :
    RustM
    (rust_primitives.hax.Tuple2 (VecDeque T A) (core.option.Option T))
    := do
  let hax_temp_output : (core.option.Option T) ←
    if (← ((← (Impl_5.len T A self)) ==? (0 : usize))) then do
      (pure core.option.Option.None)
    else do
      (pure (core.option.Option.Some
        (← (rust_primitives.sequence.seq_last T (VecDeque._0 self)))));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_6.AssociatedTypes (T : Type) (A : Type) :
  core.ops.index.Index.AssociatedTypes (VecDeque T A) usize
  where
  Output := T

instance Impl_6 (T : Type) (A : Type) :
  core.ops.index.Index (VecDeque T A) usize
  where
  index := fun (self : (VecDeque T A)) (i : usize) => do
    (rust_primitives.sequence.seq_index T (VecDeque._0 self) i)

end alloc.collections.vec_deque


namespace alloc.string

structure String where
  _0 : String

end alloc.string


namespace alloc.fmt

opaque format (args : core.fmt.Arguments) : RustM alloc.string.String

end alloc.fmt


namespace alloc.string

@[spec]
def Impl.new (_ : rust_primitives.hax.Tuple0) : RustM String := do
  (pure (String.mk ""))

@[spec]
def Impl.push_str (self : String) (other : String) : RustM String := do
  let self : String :=
    (String.mk (← (rust_primitives.string.str_concat (String._0 self) other)));
  (pure self)

@[spec]
def Impl.push (self : String) (c : Char) : RustM String := do
  let self : String :=
    (String.mk
      (← (rust_primitives.string.str_concat
        (String._0 self)
        (← (rust_primitives.string.str_of_char c)))));
  (pure self)

@[spec]
def Impl.pop (self : String) :
    RustM (rust_primitives.hax.Tuple2 String (core.option.Option Char)) := do
  let l : usize ← (core.str.Impl.len (String._0 self));
  let ⟨self, hax_temp_output⟩ ←
    if (← (l >? (0 : usize))) then do
      let self : String :=
        (String.mk
          (← (rust_primitives.string.str_sub
            (String._0 self)
            (0 : usize)
            (← (l -? (1 : usize))))));
      (pure (rust_primitives.hax.Tuple2.mk
        self
        (core.option.Option.Some
          (← (rust_primitives.string.str_index
            (String._0 self)
            (← (l -? (1 : usize))))))))
    else do
      (pure (rust_primitives.hax.Tuple2.mk self core.option.Option.None));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end alloc.string


namespace alloc.vec

structure Vec (T : Type) (A : Type) where
  _0 : (rust_primitives.sequence.Seq T)
  _1 : (core.marker.PhantomData A)

end alloc.vec


namespace alloc.collections.binary_heap

structure BinaryHeap (T : Type) (A : Type) where
  _0 : (alloc.vec.Vec T A)

@[spec]
def Impl_10.new
    (T : Type)
    (A : Type)
    [trait_constr_new_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
    [trait_constr_new_i0 : core.cmp.Ord T ]
    (_ : rust_primitives.hax.Tuple0) :
    RustM (BinaryHeap T A) := do
  (pure (BinaryHeap.mk
    (alloc.vec.Vec.mk
      (← (rust_primitives.sequence.seq_empty T rust_primitives.hax.Tuple0.mk))
      core.marker.PhantomData.mk)))

end alloc.collections.binary_heap


namespace alloc.slice

@[spec]
def Impl.to_vec (T : Type) (s : (RustSlice T)) :
    RustM (alloc.vec.Vec T alloc.alloc.Global) := do
  (pure (alloc.vec.Vec.mk
    (← (rust_primitives.sequence.seq_from_slice T s))
    core.marker.PhantomData.mk))

@[spec]
def Impl.into_vec (T : Type) (A : Type) (s : (RustSlice T)) :
    RustM (alloc.vec.Vec T A) := do
  (pure (alloc.vec.Vec.mk
    (← (rust_primitives.sequence.seq_from_slice T s))
    core.marker.PhantomData.mk))

end alloc.slice


namespace alloc.vec

@[spec]
def from_elem
    (T : Type)
    [trait_constr_from_elem_associated_type_i0 :
      core.clone.Clone.AssociatedTypes
      T]
    [trait_constr_from_elem_i0 : core.clone.Clone T ]
    (item : T)
    (len : usize) :
    RustM (Vec T alloc.alloc.Global) := do
  (pure (Vec.mk
    (← (rust_primitives.sequence.seq_create T item len))
    core.marker.PhantomData.mk))

@[spec]
def Impl.new (T : Type) (_ : rust_primitives.hax.Tuple0) :
    RustM (Vec T alloc.alloc.Global) := do
  (pure (Vec.mk
    (← (rust_primitives.sequence.seq_empty T rust_primitives.hax.Tuple0.mk))
    core.marker.PhantomData.mk))

@[spec]
def Impl.with_capacity (T : Type) (_c : usize) :
    RustM (Vec T alloc.alloc.Global) := do
  (Impl.new T rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl_1.len (T : Type) (A : Type) (self : (Vec T A)) : RustM usize := do
  (rust_primitives.sequence.seq_len T (Vec._0 self))

end alloc.vec


namespace alloc.collections.binary_heap

@[spec]
def Impl_11.len
    (T : Type)
    (A : Type)
    [trait_constr_len_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
    [trait_constr_len_i0 : core.cmp.Ord T ]
    (self : (BinaryHeap T A)) :
    RustM usize := do
  (alloc.vec.Impl_1.len T A (BinaryHeap._0 self))

end alloc.collections.binary_heap


namespace alloc.vec

@[spec]
def Impl_1.pop (T : Type) (A : Type) (self : (Vec T A)) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) (core.option.Option T)) := do
  let ⟨self, hax_temp_output⟩ ←
    if
    (← ((← (rust_primitives.sequence.seq_len T (Vec._0 self))) >? (0 : usize)))
    then do
      let last : T ← (rust_primitives.sequence.seq_last T (Vec._0 self));
      let self : (Vec T A) :=
        {self
        with _0 := (← (rust_primitives.sequence.seq_slice T
          (Vec._0 self)
          (0 : usize)
          (← ((← (rust_primitives.sequence.seq_len T (Vec._0 self)))
            -? (1 : usize)))))};
      (pure (rust_primitives.hax.Tuple2.mk self (core.option.Option.Some last)))
    else do
      (pure (rust_primitives.hax.Tuple2.mk self core.option.Option.None));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[spec]
def Impl_1.is_empty (T : Type) (A : Type) (self : (Vec T A)) : RustM Bool := do
  ((← (rust_primitives.sequence.seq_len T (Vec._0 self))) ==? (0 : usize))

@[spec]
def Impl_1.as_slice (T : Type) (A : Type) (self : (Vec T A)) :
    RustM (RustSlice T) := do
  (rust_primitives.sequence.seq_to_slice T (Vec._0 self))

opaque Impl_1.truncate (T : Type) (A : Type) (self : (Vec T A)) (n : usize) :
    RustM (Vec T A)

opaque Impl_1.swap_remove (T : Type) (A : Type) (self : (Vec T A)) (n : usize) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) T)

opaque Impl_1.remove (T : Type) (A : Type) (self : (Vec T A)) (index : usize) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) T)

opaque Impl_1.clear (T : Type) (A : Type) (self : (Vec T A)) : RustM (Vec T A)

def Impl_1.push (T : Type) (A : Type) (self : (Vec T A)) (x : T) :
    RustM (Vec T A) := do
  let self : (Vec T A) :=
    {self
    with _0 := (← (rust_primitives.sequence.seq_concat T
      (Vec._0 self)
      (← (rust_primitives.sequence.seq_one T x))))};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl_1.push.spec (T : Type) (A : Type) (self : (Vec T A)) (x : T) :
    Spec
      (requires := do
        ((← (rust_primitives.sequence.seq_len T (Vec._0 self)))
          <? core.num.Impl_11.MAX))
      (ensures := fun _ => pure True)
      (Impl_1.push (T : Type) (A : Type) (self : (Vec T A)) (x : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_1.push] <;> bv_decide
}

end alloc.vec


namespace alloc.collections.binary_heap

def Impl_10.push
    (T : Type)
    (A : Type)
    [trait_constr_push_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
    [trait_constr_push_i0 : core.cmp.Ord T ]
    (self : (BinaryHeap T A))
    (v : T) :
    RustM (BinaryHeap T A) := do
  let self : (BinaryHeap T A) :=
    {self with _0 := (← (alloc.vec.Impl_1.push T A (BinaryHeap._0 self) v))};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_10.push.spec
      (T : Type)
      (A : Type)
      [trait_constr_push_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
      [trait_constr_push_i0 : core.cmp.Ord T ]
      (self : (BinaryHeap T A))
      (v : T) :
    Spec
      (requires := do ((← (Impl_11.len T A self)) <? core.num.Impl_11.MAX))
      (ensures := fun _ => pure True)
      (Impl_10.push (T : Type) (A : Type) (self : (BinaryHeap T A)) (v : T)) :=
{
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_10.push] <;> bv_decide
}

end alloc.collections.binary_heap


namespace alloc.vec

def Impl_1.insert (T : Type) (A : Type)
    (self : (Vec T A))
    (index : usize)
    (element : T) :
    RustM (Vec T A) := do
  let left : (rust_primitives.sequence.Seq T) ←
    (rust_primitives.sequence.seq_slice T (Vec._0 self) (0 : usize) index);
  let right : (rust_primitives.sequence.Seq T) ←
    (rust_primitives.sequence.seq_slice T
      (Vec._0 self)
      index
      (← (rust_primitives.sequence.seq_len T (Vec._0 self))));
  let left : (rust_primitives.sequence.Seq T) ←
    (rust_primitives.sequence.seq_concat T
      left
      (← (rust_primitives.sequence.seq_one T element)));
  let left : (rust_primitives.sequence.Seq T) ←
    (rust_primitives.sequence.seq_concat T left right);
  let self : (Vec T A) := {self with _0 := left};
  (pure self)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_1.insert.spec (T : Type) (A : Type)
      (self : (Vec T A))
      (index : usize)
      (element : T) :
    Spec
      (requires := do
        ((← (index <=? (← (rust_primitives.sequence.seq_len T (Vec._0 self)))))
          &&? (← ((← (rust_primitives.sequence.seq_len T (Vec._0 self)))
            <? core.num.Impl_11.MAX))))
      (ensures := fun _ => pure True)
      (Impl_1.insert
        (T : Type)
        (A : Type)
        (self : (Vec T A))
        (index : usize)
        (element : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_1.insert] <;> bv_decide
}

opaque Impl_1.resize (T : Type) (A : Type)
    (self : (Vec T A))
    (new_size : usize)
    (value : T) :
    RustM (Vec T A)

def Impl_1.append (T : Type) (A : Type) (self : (Vec T A)) (other : (Vec T A)) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) (Vec T A)) := do
  let self : (Vec T A) :=
    {self
    with _0 := (← (rust_primitives.sequence.seq_concat T
      (Vec._0 self)
      (Vec._0 other)))};
  let other : (Vec T A) :=
    {other
    with _0 := (← (rust_primitives.sequence.seq_empty T
      rust_primitives.hax.Tuple0.mk))};
  (pure (rust_primitives.hax.Tuple2.mk self other))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_1.append.spec (T : Type) (A : Type)
      (self : (Vec T A))
      (other : (Vec T A)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.add
            (← (rust_primitives.hax.int.from_machine (← (Impl_1.len T A self))))
            (← (rust_primitives.hax.int.from_machine
              (← (Impl_1.len T A other))))))
          (← (rust_primitives.hax.int.from_machine core.num.Impl_11.MAX))))
      (ensures := fun _ => pure True)
      (Impl_1.append
        (T : Type)
        (A : Type)
        (self : (Vec T A))
        (other : (Vec T A))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_1.append] <;> bv_decide
}

end alloc.vec


namespace alloc.vec.drain

structure Drain (T : Type) (A : Type) where
  _0 : (rust_primitives.sequence.Seq T)
  _1 : (core.marker.PhantomData A)

end alloc.vec.drain


namespace alloc.vec

opaque Impl_1.drain (T : Type) (A : Type) (R : Type)
    (self : (Vec T A))
    (_range : R) :
    RustM (rust_primitives.hax.Tuple2 (Vec T A) (alloc.vec.drain.Drain T A))

end alloc.vec


namespace alloc.vec.drain

@[reducible] instance Impl.AssociatedTypes (T : Type) (A : Type) :
  core.iter.traits.iterator.Iterator.AssociatedTypes (Drain T A)
  where
  Item := T

instance Impl (T : Type) (A : Type) :
  core.iter.traits.iterator.Iterator (Drain T A)
  where
  next := fun (self : (Drain T A)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.sequence.seq_len T (Drain._0 self)))
        ==? (0 : usize))) then do
        (pure (rust_primitives.hax.Tuple2.mk self core.option.Option.None))
      else do
        let res : T ← (rust_primitives.sequence.seq_first T (Drain._0 self));
        let self : (Drain T A) :=
          {self
          with _0 := (← (rust_primitives.sequence.seq_slice T
            (Drain._0 self)
            (1 : usize)
            (← (rust_primitives.sequence.seq_len T (Drain._0 self)))))};
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end alloc.vec.drain


namespace alloc.vec

def Impl_2.extend_from_slice (T : Type) (A : Type)
    (s : (Vec T A))
    (other : (RustSlice T)) :
    RustM (Vec T A) := do
  let s : (Vec T A) :=
    {s
    with _0 := (← (rust_primitives.sequence.seq_concat T
      (Vec._0 s)
      (← (rust_primitives.sequence.seq_from_slice T other))))};
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_2.extend_from_slice.spec (T : Type) (A : Type)
      (s : (Vec T A))
      (other : (RustSlice T)) :
    Spec
      (requires := do
        (rust_primitives.hax.int.le
          (← (rust_primitives.hax.int.add
            (← (rust_primitives.hax.int.from_machine
              (← (rust_primitives.sequence.seq_len T (Vec._0 s)))))
            (← (rust_primitives.hax.int.from_machine
              (← (core.slice.Impl.len T other))))))
          (← (rust_primitives.hax.int.from_machine core.num.Impl_11.MAX))))
      (ensures := fun _ => pure True)
      (Impl_2.extend_from_slice
        (T : Type)
        (A : Type)
        (s : (Vec T A))
        (other : (RustSlice T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_2.extend_from_slice] <;> bv_decide
}

@[reducible] instance Impl_3.AssociatedTypes (T : Type) (A : Type) :
  core.ops.index.Index.AssociatedTypes (Vec T A) usize
  where
  Output := T

instance Impl_3 (T : Type) (A : Type) :
  core.ops.index.Index (Vec T A) usize
  where
  index := fun (self : (Vec T A)) (i : usize) => do
    (rust_primitives.sequence.seq_index T (Vec._0 self) i)

end alloc.vec


namespace alloc.collections.binary_heap

def Impl_10.pop
    (T : Type)
    (A : Type)
    [trait_constr_pop_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
    [trait_constr_pop_i0 : core.cmp.Ord T ]
    (self : (BinaryHeap T A)) :
    RustM
    (rust_primitives.hax.Tuple2 (BinaryHeap T A) (core.option.Option T))
    := do
  let max : (core.option.Option T) := core.option.Option.None;
  let index : usize := (0 : usize);
  let ⟨index, max⟩ ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (Impl_11.len T A self))
      (fun ⟨index, max⟩ i =>
        (do
        ((← (i >? (0 : usize))) ==? (← (core.option.Impl.is_some T max))) :
        RustM Bool))
      (rust_primitives.hax.Tuple2.mk index max)
      (fun ⟨index, max⟩ i =>
        (do
        if
        (← (core.option.Impl.is_none_or T (T -> RustM Bool)
          max
          (fun max =>
            (do
            (core.cmp.PartialOrd.gt T T (← (BinaryHeap._0 self)[i]_?) max) :
            RustM Bool)))) then do
          let max : (core.option.Option T) :=
            (core.option.Option.Some (← (BinaryHeap._0 self)[i]_?));
          let index : usize := i;
          (pure (rust_primitives.hax.Tuple2.mk index max))
        else do
          (pure (rust_primitives.hax.Tuple2.mk index max)) :
        RustM (rust_primitives.hax.Tuple2 usize (core.option.Option T)))));
  let ⟨self, hax_temp_output⟩ ←
    if (← (core.option.Impl.is_some T max)) then do
      let ⟨tmp0, out⟩ ←
        (alloc.vec.Impl_1.remove T A (BinaryHeap._0 self) index);
      let self : (BinaryHeap T A) := {self with _0 := tmp0};
      (pure (rust_primitives.hax.Tuple2.mk self (core.option.Option.Some out)))
    else do
      (pure (rust_primitives.hax.Tuple2.mk self core.option.Option.None));
  (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_10.pop.spec
      (T : Type)
      (A : Type)
      [trait_constr_pop_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
      [trait_constr_pop_i0 : core.cmp.Ord T ]
      (self : (BinaryHeap T A)) :
    Spec
      (requires := do pure True)
      (ensures := fun
          ⟨self__future, res⟩ => do
          ((← ((← (Impl_11.len T A self)) >? (0 : usize)))
            ==? (← (core.option.Impl.is_some T res))))
      (Impl_10.pop (T : Type) (A : Type) (self : (BinaryHeap T A))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_10.pop] <;> bv_decide
}

def Impl_11.peek
    (T : Type)
    (A : Type)
    [trait_constr_peek_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
    [trait_constr_peek_i0 : core.cmp.Ord T ]
    (self : (BinaryHeap T A)) :
    RustM (core.option.Option T) := do
  let max : (core.option.Option T) := core.option.Option.None;
  let max : (core.option.Option T) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (Impl_11.len T A self))
      (fun max i =>
        (do
        ((← (i >? (0 : usize))) ==? (← (core.option.Impl.is_some T max))) :
        RustM Bool))
      max
      (fun max i =>
        (do
        if
        (← (core.option.Impl.is_none_or T (T -> RustM Bool)
          max
          (fun max =>
            (do
            (core.cmp.PartialOrd.gt T T (← (BinaryHeap._0 self)[i]_?) max) :
            RustM Bool)))) then do
          let max : (core.option.Option T) :=
            (core.option.Option.Some (← (BinaryHeap._0 self)[i]_?));
          (pure max)
        else do
          (pure max) :
        RustM (core.option.Option T))));
  (pure max)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl_11.peek.spec
      (T : Type)
      (A : Type)
      [trait_constr_peek_associated_type_i0 : core.cmp.Ord.AssociatedTypes T]
      [trait_constr_peek_i0 : core.cmp.Ord T ]
      (self : (BinaryHeap T A)) :
    Spec
      (requires := do pure True)
      (ensures := fun
          res => do
          ((← ((← (Impl_11.len T A self)) >? (0 : usize)))
            ==? (← (core.option.Impl.is_some T res))))
      (Impl_11.peek (T : Type) (A : Type) (self : (BinaryHeap T A))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl_11.peek] <;> bv_decide
}

end alloc.collections.binary_heap


namespace alloc.vec

@[reducible] instance Impl_4.AssociatedTypes (T : Type) (A : Type) :
  core.ops.deref.Deref.AssociatedTypes (Vec T A)
  where
  Target := (RustSlice T)

instance Impl_4 (T : Type) (A : Type) : core.ops.deref.Deref (Vec T A) where
  deref := fun (self : (Vec T A)) => do (Impl_1.as_slice T A self)

@[instance] opaque Impl_5.AssociatedTypes (T : Type) :
  core.iter.traits.collect.FromIterator.AssociatedTypes
  (Vec T alloc.alloc.Global)
  T :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 (T : Type) :
  core.iter.traits.collect.FromIterator (Vec T alloc.alloc.Global) T :=
  by constructor <;> exact Inhabited.default

end alloc.vec
