module Lob_backend
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Side =
  | Side_Buy : t_Side
  | Side_Sell : t_Side

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Cmp.t_PartialEq t_Side t_Side

unfold
let impl_7 = impl_7'

type t_Order = {
  f_id:u64;
  f_side:t_Side;
  f_price:u64;
  f_quantity:u64
}

let impl_14: Core_models.Clone.t_Clone t_Order =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

type t_Match = {
  f_bid_id:u64;
  f_ask_id:u64;
  f_price:u64;
  f_quantity:u64
}

let is_match (order other: t_Order) : bool =
  order.f_quantity >. mk_u64 0 && other.f_quantity >. mk_u64 0 && order.f_side <>. other.f_side &&
  (order.f_side =. (Side_Buy <: t_Side) && order.f_price >=. other.f_price ||
  order.f_side =. (Side_Sell <: t_Side) && order.f_price <=. other.f_price)

let impl_Order__try_match (self other: t_Order) : Core_models.Option.t_Option t_Match =
  if is_match self other
  then
    let quantity:u64 = Core_models.Cmp.min #u64 self.f_quantity other.f_quantity in
    let bid_id, ask_id:(u64 & u64) =
      if self.f_side =. (Side_Buy <: t_Side)
      then self.f_id, other.f_id <: (u64 & u64)
      else other.f_id, self.f_id <: (u64 & u64)
    in
    Core_models.Option.Option_Some
    ({ f_bid_id = bid_id; f_ask_id = ask_id; f_price = self.f_price; f_quantity = quantity }
      <:
      t_Match)
    <:
    Core_models.Option.t_Option t_Match
  else Core_models.Option.Option_None <: Core_models.Option.t_Option t_Match

let process_order
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_Into v_T t_Order)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Convert.t_From v_T t_Order)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core_models.Clone.t_Clone v_T)
      (order: t_Order)
      (other_side: Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global)
    : (Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global &
      (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core_models.Option.t_Option t_Order)) =
  let matches:Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global = Alloc.Vec.impl__new #t_Match () in
  let done:bool = false in
  let done, matches, order, other_side:(bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
    t_Order &
    Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      (Alloc.Collections.Binary_heap.impl_11__len #v_T #Alloc.Alloc.t_Global other_side <: usize)
      (fun temp_0_ temp_1_ ->
          let done, matches, order, other_side:(bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
            t_Order &
            Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global) =
            temp_0_
          in
          let _:usize = temp_1_ in
          true)
      (done, matches, order, other_side
        <:
        (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
          Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global))
      (fun temp_0_ e_i ->
          let done, matches, order, other_side:(bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
            t_Order &
            Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global) =
            temp_0_
          in
          let e_i:usize = e_i in
          if ~.done <: bool
          then
            match
              Core_models.Option.impl__and_then #v_T
                #t_Match
                (Alloc.Collections.Binary_heap.impl_11__peek #v_T #Alloc.Alloc.t_Global other_side
                  <:
                  Core_models.Option.t_Option v_T)
                (fun other ->
                    let other:v_T = other in
                    impl_Order__try_match (Core_models.Convert.f_into #v_T
                          #t_Order
                          #FStar.Tactics.Typeclasses.solve
                          (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve other
                            <:
                            v_T)
                        <:
                        t_Order)
                      order
                    <:
                    Core_models.Option.t_Option t_Match)
              <:
              Core_models.Option.t_Option t_Match
            with
            | Core_models.Option.Option_Some m ->
              let order:t_Order =
                { order with f_quantity = order.f_quantity -! m.f_quantity } <: t_Order
              in
              let tmp0, out:(Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global &
                Core_models.Option.t_Option v_T) =
                Alloc.Collections.Binary_heap.impl_10__pop #v_T #Alloc.Alloc.t_Global other_side
              in
              let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global =
                tmp0
              in
              let (other: t_Order):t_Order =
                Core_models.Convert.f_into #v_T
                  #t_Order
                  #FStar.Tactics.Typeclasses.solve
                  (Core_models.Option.impl__unwrap #v_T out <: v_T)
              in
              let other:t_Order =
                { other with f_quantity = other.f_quantity -! m.f_quantity } <: t_Order
              in
              let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global =
                if other.f_quantity >. mk_u64 0
                then
                  let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global
                  =
                    Alloc.Collections.Binary_heap.impl_10__push #v_T
                      #Alloc.Alloc.t_Global
                      other_side
                      (Core_models.Convert.f_from #v_T
                          #t_Order
                          #FStar.Tactics.Typeclasses.solve
                          (Core_models.Clone.f_clone #t_Order #FStar.Tactics.Typeclasses.solve other
                            <:
                            t_Order)
                        <:
                        v_T)
                  in
                  other_side
                else other_side
              in
              let matches:Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global =
                Alloc.Vec.impl_1__push #t_Match #Alloc.Alloc.t_Global matches m
              in
              done, matches, order, other_side
              <:
              (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
                Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global)
            | _ ->
              let done:bool = true in
              done, matches, order, other_side
              <:
              (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
                Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global)
          else
            done, matches, order, other_side
            <:
            (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
              Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global))
  in
  let hax_temp_output:(Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
    Core_models.Option.t_Option t_Order) =
    matches,
    (if order.f_quantity >. mk_u64 0
      then Core_models.Option.Option_Some order <: Core_models.Option.t_Option t_Order
      else Core_models.Option.Option_None <: Core_models.Option.t_Option t_Order)
    <:
    (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core_models.Option.t_Option t_Order)
  in
  other_side, hax_temp_output
  <:
  (Alloc.Collections.Binary_heap.t_BinaryHeap v_T Alloc.Alloc.t_Global &
    (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core_models.Option.t_Option t_Order))
