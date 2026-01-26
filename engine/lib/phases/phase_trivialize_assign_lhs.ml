open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Nontrivial_lhs
    include Features.On.Construct_base
    include Features.On.Slice
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.Construct_base
      include Features.SUBTYPE.On.Slice
    end

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    [%%inline_defs dmutability + dsafety_kind]

    let rec updater_of_lhs (lhs : A.lhs) (rhs : B.expr) (span : span) :
        (Local_ident.t * B.ty) * B.expr =
      match lhs with
      | LhsLocalVar { var; typ } -> ((var, dty span typ), rhs)
      | LhsVecRef { e; _ } -> updater_of_lhs e rhs span
      | LhsFieldAccessor { e; field; _ } -> (
          let lhs = UA.expr_of_lhs span e |> dexpr in
          match lhs.typ with
          | TApp { ident; _ } ->
              let rhs =
                UB.M.expr_Construct ~constructor:ident
                  ~is_record:true (* TODO: might not be, actually *)
                  ~is_struct:true
                  ~fields:[ (field, rhs) ]
                  ~base:(Some (lhs, Features.On.construct_base))
                  ~span ~typ:lhs.typ
              in
              updater_of_lhs e rhs span
          | _ -> Error.raise { kind = ArbitraryLHS; span })
      | LhsArrayAccessor { e; typ = _; index; _ } ->
          let lhs = UA.expr_of_lhs span e |> dexpr in
          let update_at : Concrete_ident.name =
            let is_array_slice_or_vec =
              match lhs.typ with
              | TSlice _ | TArray _ -> true
              | TApp { ident; _ } -> Global_ident.eq_name Alloc__vec__Vec ident
              | _ -> false
            in
            if is_array_slice_or_vec then
              let index_typ =
                match index.typ with TRef { typ; _ } -> typ | _ -> index.typ
              in
              match index_typ with
              | TInt { size = SSize; signedness = Unsigned } ->
                  Rust_primitives__hax__monomorphized_update_at__update_at_usize
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__Range ident ->
                  Rust_primitives__hax__monomorphized_update_at__update_at_range
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__RangeFrom ident ->
                  Rust_primitives__hax__monomorphized_update_at__update_at_range_from
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__RangeTo ident ->
                  Rust_primitives__hax__monomorphized_update_at__update_at_range_to
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__RangeFull ident ->
                  Rust_primitives__hax__monomorphized_update_at__update_at_range_full
              | _ -> Rust_primitives__hax__update_at
            else Rust_primitives__hax__update_at
          in
          let vec_elem_type =
            match lhs.typ with
            | TApp { ident; args = [ GType inner; _ ] }
              when Global_ident.eq_name Alloc__vec__Vec ident ->
                Some inner
            | _ -> None
          in
          let vec_typ = lhs.typ in
          let lhs =
            match vec_elem_type with
            | Some ty ->
                UB.call Alloc__vec__Impl_1__as_slice [ lhs ] span
                  (TSlice { witness = Features.On.slice; ty })
            | None -> lhs
          in
          let rhs = UB.call update_at [ lhs; dexpr index; rhs ] span lhs.typ in
          let rhs =
            if Option.is_some vec_elem_type then
              UB.call Alloc__slice__Impl__to_vec [ rhs ] span vec_typ
            else rhs
          in

          updater_of_lhs e rhs span
      | LhsArbitraryExpr _ -> Error.raise { kind = ArbitraryLHS; span }

    and dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | Assign { lhs; e; witness } ->
          let (var, typ), inner_e = updater_of_lhs lhs (dexpr e) span in
          let lhs : B.lhs = LhsLocalVar { var; typ } in
          UB.M.expr_Assign ~lhs ~inner_e ~witness ~span ~typ:UB.unit_typ
      | [%inline_arms "dexpr'.*" - Assign] ->
          map (fun e -> B.{ e; typ = dty span expr.typ; span })
    [@@inline_ands bindings_of dexpr - dlhs - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]
