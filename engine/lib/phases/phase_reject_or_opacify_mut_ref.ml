open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let mentions_mut_ref =
        object
          inherit [_] Visitors.reduce as super
          method zero = false
          method plus = ( || )

          method! visit_ty () t =
            match t with
            | TRef { mut = Mutable _; _ } -> true
            | _ -> super#visit_ty () t
        end

      let count_mut_ref =
        object
          inherit [_] Visitors.reduce as super
          method zero = 0
          method plus = ( + )

          method! visit_ty () t =
            match t with
            | TRef { mut = Mutable _; _ } -> 1 + super#visit_ty () t
            | _ -> super#visit_ty () t
        end

      (* A local bound to two or more aliased [&mut] values: what [split_at_mut]
         and friends produce, and what [Direct_and_mut]'s place analysis diverges
         on. A single [&mut] binding (a reborrow of a [&mut] parameter, or a place
         passed as [&mut _]) is left to the functionalization, which handles it. *)
      let binds_aliased_mut_ref =
        object
          inherit [_] Visitors.reduce as super
          method zero = false
          method plus = ( || )
          method! visit_pat () p = count_mut_ref#visit_ty () p.typ >= 2 || super#visit_pat () p
        end

      let exclude (item : item) : item =
        try
          Error.unimplemented ~issue_id:420
            ~details:
              "This function returns a mutable reference, which the backend \
               cannot state; the item is excluded."
            item.span
        with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
          let error = Diagnostics.pretty_print_context_kind context kind in
          let cast_item : item -> Ast.Full.item = Stdlib.Obj.magic in
          let ast = cast_item item |> Print_rust.pitem_str in
          let msg = error ^ "\nLast available AST for this item:\n\n" ^ ast in
          make_hax_error_item item.span item.ident msg

      let ditems =
        List.map ~f:(fun (item : item) ->
            match item.v with
            | Fn { body; _ } when mentions_mut_ref#visit_ty () body.typ ->
                exclude item
            | Fn { name; generics; params; safety; body }
              when binds_aliased_mut_ref#visit_expr () body ->
                let dropped =
                  let open Concrete_ident_generated in
                  Ast.Global_ident.of_name ~value:true
                    Rust_primitives__hax__dropped_body
                in
                let body = { body with e = GlobalVar dropped } in
                {
                  item with
                  v = Fn { name; generics; params; safety; body };
                  attrs = Attr_payloads.to_attr Types.Erased item.span :: item.attrs;
                }
            | _ -> item)
    end)
