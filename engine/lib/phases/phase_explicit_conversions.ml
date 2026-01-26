open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      module A = Ast.Make (F)
      module UA = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module Attrs = Attr_payloads.MakeBase (Error)

      let explicit_conversions =
        object
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match super#visit_expr () e with
            | {
             e =
               App
                 {
                   f = { e = GlobalVar f; _ };
                   args = [ ({ typ = TApp { ident; _ }; _ } as inner) ];
                   _;
                 };
             typ = TSlice _ as t;
             span;
            }
              when Ast.Global_ident.eq_name Core__ops__deref__Deref__deref f
                   && Ast.Global_ident.eq_name Alloc__vec__Vec ident ->
                UA.call Alloc__vec__Impl_1__as_slice [ inner ] span t
            | e -> e

          (* Option.value ~default:e 
            (
              let* _ = e.typ  in
              let* e = UA.Expect.concrete_app1 Core__ops__deref__Deref__deref e in 
              let e = UA.call Alloc__vec__Impl_1__as_slice [e] e.span e.typ in
              Some e
            ) *)
          (* match e with
            | {
             e = Borrow { e = { typ = TApp { ident; _ }; _ } as inner; _ };
             typ = TSlice _;
             _;
            }
              when Ast.Global_ident.eq_name Alloc__vec__Vec ident ->
                inner
            | _ -> super#visit_expr () e *)
        end

      let ditems = List.map ~f:(explicit_conversions#visit_item ())
    end)
