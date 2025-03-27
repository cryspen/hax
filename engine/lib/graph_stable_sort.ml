(* This is a modified version of the stable topological sort from the ocamlgraph library *)
(* The original code is distributed under the terms of the GNU Library General Public    *)
(* License version 2.1 and was developed by Sylvain Conchon, Jean-Christophe Filliatre   *)
(* and Julien Signoles. More information in the LICENSE file that can be found here:     *)
(* https://github.com/backtracking/ocamlgraph/blob/master/LICENSE                        *)

module type G = sig
  type t

  module V : Graph.Sig.COMPARABLE

  val iter_vertex : (V.t -> unit) -> t -> unit
  val iter_succ : (V.t -> unit) -> t -> V.t -> unit
end

module Make_stable (G : sig
  include G

  val in_degree : t -> V.t -> int
end) =
struct
  module H = Hashtbl.Make (G.V)
  module C = Graph.Path.Check (G)

  let choose ~old ((v, n) : G.V.t * int) =
    let l, min = old in
    if n = min then (v :: l, n) else if n < min then ([ v ], n) else old

  module Q = struct
    module S = Set.Make (G.V)

    let create () = ref S.empty
    let push v s = s := S.add v !s

    let pop s =
      let r = S.min_elt !s in
      s := S.remove r !s;
      r

    let is_empty s = S.is_empty !s

    let choose ~old new_ =
      let l, n = choose ~old new_ in
      (List.sort G.V.compare l, n)
  end

  (* in case of multiple cycles, choose one vertex in a cycle which
     does not depend of any other. *)
  let find_top_cycle checker vl =
    (* choose [v] if each other vertex [v'] is in the same cycle
       (a path from v to v') or is in a separate component
       (no path from v' to v).
       So, if there is a path from v' to without any path from v to v',
       discard v. *)
    let on_top_cycle v =
      List.for_all
        (fun v' ->
          G.V.equal v v' || C.check_path checker v v'
          || not (C.check_path checker v' v))
        vl
    in
    List.filter on_top_cycle vl

  let fold f g acc =
    let checker = C.create g in
    let degree = H.create 97 in
    let todo = Q.create () in
    let push x =
      H.remove degree x;
      Q.push x todo
    in
    let add_vertex acc v =
      G.iter_succ
        (fun x ->
          try
            let d = H.find degree x in
            if d = 1 then push x else H.replace degree x (d - 1)
          with Not_found -> (* [x] already visited *)
                            ())
        g v;
      f v acc
    in
    let rec walk acc =
      if Q.is_empty todo then (
        (* let's find any node of minimal degree *)
        let min, _ =
          H.fold (fun v d old -> Q.choose ~old (v, d)) degree ([], max_int)
        in
        match min with
        | [] -> acc
        | _ ->
            let vl = find_top_cycle checker min in
            List.iter (H.remove degree) vl;
            let acc = List.fold_left add_vertex acc vl in
            (* let v = choose_independent_vertex checker min in push v; *)
            walk acc)
      else
        let v = Q.pop todo in
        let acc = add_vertex acc v in
        walk acc
    in
    G.iter_vertex
      (fun v ->
        let d = G.in_degree g v in
        if d = 0 then Q.push v todo else H.add degree v d)
      g;
    walk acc

  let iter f g = fold (fun v () -> f v) g ()
end
