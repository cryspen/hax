type t [@@deriving show, yojson, compare, sexp, eq, hash]

type name = Concrete_ident_generated.t
[@@deriving show, yojson, compare, sexp, eq, hash]

module ImplInfoStore : sig
  val init : (Types.def_id * Types.impl_infos) list -> unit
end

module Kind : sig
  type t =
    | Type
    | Value
    | Lifetime
    | Constructor of { is_struct : bool }
    | Field
    | Macro
    | Trait
    | Impl
    | AssociatedItem of t
  [@@deriving show, yojson, compare, sexp, eq, hash]
end

val of_def_id : Kind.t -> Types.def_id -> t
val of_name : Kind.t -> name -> t
val eq_name : name -> t -> bool
val to_debug_string : t -> string

module Create : sig
  val fresh_module : from:t list -> t
  val move_under : new_parent:t -> t -> t

  val map_last : f:(string -> string) -> t -> t
  (** [map_last f ident] applies [f] on the last chunk of [ident]'s
      path if it holds a string *)
end

type view = { crate : string; path : string list; definition : string }

val map_path_strings : f:(string -> string) -> t -> t
val matches_namespace : Types.namespace -> t -> bool

include module type of struct
  include Concrete_ident_sig.Make (struct
    type t_ = t
    type view_ = view
  end)
end

module MakeViewAPI (NP : NAME_POLICY) : VIEW_API
module DefaultNamePolicy : NAME_POLICY
module DefaultViewAPI : VIEW_API

type comparator_witness

val comparator : (t, comparator_witness) Base.Comparator.comparator

val lookup_raw_impl_info : t -> Types.impl_infos option
(** Lookup the (raw[1]) implementation informations given a concrete
ident. Returns `Some _` if and only if the supplied identifier points
to an `Impl`.

[1]: those are raw THIR types.

{b WARNING}: due to {{: https://github.com/hacspec/hax/issues/363}
issue 363}, when looking up certain identifiers generated by the
engine, this function may return [None] even though the supplied
identifier points to an [Impl] block. *)

val parent_impl : t -> t option
(** Returns the identifier pointing to the parent `impl` block, if it
exists. *)
