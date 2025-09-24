module Core_models.Hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_Hasher (v_Self: Type0) = { __marker_trait_t_Hasher:Prims.unit }

class t_Hash (v_Self: Type0) = {
  f_hash_pre:#v_H: Type0 -> {| i0: t_Hasher v_H |} -> self_: v_Self -> h: v_H
    -> pred: Type0{true ==> pred};
  f_hash_post:#v_H: Type0 -> {| i0: t_Hasher v_H |} -> v_Self -> v_H -> v_H -> Type0;
  f_hash:#v_H: Type0 -> {| i0: t_Hasher v_H |} -> x0: v_Self -> x1: v_H
    -> Prims.Pure v_H (f_hash_pre #v_H #i0 x0 x1) (fun result -> f_hash_post #v_H #i0 x0 x1 result)
}
