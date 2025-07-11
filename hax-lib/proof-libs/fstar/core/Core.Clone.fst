module Core.Clone

class t_Clone self = {
  f_clone_pre: self -> Type0;
  f_clone_post: self -> self -> Type0;
  f_clone: x:self -> r:self {x == r}
}

(** Everything is clonable *)
instance clone_all (t: Type): t_Clone t = {
  f_clone_pre = (fun _ -> True);
  f_clone_post = (fun _ _ -> True);
  f_clone = (fun x -> x);
}

