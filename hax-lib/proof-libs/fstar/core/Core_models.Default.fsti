module Core_models.Default
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_Default (v_Self: Type0) = {
  f_default_pre:x: Prims.unit
    -> pred:
      Type0
        { (let _:Prims.unit = x in
            true) ==>
          pred };
  f_default_post:Prims.unit -> v_Self -> Type0;
  f_default:x0: Prims.unit
    -> Prims.Pure v_Self (f_default_pre x0) (fun result -> f_default_post x0 result)
}
