module Core.Ops.Drop

class t_Drop (v_Self: Type) = {
  f_drop_pre : v_Self -> Type;
  f_drop_post : v_Self -> v_Self -> Type;
  f_drop : v_Self -> v_Self;
}
