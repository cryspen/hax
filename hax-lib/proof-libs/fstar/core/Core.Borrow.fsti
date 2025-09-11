module Core.Borrow

class t_Borrow (v_Self: Type0) (v_Borrowed: Type0) = {
    f_borrow_pre: v_Self -> Type0;
    f_borrow_post: v_Self -> v_Borrowed -> Type0;
    f_borrow: v_Self -> v_Borrowed
}
