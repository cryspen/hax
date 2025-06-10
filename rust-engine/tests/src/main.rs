/*
mod my_mod {
    pub fn index(index: usize, values: &[u8]) -> u8 {
        values[index]
    }
}

fn my_main() {
    let values = [1u8, 2, 3];
    my_mod::index(1, &values);
}

fn pattern_matching() -> u8 {
    match 1 {
        1 => 1 + 1,
        _ => 1 - 1,
    }
} */

fn main() {}

fn generic<A, const N: usize>(x: A) -> A {
    if N > 1 {
        x
    } else {
        x
    }
}

fn test_expr() {
    // box
    // TODO
    // if
    assert_eq!(if true { 0 } else { 1 }, 0);
    assert_eq!(if false { 0 } else { 1 }, 1);
    // call
    assert_eq!(generic::<usize, 3>(1), 1);
    // deref
    let reference = &1;
    assert_eq!(*reference, 1);
    // binary
    assert_eq!(1 + 1, 2);
    //assert_eq!(1_i32.wrapping_add(1), 2);
    assert_eq!(0b101 & 0b110, 0b100);
    assert_eq!(0b101 | 0b110, 0b111);
    assert_eq!(0b101 ^ 0b110, 0b11);
    assert_eq!(1.cmp(&2), std::cmp::Ordering::Less);
    assert_eq!(1.cmp(&1), std::cmp::Ordering::Equal);
    assert_eq!(2.cmp(&1), std::cmp::Ordering::Greater);
    assert_eq!(4 / 2, 2);
    assert_eq!(5 == 6, false);
    assert_eq!(5 == 5, true);
    assert_eq!(5 >= 5, true);
    assert_eq!(6 >= 7, false);
    assert_eq!(6 > 5, true);
    assert_eq!(6 > 6, false);
    assert_eq!(5 <= 5, true);
    assert_eq!(8 <= 7, false);
    assert_eq!(6 < 7, true);
    assert_eq!(6 < 6, false);
    assert_eq!(6 * 7, 42);
    //assert_eq!(6_i32.wrapping_mul(7), 42);
    assert_eq!(5 != 6, true);
    assert_eq!(6 != 6, false);
    // TODO offset
    assert_eq!(7 % 2, 1);
    assert_eq!(0b10 << 1, 0b100);
    assert_eq!(0b10 >> 1, 0b1);
    assert_eq!(2 - 1, 1);
    //assert_eq!(2_i32.wrapping_sub(1), 1);
    // Logical op
    assert_eq!(true && true, true);
    assert_eq!(true && false, false);
    assert_eq!(true || false, true);
    assert_eq!(false || false, false);
    // Unary
    assert_eq!(-2, 0 - 2);
    assert_eq!(!true, false);
    // TODO cast
    // TODO Use
    // TODO NeverToAny
    // TODO PointerCoercion
    // loop + break
    assert_eq!(
        loop {
            break 1;
        },
        1
    );
    // continue
    /* assert_eq!(
        {
            let mut i = 0;
            loop {
                if i < 5 {
                    i += 1;
                    continue;
                } else {
                    break;
                }
            }
            i
        },
        5
    ); */
    // TODO Match
    // Block
    assert_eq!({ 1 }, 1);
    // Assign
    /* assert_eq!(
        {
            let mut x = 1;
            x = 2;
            x
        },
        2
    ); */
    // AssignOp
    /* assert_eq!(
        {
            let mut x = 1;
            x += 1;
            x
        },
        2
    ); */
    // TODO field
    // TODO VarRef
    // TODO ConstRef
    // TODO GlobalName
    // TODO UpvarRef
    // borrow
    assert_eq!(&1, &1);
    // TODO RawBorrow
    // Return
    fn f_return(x: u8) -> u8 {
        if x > 10 {
            return 0;
        };
        x
    }
    assert_eq!(f_return(100), 0);
    // TODO ConstBlock
    // TODO Repeat
    // Array + index
    assert_eq!([1, 3, 5][2], 5);
    // Tuple + tuple field
    assert_eq!((1, 3, 5).2, 5);
    // Adt
    //assert_eq!(Option::Some(1).unwrap(), 1);
    // TODO Place and Value type ascription
    // Closure
    /* assert_eq!(
        {
            let f = |x| x;
            f(1)
        },
        1
    ); */
    // TODO Literal (apart from int and bool)
    // TODO ZstLiteral
    // TODO Named const
    // TODO static ref
    // TODO Yield
}

// and or tuple_field
