fn g(x: u8, y: u8) {}

struct Foo;

fn f<T>(x: Foo, y: &mut u8, z: T) -> u8 {
    let xx: T = z;
    if true {
        g(123, 45);
        *y = 3;
        1
    } else {
        if true {};
        let (_, _, _) = ("hello", 12u32, ());
        let arr = [1u8, 2, 4];
        let _ = &arr[..];
        let _ = &(8u8 as u8);
        let mut x = 0;
        for i in [1, 2, 3] {
            if true {
                continue;
            }
            break;
        }
        let aa = |x: u8, y: u64| 33u8;
        x = 3;
        match 0 {
            1 => 0,
            2 => 1,
            3 => return 3,
            _ => 32,
        }
    }
}
