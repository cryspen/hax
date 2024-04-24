use hax_lib as hax;

// dummy max value
const u32_max: u32 = 90000;

#[hax::requires(x > 10 && y > 10 && z > 10 && x + y + z < u32_max)]
#[hax::ensures(|result| hax_lib::implies(true, || result > 32))]
fn add3(x: u32, y: u32, z: u32) -> u32 {
    x + y + z
}

#[hax::lemma]
fn add3_lemma(x: u32) -> Proof<{ x <= 10 || x >= u32_max / 3 || add3(x, x, x) == x * 3 }> {}

#[hax::exclude]
pub fn f<'a, T>(c: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if c {
        x
    } else {
        y
    }
}

#[hax::attributes]
pub struct Foo {
    pub x: u32,
    #[refine(y > 3)]
    pub y: u32,
    #[refine(y + x + z > 3)]
    pub z: u32,
}

#[hax::exclude]
impl Foo {
    fn g(&self) {}
}

impl Foo {
    #[hax::exclude]
    fn h(&self) {}
}

#[hax::attributes]
mod refined_arithmetic {
    use core::ops::{Add, Mul};

    struct Foo(u8);

    impl Add for Foo {
        type Output = Foo;
        #[requires(self.0 < 255 - rhs.0)]
        fn add(self, rhs: Foo) -> Foo {
            Foo(self.0 + rhs.0)
        }
    }

    impl Mul for Foo {
        type Output = Foo;
        #[requires(rhs.0 == 0 || self.0 < 255 / rhs.0)]
        fn mul(self, rhs: Foo) -> Foo {
            Foo(self.0 * rhs.0)
        }
    }
}

mod refined_indexes {
    use hax_lib as hax;
    const MAX: usize = 10;
    struct MyArray(pub [u8; MAX]);

    #[hax::attributes]
    impl std::ops::Index<usize> for MyArray {
        type Output = u8;
        #[requires(index < MAX)]
        fn index(&self, index: usize) -> &Self::Output {
            &self[index]
        }
    }

    #[hax::exclude]
    impl std::ops::IndexMut<usize> for MyArray {
        fn index_mut(&mut self, index: usize) -> &mut Self::Output {
            &mut self[index]
        }
    }

    fn mutation_example(
        use_generic_update_at: &mut MyArray,
        use_specialized_update_at: &mut [u8],
        specialized_as_well: &mut Vec<u8>,
    ) {
        use_generic_update_at[2] = 0;
        use_specialized_update_at[2] = 0;
        specialized_as_well[2] = 0;
    }
}
mod newtype_pattern {
    use hax_lib as hax;

    const MAX: usize = 10;
    #[hax::attributes]
    struct SafeIndex {
        #[refine(i < MAX)]
        i: usize,
    }
    impl SafeIndex {
        fn new(i: usize) -> Option<Self> {
            if i < MAX {
                Some(Self { i })
            } else {
                None
            }
        }
        fn as_usize(&self) -> usize {
            self.i
        }
    }

    impl<T> std::ops::Index<SafeIndex> for [T; MAX] {
        type Output = T;
        fn index(&self, index: SafeIndex) -> &Self::Output {
            &self[index.i]
        }
    }
}

#[hax::fstar::before(r#"let before_${inlined_code} = "example before""#)]
#[hax::fstar::after(r#"let ${inlined_code}_after = "example after""#)]
fn inlined_code(foo: Foo) {
    const V: u8 = 12;
    let v_a = 13;
    hax::fstar!(
        r"let x = ${foo.x} in
          let $?{Foo {y, ..}} = $foo in
          $add3 ((fun _ -> 3ul) $foo) $v_a $V y
        "
    );
}

#[hax::fstar::replace(r#"unfold let $some_function _ = "hello from F*""#)]
fn some_function() -> String {
    String::from("hello from Rust")
}

/// An minimal example of a model of math integers for F*
mod int_model {
    use super::hax;
    #[hax::fstar::replace(r#"unfold type $:{Int} = int"#)]
    #[derive(Copy, Clone)]
    struct Int(u128);

    #[hax::fstar::replace(r#"unfold let ${add} x y = x + y"#)]
    fn add(x: Int, y: Int) -> Int {
        Int(x.0 + y.0)
    }

    use std::ops::Sub;
    #[hax::fstar::replace(
        r#"
unfold instance impl: Core.Ops.Arith.t_Sub $:Int $:Int =
  {
    f_Output = $:Int;
    f_sub_pre = (fun (self: $:Int) (other: $:Int) -> true);
    f_sub_post = (fun (self: $:Int) (other: $:Int) (out: $:Int) -> true);
    f_sub = fun (self: $:Int) (other: $:Int) -> self + other
  }
"#
    )]
    impl Sub for Int {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self(self.0 + other.0)
        }
    }
}
