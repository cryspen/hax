// Tests on constants
#![allow(dead_code)]
#![allow(unused_variables)]

const C1: u32 = 5678;
const C2: u32 = C1 + 1;
const C3: u32 = if true { 890 } else { 9 / 0 };

const fn computation(x: u32) -> u32 {
    x + x + 1
}

const C4: u32 = computation(C1) + C2;

fn test() {
    let x = C1 + 1;
    let y = C2 + C3;
    let z = C4 - C3;
}

mod const_parameters {

    /// Function with const parameter
    fn f<const N: usize>() -> usize {
        N
    }

    const N0: usize = 1;
    const N1: usize = 10;

    fn test() {
        let _ = f::<9>() + f::<N1>();
    }

    /// Trait definition
    trait T<const N_TRAIT: usize> {
        fn f<const N_FIELD: usize>(&self) -> usize;
    }

    /// Struct definition
    struct S<const N: usize>(u32);

    impl<const N_TRAIT: usize> T<N_TRAIT> for S<N_TRAIT> {
        fn f<const N_FIELD: usize>(&self) -> usize {
            N_TRAIT - N_FIELD
        }
    }

    #[hax_lib::lean::before(
        "
/--
error: Application type mismatch: The argument
  s
has type
  S 10
but is expected to have type
  usize
in the application
  T.f 1 s
---
error: Application type mismatch: The argument
  x
has type
  A
but is expected to have type
  usize
in the application
  T.f 11 x
---
error: Application type mismatch: The argument
  x
has type
  A
but is expected to have type
  usize
in the application
  T.f 4 x
-/
#guard_msgs in"
    )]
    fn test2<const N2: usize, A: T<N2>>(x: A) -> usize {
        let s = S::<N1>(9);
        let _ = s.f::<1>() + x.f::<{ 1 + N1 }>();
        let s = S::<{ 1 + 2 }>(9);
        x.f::<{ 2 + 2 }>()
    }
}
