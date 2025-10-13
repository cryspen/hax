//! Tests on structs
#![allow(dead_code)]
#![allow(unused_variables)]

// # Tuple Structs

// 1. Type definitions
struct T0();
struct T1<A>(A);
struct T2<A, B>(A, B);
struct T3<A, B, C>(A, B, C);
struct T3p<A, B, C>(A, T2<B, C>);

fn tuple_structs() -> () {
    // 2. Expressions
    let t0 = T0();
    let t1 = T1(1);
    let t2 = T2(1, 2);
    let t3 = T3(T0(), T1(1), T2(1, 2));
    let t3p = T3p(T0(), T2(T1(1), T2(1, 2)));

    // 3. Patterns
    let T0() = t0;
    let T1(u1) = t1;
    let T2(u2, u3) = t2;
    let T3(T0(), T1(_), T2(_, _)) = t3;
    let T3p(T0(), T2(T1(_), T2(_, _))) = t3p;

    // 4. Accessors
    let _ = t1.0;
    let _ = t2.0;
    let _ = t2.1;
    let _ = t3.0;
    let _ = t3.1;
    let _ = t3.2;
    let _ = t3.2.1;
    let _ = t3p.0;
    let _ = t3p.1;
    let _ = t3p.1.1.0;
    let _ = t3p.1.0;
    let _ = t3p.1.1;

    // 5. Pattern matching
    let _ = match t0 {
        T0() => {}
    };
    let _ = match t1 {
        T1(u1) => {}
    };
    let _ = match t2 {
        T2(u2, u3) => {}
    };
    let _ = match t3 {
        T3(T0(), T1(u1), T2(u2, u3)) => {}
    };
    let _ = match t3p {
        T3p(T0(), T2(T1(u1), T2(u2, u3))) => {}
    };
}

// # Normal Structs

// 1. Type definitions
struct S1 {
    f1: usize,
    f2: usize,
}

struct S2 {
    // Nested structs
    f1: S1, // possible shadowing between fields
    f2: usize,
}

struct S3 {
    // Reserved keywords in Lean
    end: usize,
    def: usize,
    theorem: usize,
    structure: usize,
    inductive: usize,
}

fn normal_structs() -> () {
    // 2. Expressions
    let s1 = S1 { f1: 0, f2: 1 };
    let s2 = S2 {
        f1: S1 { f1: 2, f2: 3 },
        f2: 4,
    };
    let s3 = S3 {
        end: 0,
        def: 0,
        theorem: 0,
        structure: 0,
        inductive: 0,
    };

    // 3. Patterns
    let S1 { f1, f2 } = s1;
    let S1 {
        f1,
        f2: other_name_for_f2,
    } = s1;
    let S2 {
        f1: S1 { f1, f2 },
        f2: other_name_for_f2,
    } = s2;
    let S3 {
        end,
        def,
        theorem,
        structure,
        inductive,
    } = s3;

    // 4. Accessors
    let _ = (s1.f1, s1.f2);
    let _ = (
        s1.f1, s1.f2, s2.f1.f1, s2.f1.f2, s2.f2, s3.end, s3.def, s3.theorem,
    );

    // 5. Pattern-matching
    match s1 {
        S1 { f1, f2 } => {}
    };
    match s2 {
        S2 {
            f1: S1 {
                f1,
                f2: other_name_for_f2,
            },
            f2,
        } => {}
    }
    match s3 {
        S3 {
            end,
            def,
            theorem,
            structure,
            inductive,
        } => {}
    }
}

mod miscellaneous {
    struct S {
        f: i32,
    }

    fn test_tuples() -> (i32, i32) {
        let lit = 1;
        let constr = S { f: 42 };
        let proj = constr.f;
        let ite = if true {
            (1, 2)
        } else {
            let z = 1 + 2;
            (z, z)
        };
        (1, 2)
    }
}

mod base_expressions {

    struct S {
        f1: u32,
        f2: u32,
        f3: u32,
    }

    fn test() {
        let s1 = S {
            f1: 1,
            f2: 2,
            f3: 3,
        };
        let _ = S { f1: 0, ..s1 };
        let _ = S { f2: 0, ..s1 };
        let _ = S { f3: 0, ..s1 };
        let _ = S { f1: 0, f2: 1, ..s1 };
        let _ = S { f2: 0, f3: 1, ..s1 };
        let _ = S { f3: 0, f1: 2, ..s1 };
        let _ = S {
            f1: 0,
            f2: 1,
            f3: 0,
            ..s1
        };
    }
}
