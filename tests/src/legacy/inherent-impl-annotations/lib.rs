//! Tests for issue #1698: hax_lib annotations on inherent `impl` blocks and on
//! their items.
//! @off: coq, ssprove, proverif, legacy-lean

struct OnMethod;

// Annotations on an item of an inherent `impl` block used to expand to an
// unnamed `const _`, which is illegal in associated item position.
impl OnMethod {
    #[hax_lib::fstar::options("--z3rlimit 111")]
    fn annotated_method() -> u8 {
        0
    }

    #[hax_lib::fstar::before(r#"let before_method = "before method""#)]
    #[hax_lib::fstar::after(r#"let after_method = "after method""#)]
    fn quoted_method() -> u8 {
        1
    }
}

struct OnBlock;

// `before` lands before the first item, `after` after the last one.
#[hax_lib::fstar::before(r#"let before_block = "before block""#)]
#[hax_lib::fstar::after(r#"let after_block = "after block""#)]
impl OnBlock {
    fn first() -> u8 {
        0
    }
    fn second() -> u8 {
        1
    }
}

struct OnBlockOptions;

// `options` expands to a `before` and an `after`, hence it scopes over the
// whole block.
#[hax_lib::fstar::options("--z3rlimit 222")]
impl OnBlockOptions {
    fn first() -> u8 {
        0
    }
    fn second() -> u8 {
        1
    }
}

struct OnBlockWithConst;

#[hax_lib::fstar::options("--z3rlimit 333")]
impl OnBlockWithConst {
    const C: u8 = 3;
    fn f() -> u8 {
        Self::C
    }
}
