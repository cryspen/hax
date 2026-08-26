//! @off: fstar, lean, coq, ssprove
//! @fail(extraction): proverif(HAX0008)
//!
//! A field projection reduces only on its constructor. Applied to an opaque
//! associated constant, which has no constructor, it can never reduce, so the
//! projection is flagged. Projecting a bound value reduces normally.

struct Tag(u32);

impl Tag {
    const DEFAULT: Tag = Tag(0);
}

fn dead_projection() -> u32 {
    Tag::DEFAULT.0
}

fn live_projection(t: Tag) -> u32 {
    t.0
}
