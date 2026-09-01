//! Model of `core::ptr` — the alignment types only, since the model has no raw
//! pointers. `alignment` is here because `alloc::layout::Layout` names it.
//!
//! Lean-only: F* drops this module via the Makefile's `-i` flags.
/// See [`std::ptr::Alignment`]
pub mod alignment {
    // Real `core` generates one variant per power of two on a 64-bit target,
    // with the alignment itself (`1 << n`) as the discriminant. The model drops
    // the discriminants — aeneas converts them with OCaml's `Z.to_int`, and
    // `1 << 62` already overflows a 63-bit int (`Z.Overflow` in
    // `SymbolicToPureTypes.translate_variant`) — which is also how Aeneas's own
    // Lean library declares this enum: 64 plain variants.
    macro_rules! alignment_enum {
        ($($n:literal),*) => {
            pastey::paste! {
                /// `core::ptr::alignment::AlignmentEnum`
                pub enum AlignmentEnum {
                    $(
                        #[doc = concat!("`AlignmentEnum::_Align1Shl", stringify!($n), "`")]
                        [<_Align1Shl $n>],
                    )*
                }
            }
        };
    }

    alignment_enum!(
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
        48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63
    );

    /// See [`std::ptr::Alignment`]
    ///
    /// A `repr(transparent)` newtype over [`AlignmentEnum`] in real `core` too;
    /// the model carries no operations, as Aeneas's does not either.
    pub struct Alignment(AlignmentEnum);
}
