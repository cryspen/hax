//! @fail(tc): lean(1)
//! @fail(tc): fstar(134)
// `initialize_symmetric(&Noise_KKpsk0_..._SHA256.0)` projects field 0 of an
// opaque associated constant. The accessor reduces only on its constructor, so
// the projection is dead and the two initiate/respond entry points cannot
// complete. Flagged by the projection-on-constant check.
//! @fail(extraction): proverif(HAX0008, HAX0008)

pub mod noise_crypto;
pub mod noise_kkpsk0;
pub mod noise_lib;
