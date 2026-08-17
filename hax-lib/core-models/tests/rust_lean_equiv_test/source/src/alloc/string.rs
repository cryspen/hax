//! Equivalence tests for `alloc::string::*`.
//!
//! Mirrors the proptest cases in `alloc/src/lib.rs` (module `string::tests`),
//! pinning each observation on a concrete input.
//!
//! TODO(lean-string-model): every test below is commented out, and none of them
//! can be enabled yet.
//!
//! `alloc_models::string::*` and `{impl alloc_models::string::String}::*` are in
//! `ALLOC_CHARON_EXCLUDES` (see the top-level `Makefile`), so the Lean side of
//! this module is whatever is hand-written in
//! `../proof-libs/lean/CoreModels/RustPrimitives/Funs.lean` — and that is only
//! `alloc.string.String.new`. A test that mentions any other method extracts to
//! a reference to a Lean constant that does not exist, which breaks the Lake
//! build outright; `skip_lean` cannot rescue that (it only suppresses the
//! `#guard`, not the extraction of the test body). So the tests wait here until
//! the Lean counterparts exist, at which point uncommenting them is the whole
//! job.
//!
//! Until then the Rust↔std agreement of these items is covered by the
//! `proptest!` suite in the model crate.

// ----- new -------------------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_new_is_empty() -> bool {
//     let s = String::new();
//     s.is_empty() && s.len() == 0
// }

// ----- with_capacity / try_with_capacity -------------------------------------

// #[rust_lean_test]
// pub fn test_string_with_capacity_is_empty() -> bool {
//     let s = String::with_capacity(10);
//     s.is_empty() && s.capacity() >= s.len()
// }

// ----- len / is_empty --------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_len_ascii() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     s.len() == 3
// }

// `é` is two bytes, so `len` (bytes) and the char count disagree here.
// #[rust_lean_test]
// pub fn test_string_len_multibyte() -> bool {
//     let mut s = String::new();
//     s.push('é');
//     s.len() == 2
// }

// ----- push / push_str -------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_push_str_concatenates() -> bool {
//     let mut s = String::new();
//     s.push_str("ab");
//     s.push_str("cd");
//     s.as_str() == "abcd"
// }

// #[rust_lean_test]
// pub fn test_string_push_empty_str() -> bool {
//     let mut s = String::new();
//     s.push_str("");
//     s.is_empty()
// }

// ----- pop -------------------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_pop_empty() -> bool {
//     let mut s = String::new();
//     s.pop().is_none()
// }

// #[rust_lean_test]
// pub fn test_string_pop_last_char() -> bool {
//     let mut s = String::new();
//     s.push_str("ab");
//     s.pop() == Some('b') && s.as_str() == "a"
// }

// #[rust_lean_test]
// pub fn test_string_pop_multibyte() -> bool {
//     let mut s = String::new();
//     s.push_str("aé");
//     s.pop() == Some('é') && s.as_str() == "a"
// }

// ----- as_str / as_bytes / into_bytes ----------------------------------------

// #[rust_lean_test]
// pub fn test_string_as_bytes_len() -> bool {
//     let mut s = String::new();
//     s.push_str("aé");
//     s.as_bytes().len() == 3
// }

// #[rust_lean_test]
// pub fn test_string_into_bytes_first() -> bool {
//     let mut s = String::new();
//     s.push_str("ab");
//     let b = s.into_bytes();
//     b.len() == 2
// }

// ----- clear -----------------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_clear() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     s.clear();
//     s.is_empty()
// }

// ----- truncate --------------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_truncate_zero() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     s.truncate(0);
//     s.is_empty()
// }

// #[rust_lean_test]
// pub fn test_string_truncate_past_end_is_noop() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     s.truncate(10);
//     s.as_str() == "abc"
// }

// ----- split_off -------------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_split_off_middle() -> bool {
//     let mut s = String::new();
//     s.push_str("abcd");
//     let tail = s.split_off(2);
//     s.as_str() == "ab" && tail.as_str() == "cd"
// }

// #[rust_lean_test]
// pub fn test_string_split_off_at_end() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     let tail = s.split_off(3);
//     s.as_str() == "abc" && tail.is_empty()
// }

// ----- insert / insert_str ---------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_insert_str_front() -> bool {
//     let mut s = String::new();
//     s.push_str("cd");
//     s.insert_str(0, "ab");
//     s.as_str() == "abcd"
// }

// #[rust_lean_test]
// pub fn test_string_insert_char_at_end() -> bool {
//     let mut s = String::new();
//     s.push_str("ab");
//     s.insert(2, 'c');
//     s.as_str() == "abc"
// }

// ----- remove ----------------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_remove_first() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     s.remove(0) == 'a' && s.as_str() == "bc"
// }

// `é` occupies bytes 1..3, so removing at byte 1 removes the whole char.
// #[rust_lean_test]
// pub fn test_string_remove_multibyte() -> bool {
//     let mut s = String::new();
//     s.push_str("aéb");
//     s.remove(1) == 'é' && s.as_str() == "ab"
// }

// ----- retain ----------------------------------------------------------------

// TODO(closure-extraction): `String::retain` is `#[hax_lib::opaque]` — the
// model's `Fn*` traits do not expose the closure's `Output` type, so a called
// closure does not survive extraction.

// ----- capacity / reserve / shrink -------------------------------------------

// The model's capacity is exactly its length, so only std's `capacity() >=
// len()` guarantee is observable (see `String::capacity`).
// #[rust_lean_test]
// pub fn test_string_reserve_keeps_contents() -> bool {
//     let mut s = String::new();
//     s.push_str("abc");
//     s.reserve(100);
//     s.shrink_to_fit();
//     s.as_str() == "abc" && s.capacity() >= s.len()
// }

// ----- from_utf8 / from_utf8_lossy / FromUtf8Error ---------------------------

// #[rust_lean_test]
// pub fn test_string_from_utf8_valid() -> bool {
//     let mut v: Vec<u8> = Vec::new();
//     v.push(97);
//     v.push(98);
//     match String::from_utf8(v) {
//         Ok(s) => s.as_str() == "ab",
//         Err(_) => false,
//     }
// }

// `0xff` starts no valid UTF-8 sequence, so the bytes come back untouched.
// #[rust_lean_test]
// pub fn test_string_from_utf8_invalid() -> bool {
//     let mut v: Vec<u8> = Vec::new();
//     v.push(255);
//     match String::from_utf8(v) {
//         Ok(_) => false,
//         Err(e) => e.as_bytes().len() == 1,
//     }
// }

// ----- ToString --------------------------------------------------------------

// TODO(display-model): `ToString`'s blanket impl is `#[hax_lib::opaque]` (the
// model cannot run a `Display` implementation), so there is nothing to observe.

// ----- into_boxed_str --------------------------------------------------------

// #[rust_lean_test]
// pub fn test_string_into_boxed_str() -> bool {
//     let mut s = String::new();
//     s.push_str("ab");
//     &*s.into_boxed_str() == "ab"
// }
