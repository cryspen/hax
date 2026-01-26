# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

Changes to the Rust Engine:

Changes to the frontend:

Changes to cargo-hax:

Changes to hax-lib:

Changes to the Lean backend:

Miscellaneous:

## 0.3.6

Changes to the Rust Engine:
 - Add a rejection phase for interleaving of expressions and statements not
   supported by the Lean do-notation syntax (#1739).
 - Add a phase to handle the monadic encoding: it explicitly introduces two new
   Hax primitives `pure` (to wrap values as monadic computations) and `lift` (to
   lift monadic computations into values) (#1746)
 - Add a mechanism to lookup pre- and post-conditions (#1805)

Changes to the frontend:
 - Update the pin of rustc (#1765)
 - Miscellaneous changes related to Charon (#1765)

Change to cargo-hax:

Changes to hax-lib:
 - Add Lean core models for options, results, default (#1747)
 - F* lib: improved while loops support, additions of some specific arithmetic operations and fixed `TryInto` for integer types (#1742)
 - Lean lib: use macros for int operations (#1795)
 - Lean lib: add new setup for `bv_decide` (#1828)
 - Lean lib: base specs on mathematical integers (#1829)
 - Lean lib: represent `usize` via a copy of `UInt64` (#1829)
 - Lean lib: Add support for while loops (#1857, #1863)
 - Lean lib: use Rust core models (#1865)
 - Lean lib: specs for negation (#1891)

Changes to the Lean backend:
 - Support for constants with arbitrary computation (#1738)
 - Add support for base-expressions of structs (#1736)
 - Use the explicit monadic phase to insert `pure` and `←` only on demand, and
   not introduce extra `do` block (#1746)
 - Rename `Result` monad to `RustM` to avoid confusion with Rust `Result` type (#1768)
 - Add support for shift-left (#1785)
 - Add support for default methods of traits (#1777)
 - Add support for floats (#1784)
 - Add support for pattern matching on constant literals (#1789)
 - Add support for binding subpatterns in match constructs (#1790)
 - Add error when using patterns in function parameters (#1792)
 - Add grind annotations for various lemmas in the Lean library (#1802)
 - Add support for constant parameters to functions and traits (#1797)
 - Add support for associated types with equality constraints (#1806)
 - Make trait-level arguments explicit for all trait functions, adding them as
   extra parameters (#1803)
 - Add generation of specs from requires/ensures-annotations (#1815)
 - Add support for nonliteral array sizes (#1826)
 - Add `hax_lib::lean::proof` attribute (#1831)
 - Add support for `#[hax_lib::opaque]` (#1846)
 - Turn rejection phase into a transformation phase (#1840)

Miscellaneous:
- Reserve extraction folder for auto-generated files in Lean examples (#1754)

## 0.3.5

Changes to the Rust Engine:
 - The module `names` now produces `ExplicitDefId`s instead of `DefId`s (#1648)
 - Add a resugaring `FunctionsToConstants` (#1559)
 - Drop the tuple nodes of the AST, add resugaring node for tuples (#1662)
 - Add support for enums and structs to the Lean backend (type definitions,
   expressions, pattern-matching) (#1623)
 - Update name rendering infrastructure in the Lean backend (#1623, #1624)
 - Printers now emit proper diagnostics (PR #1669)
 - Global identifiers are now interned (#1689)
 - Global identifiers are encapsulated properly, and provide easy destructuring as tuple identifiers (#1693)
 - Add support for `trait` and `impl` in the Lean backend (#1679): trait definitions, trait bounds
   on functions, impl definitions. The typeclass resolution in the generated code is left implicit
   (relies on Lean). Limited support for associated types. No support for default implementations.
 - Refactor of the printing infrastructure: lowers the boilerplate, get rid of most lifetimes annotation, add proper contextual span support (#1735)

Changes to the frontend:
- Add an explicit `Self: Trait` clause to trait methods and consts (#1559)
- Fix `ImplExpr::Builtin` that had some type errors (#1559)
- Improve the translation of `Drop` information (#1559)
- Add variance information to type parameters (#1559)
- Cleanup the `State` infrastructure a little bit (#1559)
- Add information about the metadata to use in unsize coercions (#1559)
- Resolve `dyn Trait` predicates (#1559)
- Many improvements to `FullDef` (#1559)
- Add infrastructure to get a monomorphized `FullDef`; this is used in charon to monomorphize a crate graph (#1559)
- Fix a regression affecting projection predicates (#1678)

Change to cargo-hax:
- Improve the caching of rustc when using `cargo hax` commands (#1719)
- Add hidden commands and flags to explicitly manipulate `haxmeta` files (#1722)

Changes to hax-lib:
- New behavior for `hax_lib::include`: it now forces inclusion when in contradiction with `-i` flag.
- hax-lib requires edition 2021 instead of 2024 (#1726)
- Improved `VecDeque` model in F* proof lib (#1728)
- Split the Lean library into several files, update to lean 4.23.0 (#1696)

Changes to the Lean backend:
- Improve support for functionalized loops (#1695)
- Improve error messages, having each error (coming from the Lean backend) point to a specific github issue (#1717).

Miscellaneous:
 - A lean tutorial has been added to the hax website (#1626)
 - Add end-to-end tests for the website (#1690)
 - Diagnostics reporting were improved (#1692)

## 0.3.4

The release of `0.3.3` got troubles because of the new Rust Engine crates.
This release is mostly empty.

## 0.3.3

Changes to the frontend:
 - A field `visibility` was added to HIR items (#1643)

Rust Engine:
 - A Lean backend was introduced (#1593, #1591, #1590, #1607)
 - The Rust engine was improved (#1624, #1603, #1600, #1585)
 - The F* backend has been improved (#1587, #1585)

## 0.3.2

Changes to the frontend:
 - Provide the `FnOnce` shim for closures (#1477)
 - Update pin of rustc (#1482)
 - Add `Ty::FnDef` (splitting `FnPtr` and `FnDef`) (#1487)
 - Regroup generic and trait arguments in a struct `ItemRef` (#1514)
 - Support trait aliases in `FullDef` (#1494)
 - Separate `{Add,Sub,Mul}Unchecked` and `{Add,Sub,Mul}` (#1513)
 - Our pin to rustc was updated (#1534)

Changes to the engine:
 - introduce an experimental Rust engine (#1501, #1502, #1504, #1505, #1518)

Changes the `hax-lib`:
 - Support hax octal and binary literals in the `int!` macro
 - F*: additions of integer function implementations (#1520)
 - F*: change the definition of the `Clone` tyepclass (#1552)


## 0.3.1 (2025-05-26)

Changes to `hax-lib`:
- Bug fix with PartialOrd in f* lib: [#1473](https://github.com/cryspen/hax/pull/1473)
- Move `proof-libs` into `hax-lib` to allow dependencies using crates.io

## 0.3.0 (2025-05-16)

Changes to `hax-lib`:
- Support for SMT patterns in lemmas: [#1428](https://github.com/cryspen/hax/pull/1428)
- While loop invariants and termination (`loop_decreases`): [#1375](https://github.com/cryspen/hax/pull/1375)
- Removal of deprecated dependencies: [#1385](https://github.com/cryspen/hax/pull/1385) and [#1394](https://github.com/cryspen/hax/pull/1394)
- Support for mathematical integers and logical propositions has been strengthened: [#1372](https://github.com/cryspen/hax/pull/1372), [#1352](https://github.com/cryspen/hax/pull/1352), [#1351](https://github.com/cryspen/hax/pull/1351)
- `hax_lib::BACKEND::replace_body`: [#1321](https://github.com/cryspen/hax/pull/1321)
- `hax_lib::decreases`: [#1342](https://github.com/cryspen/hax/pull/1342)

## 0.2.0 (2024-01-20)
 - Initial release
