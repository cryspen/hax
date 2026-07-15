# Examples

| Name               | Status of the F\* extraction |
| ------------------ | ---------------------------- |
| chacha20           | Typechecks                   |
| limited-order-book | Typechecks                   |
| sha256             | Lax-typechecks               |
| barrett            | Typechecks                   |
| kyber_compress     | Typechecks                   |

## How to generate the F\* code and typecheck it for the examples

<details>
  <summary><b>Requirements</b></summary>

  First, make sure to have hax installed in PATH. Then:

  * With Nix, `nix develop .#examples` setups a shell automatically for you.

  * Without Nix:
    1. install F* `v2025.10.06`<!---FSTAR_VERSION--> manually (see https://github.com/FStarLang/FStar/blob/master/INSTALL.md);
       1. make sure to have `fstar.exe` in PATH;
       2. or set the `FSTAR_HOME` environment variable.
    2. clone [Hacl*](https://github.com/hacl-star/hacl-star) somewhere;
    3. `export HACL_HOME=THE_DIRECTORY_WHERE_YOU_HAVE_HACL_STAR`.
</details>

To generate F\* code for all the example and then typecheck
everything, just run `make` in this directory.

Running `make` will run `make` in each example directory, which in
turn will generate F\* modules using hax and then typecheck those
modules using F\*.

Note the generated modules live in the
`<EXAMPLE>/proofs/fstar/extraction` folders.

## Coq

For those examples, we generated Coq modules without typechecking them.
The `<EXAMPLE>/proofs/coq/extraction` folders contain the generated Coq modules.

## Aeneas-Lean

For the Aeneas-Lean backend, we have three examples: `barrett`, `sha3`, and `loop_equivalence`.

### Barrett reduction

Barrett reduction allows to compute remainders without using divisions.
We prove that the code does not panic and that it correctly computes the remainder,
provided that the input is small enough.

The proof can be run as follows:
```sh
cd barrett/
make lean
```

This extracts the Rust code from `barrett/src/lib.rs` into
`examples/barrett/proofs/lean/Barrett/Extraction/Funs.lean`. The Lean proof can be found in
`examples/barrett/proofs/lean/Barrett/Verification.lean`.

### SHA-3

The SHA-3 example contains two small parts of two implementations of SHA-3.

The two parts that we consider are: 
- **Part 1** the `iota` function, and
- **Part 2** a single round of `keccak_f`.

The two implementations that we prove equivalent are:
- a realistic SHA-3 implementation taken from the `libcrux` library
- a reference implementation close to the official FIPS spec of the algorithm

Note that this is only a very small part of SHA-3. Some of the functions that are part of
a round of `keccak_f`, but that we ignore in this example are simply `unimplemented!()`.

The proofs can be run as follows:
```sh
cd sha3/
make
```

This extracts the Rust code from `sha3/src/lib.rs` into
`examples/sha3/proofs/lean/Sha3/Extraction/Funs.lean`. The Lean proof can be found in
`examples/sha3/proofs/lean/Sha3/Equivalence.lean`.

### Loop Equivalence

The loop equivalence example contains two artificially crafted functions that implement a loop
operating on an array in two different styles. We prove them to be equivalent.

The proofs can be run as follows:
```sh
cd loop_equivalence/
make
```

## Lean (legacy backend)

Three examples are fine-tuned to showcase the Lean backend: `barrett`,
`lean_chacha20`, and `adc`. For all of them, the lean extraction can be
obtained by running `cargo hax into legacy-lean`.

### Barrett

The *Barrett reduction* allows to compute remainders without using divisions. It
showcases arithmetic operations, conversions between integer types (namely `i32`
and `i64`). The Lean backend provides *panicking* arithmetic operations `+?`,
`-?`, etc, that panic on overflows.

For the Lean extracted code, we prove panic freedom with regards to those
arithmetic operations, and then we prove that the result is indeed the modulus
(as long as the absolute value of the input is lower than the bound
`BARRETT_R`). The proof is made via bit-blasting (using Lean's `bv_decide`). To
limit the computation time, the bound `BARRETT_R` was lowered compared to the
normal example in the `barrett` folder.

The proofs are backported in the rust code (in `barrett/src/lib.rs`): doing
`cargo hax into legacy-lean` extracts a valid lean file that contains the proof.

The proof can be run by doing (requires `lake`):

```sh
cd barrett/
make lean
```

### ADC (Addition with Carry)

The *ADC* (addition with carry) example verifies a 32-bit limb addition with
carry, a fundamental building block in multi-precision (bignum) arithmetic.
It uses `#[hax_lib::legacy_lean::after(...)]` to embed a Lean 4 correctness theorem
directly after the extracted function definition. The precondition and
postcondition are expressed as pure Lean propositions in a Hoare triple, and
the proof is fully automated via `hax_mvcgen` and Lean's `bv_decide`
bit-blasting procedure.

The verified property states that the 64-bit sum `a + b + carry_in` is correctly
split into a 32-bit sum and a 1-bit carry output.

The proof can be run by doing (requires `lake`):

```sh
cd adc/
make
```

### Chacha20

The Chacha20 example extracts to Lean, but requires a manual edit to be
wellformed. It showcases array, vector and slices accesses, as well as loops
(with loop invariants). For the Lean extracted code, we prove panic freedom,
which involves arithmetic on size of arrays.

This edit and the proofs of panic freedom can be found in
`lean_chacha20/proofs/lean/extraction/lean_chacha20_manual_edit.lean`.

The extraction (in `lean_chacha20.lean`) and rerun of the proofs (in
`lean_chacha20_manual_edit.lean`) can be done by doing (requires `lake`):

```sh
cd lean_chacha20/
make
```
