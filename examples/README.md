# Examples

## Lean

For the Lean backend, we have three examples: `barrett`, `sha3`, and `loop_equivalence`.

### Barrett reduction

Barrett reduction allows to compute remainders without using divisions. It
showcases arithmetic operations, conversions between integer types (namely `i32`
and `i64`).
We prove that the code does not panic and that it correctly computes the remainder,
provided that the input is small enough.

The extraction and proofs can be run as follows:
```sh
cd barrett/
make lean
```

This extracts the Rust code from `barrett/src/lib.rs` into
`examples/barrett/proofs/lean/Barrett/Extraction/`. The Lean proof can be found in
`examples/barrett/proofs/lean/Barrett/Proofs/`.

### SHA-3

The SHA-3 example contains two small parts of a real-world implementation of SHA-3.
It also contains a Rust specification of these two parts, closely following the
official FIPS standard of the algorithm.

The example showcases array access, bit vector arithmetic, how
to prove equivalence to a specification, and how to verify nested
functions one by one.

The two parts that we consider are: 
- **Part 1:** the `iota` function, and
- **Part 2:** a single round of `keccak_f`.

We prove that the implementation is equivalent to the specification.

Note that this is only a very small part of SHA-3. Some of the functions that are part of
a round of `keccak_f`, but that we ignore in this example are simply `unimplemented!()`.

The extraction and proofs can be run as follows:
```sh
cd sha3/
make lean
```

This extracts the Rust code from `sha3/src/lib.rs` into
`examples/sha3/proofs/lean/Sha3/Extraction/Funs.lean`. The Lean proof can be found in
`examples/sha3/proofs/lean/Sha3/Equivalence.lean`.

### Loop Equivalence

The loop equivalence example contains two artificially crafted functions that implement a loop
operating on an array in two different styles. We prove them to be equivalent.

The extraction and proofs can be run as follows:
```sh
cd loop_equivalence/
make lean
```

### ADC (Addition with Carry)

The *ADC* (addition with carry) example verifies a 32-bit limb addition with
carry, a fundamental building block in multi-precision (bignum) arithmetic.

The verified property states that the 64-bit sum `a + b + carry_in` is correctly
split into a 32-bit sum and a 1-bit carry output.

The extraction and proofs can be run as follows:
```sh
cd adc/
make lean
```

## F*

### Requirements

  First, make sure to have hax installed in PATH. Then:

  * With Nix, `nix develop .#examples` setups a shell automatically for you.

  * Without Nix: Install [Hax](../README.md#installation) 
  and [F*](https://github.com/FStarLang/FStar/blob/master/INSTALL.md) `v2025.10.06`<!---FSTAR_VERSION-->

### Run the examples

Running `make fstar` in one of the example directories will
generate F\* modules using hax and then typecheck those
modules using F\*.

Note the generated modules live in the
`<EXAMPLE>/proofs/fstar/extraction` folders.

| Name               | Status of the F\* extraction |
| ------------------ | ---------------------------- |
| chacha20           | Typechecks                   |
| limited-order-book | Typechecks                   |
| sha256             | Lax-typechecks               |
| barrett            | Typechecks                   |
| kyber_compress     | Typechecks                   |

## Coq

See [./coq-example/README.md]()


## Lean (legacy backend)

Only one example is still running on the legacy lean backend: `legacy_lean_chacha20`.

### Chacha20

The Chacha20 example showcases array, vector and slices accesses, as well as loops
(with loop invariants). For the Lean extracted code, we prove panic freedom,
which involves arithmetic on size of arrays.

The extraction and proofs can be run as follows:
```sh
cd legacy_lean_chacha20/
make
```
