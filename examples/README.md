# Examples

The sections below describe what each example shows and how to run its backend.

Each example declares its extraction as a proof scenario (a `[scenario.<name>]`
table in its `hax.toml`, see the [tools manual](../docs/manual/tools.md)), so
the generated files live in `<EXAMPLE>/proofs/<scenario>/<backend>/`.

## Lean

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

This extracts the Rust code from `src/lib.rs` into
`proofs/barrett/lean/Barrett/Extraction/`. The Lean proof can be found in
`proofs/barrett/lean/Barrett/Verification/ProofObligations.lean`.

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

This extracts the Rust code from `src/lib.rs` into
`proofs/sha3/lean/Sha3/Extraction/Funs.lean`. The Lean proof can be found in
`proofs/sha3/lean/Sha3/Verification/Equivalence.lean`.

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

### Lean tutorial

The `lean_tutorial` example accompanies the
[Lean tutorial](../docs/manual/lean/tutorial/index.md): it contains the code
the tutorial develops. The extraction and proofs can be run as follows:
```sh
cd lean_tutorial/
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
`<EXAMPLE>/proofs/<scenario>/fstar/extraction` folders.

| Name               | Description                                                              | Status of the F\* extraction |
| ------------------ | ------------------------------------------------------------------------ | ---------------------------- |
| chacha20           | An implementation of the ChaCha20 stream cipher.                          | Typechecks                   |
| limited-order-book | A limited order book, the matching component of an exchange.              | Typechecks                   |
| sha256             | An implementation of the SHA-256 hash function.                           | Lax-typechecks               |
| barrett            | Barrett reduction (see the [Lean section](#barrett-reduction) above).     | Typechecks                   |
| kyber_compress     | The coefficient compression function of Kyber (ML-KEM).                   | Typechecks                   |

## ProVerif

The `proverif-psk` example implements the initiator and responder logic of a
simplistic pre-shared-key (PSK) based protocol, and analyzes it with the
ProVerif backend; a handwritten ProVerif model of the same protocol is included
for comparison. See its [Readme](./proverif-psk/Readme.md) for the protocol and
the modeling choices.

With [ProVerif](https://bblanche.gitlabpages.inria.fr/proverif/) installed, the
extraction and analysis can be run as follows:
```sh
cd proverif-psk/
make
```

## Checking examples

From the repository root, `just check-example <name>` extracts and verifies a
single example, and `just check-examples` does so for all of them. This is what
CI runs.

Both commands start from a clean state: they first delete the generated files,
including the extractions tracked in git. Restore the tracked files with
`git checkout examples/*/proofs`.
