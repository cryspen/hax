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
    1. install F* `v2025.03.25`<!---FSTAR_VERSION--> manually (see https://github.com/FStarLang/FStar/blob/master/INSTALL.md);
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

## Lean

Two examples are fine-tuned to showcase the Lean backend: `lean_barrett` and
`lean_chacha20`. For both, the lean extraction can be obtained by running `cargo
hax into lean`.

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

The proofs are backported in the rust code (in `lean_barrett/src/lib.rs`): doing
`cargo hax into lean` extracts a valid lean file that contains the proof.

The proof can be run by doing (requires `lake`):

```sh
cd lean_barrett/
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
