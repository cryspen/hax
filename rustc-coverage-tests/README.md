This crate contains the [rust files](https://github.com/rust-lang/rust/tree/master/tests/coverage) from rustc [coverage tests](https://rustc-dev-guide.rust-lang.org/tests/compiletest.html#coverage-tests). 

The following test target are available:
- `json` to test AST extraction as json using hax frontend
- `fstar` to test that extraction to F* succeeds
- `fstar-lax` to test that extraction to F* and lax-checking succeed
- `coq` to test that extraction to coq succeeds
- `lean` to test that extraction to Lean succeeds
- `lean-tc` to test that extraction to Lean succeeds and type checks

## Running

A script is available to run the tests using `python rustc-coverage-tests.py <target>` where `<target>` is either one of the targets or `all`.

### Checking negative results

If you run `python run-coverage-tests.py --with-negative <target>` you also check that tests that are not expected to succeed actually fail.

It will produce a summary of the results file by file.

This feature has some python dependencies, so you may need to run `pip install tabulate pyyaml` first.

### Checking stability

If you run `python run-coverage-tests.py --with-negative --check-stability <target>` you check that the generated files correspond to the stored snapshots. To update these snapshots, run `python run-coverage-tests.py --with-negative --check-stability --update-snapshots <target>`


## Modifying

### Updating sources

Run ./update-test-sources.sh to update the test with the latest versions used by rustc.

### Adding a new test target

To add a new test target:
- Add a corresponding feature to the `Cargo.toml`
- Activate the wanted tests for this feature by enabling them under the feature. This is done using the `cfg` attributes in the `lib.rs`/`mod.rs` files (see next section).
- Activate the same tests for the feature in `test_config.yaml`.
- Modify the script to add the new target

### Activating a test file for a given target

To activate a test for a target, you can add the feature corresponding to the target to the `cfg` attribute of this test in `lib.rs` (or `mod.rs` for tests contained in submodules). For example: 
```rust
#[cfg(any(feature = "json", feature = "fstar"))]
mod abort;
```
This means that the test in `abort.rs` runs only for features `json` and `fstar`. If you want to also run it under a new feature you can modify this to `#[cfg(any(feature = "json", feature = "fstar", feature = "<my_new_feature>"))]`.

Some tests are currently not activated for any feature. The corresponding module declarations are commented out (for example `// mod async_block;`). To add these tests to a target, uncomment the corresponding line and add the adequate `cfg` attribute.

There is a separate configuration in `test_config.yaml` that should match what is defined with the `cfg` flags. This one is also used to check that tests that are not activated do fail.
