# Rust↔Lean equivalence test

HAX ?= cargo hax
LEAN_DIR = source/proofs/lean
EXTRACTION_DIR = $(LEAN_DIR)/RustLeanTests/Extraction

.PHONY: all cargo-test extract gen-lean-tests build clean

all: cargo-test build

# Rust-side half: every `#[rust_lean_test]` generates a `#[cfg(test)]
# #[test]` wrapper that asserts the function returns `true`. The Lean-side
# half is the `#guard`s built below.
cargo-test:
	cd source && cargo test --lib

# 1. Extract Rust -> Lean with hax. Output
#    lands in `source/proofs/lean/RustLeanTests/Extraction/`.
extract:
	cd source && $(HAX) into lean

# 2. Generate `RustLeanTests/LeanTests.lean` — one `#guard <name> == .ok
#    true` per `#[rust_lean_test]` function. Depends on `extract` so the gen
#    script can look up each test's fully-qualified Lean name in `Funs.lean`.
gen-lean-tests: extract
	python3 gen_lean_tests.py

# 3. Build the Lean library — this is where the `#guard`s fire.
build: gen-lean-tests
	cd $(LEAN_DIR) && lake exe cache get && lake build

# Remove only the Aeneas-generated files and the generated `LeanTests.lean`;
# keep the hand-written project files.
clean:
	rm -f $(EXTRACTION_DIR)/Funs.lean \
	      $(EXTRACTION_DIR)/Types.lean \
	      $(EXTRACTION_DIR)/FunsExternal_Template.lean \
	      $(EXTRACTION_DIR)/TypesExternal_Template.lean \
	      $(LEAN_DIR)/RustLeanTests/LeanTests.lean
	rm -rf $(LEAN_DIR)/llbc $(LEAN_DIR)/.lake
