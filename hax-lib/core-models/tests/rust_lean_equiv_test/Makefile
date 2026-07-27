CHARON ?= charon
AENEAS ?= aeneas

CRATE_NAME = rust_lean_tests
LLBC_FILE = $(CRATE_NAME).llbc
LEAN_DIR = lean
# `-subdir RustLeanTests` makes Aeneas place its output at
# $(LEAN_DIR)/RustLeanTests/ AND emit `import RustLeanTests.<X>` rather
# than the auto-derived module prefix.
SUBDIR = RustLeanTests

.PHONY: all llbc extract gen-lean-tests cargo-test build clean

all: cargo-test build

# Rust-side half of the rust↔lean equivalence check: every
# `#[rust_lean_test]` function generates a `#[cfg(test)] #[test]` wrapper
# that asserts it returns `true`. The Lean-side half is the `#guard`s
# emitted by `gen_lean_tests.py` (see `gen-lean-tests` below).
cargo-test:
	cd source && cargo test --lib

# 1. Run charon to produce LLBC from the source crate.
# `--dest-file` must be absolute: since the parent `tests/` is a cargo
# workspace, charon resolves relative paths against the workspace root,
# not the source subcrate.
$(LLBC_FILE): $(shell find source/src -name '*.rs') source/Cargo.toml
	cd source && $(CHARON) cargo --preset=aeneas --dest-file $(abspath $(LLBC_FILE))

llbc: $(LLBC_FILE)

# 2. Run Aeneas to extract Lean files into $(LEAN_DIR)/$(SUBDIR)/.
extract: $(LLBC_FILE)
	$(AENEAS) -core-models-lib -backend lean $(LLBC_FILE) -split-files \
		-dest $(LEAN_DIR) -subdir $(SUBDIR)
	# Aeneas writes `*External_Template.lean` files alongside its
	# real output. Our hand-written `FunsExternal.lean` /
	# `TypesExternal.lean` stubs satisfy the imports — drop the
	# templates so Lake doesn't pick them up by mistake.
	rm -f $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean

# 3. Generate `lean/RustLeanTests/LeanTests.lean` — one
#    `#guard <name> == .ok true` per `#[rust_lean_test]` function in
#    `source/src/lib.rs`. Depends on `extract` so the gen script can
#    look up each test's fully-qualified Lean name in `Funs.lean`.
gen-lean-tests: extract
	python3 gen_lean_tests.py

# 4. Build the Lean library — this is where the `#guard`s fire.
build: gen-lean-tests
	cd $(LEAN_DIR) && lake exe cache get && lake build

# Only remove files Aeneas re-generates; keep the hand-written
# `FunsExternal.lean` / `TypesExternal.lean` stubs in $(SUBDIR).
clean:
	rm -f $(LLBC_FILE)
	rm -f $(LEAN_DIR)/$(SUBDIR)/Funs.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/Types.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/LeanTests.lean
	rm -rf $(LEAN_DIR)/.lake
