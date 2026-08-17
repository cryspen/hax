# Extract the `client_test` crate, using core-models as a dependency.
# This tests the setup an actual user would have.

HAX ?= cargo hax
LEAN_DIR = proofs/lean
EXTRACTION_DIR = $(LEAN_DIR)/ClientTest/Extraction

.PHONY: all extract build clean

all: build

# 1. Extract Rust -> Lean
extract:
	$(HAX) into lean

# 2. Build the Lean library — this is the actual test.
build: extract
	cd $(LEAN_DIR) && lake exe cache get && lake build

# Remove the generated files; keep the hand-written project files
# (lakefile.toml, lean-toolchain, ClientTest.lean, and the
# Assumptions/*External.lean stubs).
clean:
	rm -rf $(EXTRACTION_DIR)
	rm -rf $(LEAN_DIR)/llbc $(LEAN_DIR)/.lake
	rm -f $(LEAN_DIR)/.gitignore
