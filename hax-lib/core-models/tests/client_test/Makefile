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

# Remove only the Aeneas-generated files; keep the hand-written project files
# (lakefile.toml, lean-toolchain, ClientTest.lean, and the *External.lean stubs).
clean:
	rm -f $(EXTRACTION_DIR)/Funs.lean \
	      $(EXTRACTION_DIR)/Types.lean \
	      $(EXTRACTION_DIR)/Specs.lean \
	      $(EXTRACTION_DIR)/ProofObligations.lean \
	      $(EXTRACTION_DIR)/FunsExternal_Template.lean \
	      $(EXTRACTION_DIR)/TypesExternal_Template.lean
	rm -rf $(LEAN_DIR)/llbc $(LEAN_DIR)/.lake
