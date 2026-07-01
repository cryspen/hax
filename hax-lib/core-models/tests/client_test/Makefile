CHARON ?= charon
AENEAS ?= aeneas

CRATE_NAME = client_test
LLBC_FILE = $(CRATE_NAME).llbc
LEAN_DIR = lean
# `-subdir ClientTest` makes Aeneas place its output at
# $(LEAN_DIR)/ClientTest/ AND emit `import ClientTest.<X>` rather than the
# auto-derived module prefix.
SUBDIR = ClientTest

.PHONY: all llbc extract build clean

all: build

# 1. Run charon to produce LLBC from the Rust crate.
# `--dest-file` must be absolute: since the parent `tests/` is a cargo
# workspace, charon resolves relative paths against the workspace root,
# not this subcrate.
$(LLBC_FILE): src/lib.rs Cargo.toml
	$(CHARON) cargo --preset=aeneas --dest-file $(abspath $(LLBC_FILE))

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

# 3. Build the Lean library — this is the actual test. If extraction
#    produced anything that fails to elaborate against our CoreModels
#    shims, the build errors here.
build: extract
	cd $(LEAN_DIR) && lake exe cache get && lake build

# Only remove files Aeneas re-generates; keep the hand-written
# `FunsExternal.lean` / `TypesExternal.lean` stubs in $(SUBDIR).
clean:
	rm -f $(LLBC_FILE)
	rm -f $(LEAN_DIR)/$(SUBDIR)/Funs.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/Types.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/FunsExternal_Template.lean
	rm -f $(LEAN_DIR)/$(SUBDIR)/TypesExternal_Template.lean
	rm -rf $(LEAN_DIR)/.lake
