CHARON ?= charon
AENEAS ?= aeneas
RUSTFLAGS ?= "--cfg charon"

# `hax-lib` git revision, derived from the workspace Cargo.toml so the
# alloc-staging step (which inlines an explicit `hax-lib = { git, rev }`
# line, see below) can never disagree with the version the rest of the
# workspace pulls in via `hax-lib.workspace = true`.
HAX_LIB_REV := $(shell sed -n 's/.*hax-lib.*rev = "\([^"]*\)".*/\1/p' Cargo.toml)

CRATE_NAME = core_models
LLBC_FILE = $(CRATE_NAME).llbc
LEAN_DIR = ../proof-libs/lean
# The main Rust crate (`core-models`) lives under ./core-models/ — its
# Cargo.toml is the package manifest. The root Cargo.toml is the
# workspace.
CORE_MODELS_DIR = core-models

# The `alloc/` crate cannot be extracted directly: its package name is
# `alloc`, which collides with Aeneas's builtin path map for `alloc::vec::Vec`
# and friends, crashing the type analyser. We work around this by staging a
# copy of the crate under `.alloc-extract/` whose Cargo.toml has been
# rewritten to `name = "alloc_models"`. After Aeneas runs, the patcher
# rewrites the resulting Lean files to put everything back in the `alloc`
# namespace (downstream Aeneas-extracted code expects `alloc.vec.Vec` etc.).
ALLOC_LLBC_FILE = alloc.llbc
ALLOC_STAGE_DIR = .alloc-extract

# Items in the `alloc` crate that can't be extracted (Aeneas crashes on them
# even after the rename trick). They are independent of the patcher's
# Lean-text comment-out logic.
ALLOC_CHARON_EXCLUDES = \
    --exclude 'alloc_models::collections::binary_heap::*' \
    --exclude '{impl alloc_models::collections::binary_heap::BinaryHeap<_, _>}' \
    --exclude '{impl alloc_models::collections::binary_heap::BinaryHeap<_, _>}::*' \
    --exclude 'alloc_models::string::*' \
    --exclude '{impl alloc_models::string::String}::*' \
    --exclude '{impl core::iter::traits::collect::FromIterator<_> for alloc_models::vec::Vec<_>}' \
    --exclude '{impl core::iter::traits::collect::FromIterator<_> for alloc_models::vec::Vec<_>}::*' \
    --exclude '{impl core::iter::traits::collect::FromIterator<_> for alloc_models::collections::vec_deque::VecDeque<_, _>}' \
    --exclude '{impl core::iter::traits::collect::FromIterator<_> for alloc_models::collections::vec_deque::VecDeque<_, _>}::*' \
    --exclude 'alloc_models::slice::_::sort_by'

.PHONY: all llbc extract patch lean build clean clean-generated tests \
        tests-clean alloc-stage alloc-llbc alloc-extract alloc-clean \
        coverage

all: lean coverage

# 1. Run charon to produce LLBC from the Rust crate.
#
# `--exclude` removes items at the LLBC level so Aeneas never sees them.
# We use it for pure-fn duplicates that we provide ourselves in
# `Aeneas/PureFuns.lean` (Aeneas marks the corresponding `core::*` items
# with `~can_fail:false`, so the extraction emits *pure* references that
# our shims must satisfy).
#
# Things we *cannot* exclude here (because the rest of the crate references
# them and Aeneas's dependency analysis crashes if they vanish):
#   - `core_models::num::*::{MIN,MAX}` (used by `try_from` impls).
#   - The trait/type forward declarations (`clone::Clone`, `marker::Copy`,
#     `ops::function::{Fn,FnMut,FnOnce}`, `option::Option`).
# These are still handled at the Lean text level by `patch_lean.py`.
CHARON_EXCLUDES = \
    --exclude 'core_models::mem::swap' \
    --exclude 'core_models::mem::replace' \
    --exclude 'core_models::option::_::is_some' \
    --exclude 'core_models::option::_::is_none' \
    --exclude 'core_models::option::_::unwrap_or' \
    --exclude 'core_models::option::_::take' 

llbc: $(LLBC_FILE)

$(LLBC_FILE): $(CORE_MODELS_DIR)/src/**/*.rs $(CORE_MODELS_DIR)/Cargo.toml
	cd $(CORE_MODELS_DIR) && RUSTFLAGS=$(RUSTFLAGS) $(CHARON) cargo --preset=aeneas \
	    $(CHARON_EXCLUDES) \
	    --dest-file $(abspath $(LLBC_FILE))

# 2. Run Aeneas to extract Lean files into $(LEAN_DIR)/.
#    Aeneas writes Funs.lean, Types.lean, FunsExternal_Template.lean,
#    TypesExternal_Template.lean at the root of $(LEAN_DIR). Anything inside
#    $(LEAN_DIR)/Aeneas/ is left untouched.
extract: $(LLBC_FILE) alloc-extract
	mkdir -p $(LEAN_DIR)
	$(AENEAS) -core-models-lib -backend lean $(LLBC_FILE) -split-files -dest $(LEAN_DIR) \
	-subdir CoreModels/Core -all-computable

# -----------------------------------------------------------------------------
# alloc/ extraction (with the `alloc_models` crate-name workaround)
# -----------------------------------------------------------------------------

# Stage a renamed copy of `alloc/` so charon sees a crate named `alloc_models`
# (avoids the Aeneas builtin name collision on `alloc::vec::Vec`). The src/
# tree is symlinked so any source edit is picked up automatically.
$(ALLOC_STAGE_DIR)/Cargo.toml: alloc/Cargo.toml
	rm -rf $(ALLOC_STAGE_DIR)
	mkdir -p $(ALLOC_STAGE_DIR)
	cp alloc/Cargo.toml $(ALLOC_STAGE_DIR)/Cargo.toml
	ln -s ../alloc/src $(ALLOC_STAGE_DIR)/src
	# Rename the package and inline the workspace-inherited `hax-lib` dep so
	# the staged crate can be built standalone (the `[workspace]` block
	# appended at the end opts the staged crate out of our root workspace).
	sed -i 's|^name = "alloc"$$|name = "alloc_models"|' $(ALLOC_STAGE_DIR)/Cargo.toml
	sed -i 's|^hax-lib\.workspace = true$$|hax-lib = { git = "https://github.com/cryspen/hax", rev = "$(HAX_LIB_REV)" }|' $(ALLOC_STAGE_DIR)/Cargo.toml
	printf '\n[workspace]\n' >> $(ALLOC_STAGE_DIR)/Cargo.toml

alloc-stage: $(ALLOC_STAGE_DIR)/Cargo.toml

$(ALLOC_LLBC_FILE): $(ALLOC_STAGE_DIR)/Cargo.toml alloc/src/lib.rs
	cd $(ALLOC_STAGE_DIR) && RUSTFLAGS=$(RUSTFLAGS) $(CHARON) cargo --preset=aeneas \
	    $(ALLOC_CHARON_EXCLUDES) \
	    --dest-file $(abspath $(ALLOC_LLBC_FILE))

alloc-llbc: $(ALLOC_LLBC_FILE)

# Run Aeneas on the staged alloc llbc, writing into $(LEAN_DIR)/CoreModels/Alloc/.
# `-subdir CoreModels/Alloc` makes Aeneas emit `import CoreModels.Alloc.<X>` rather
# than the auto-derived `Alloc_models.<X>` prefix.
alloc-extract: $(ALLOC_LLBC_FILE)
	$(AENEAS) -core-models-lib -backend lean $(ALLOC_LLBC_FILE) -split-files \
	    -dest $(LEAN_DIR) -subdir CoreModels/Alloc -all-computable

# 3. Move generated files into $(LEAN_DIR)/CoreModels/ and apply our patches
#    (imports, opens, namespace rename, comment-outs of broken defs, etc.).
patch:
	python3 patch_lean.py

# 4. Build the Lean library to verify it compiles.
build:
	cd $(LEAN_DIR) && lake exe cache get && lake build

# Convenience target: extract, patch, build.
lean: extract patch build

# Remove only generated artifacts; preserve hand-written files.
clean-generated:
	rm -f $(LEAN_DIR)/CoreModels/Core/Funs.lean
	rm -f $(LEAN_DIR)/CoreModels/Core/Types.lean
	rm -f $(LEAN_DIR)/CoreModels/Core/FunsExternal_Template.lean
	rm -f $(LEAN_DIR)/CoreModels/Core/TypesExternal_Template.lean
	rm -rf $(LEAN_DIR)/CoreModels/Alloc

# Drop the staged alloc copy and its llbc.
alloc-clean:
	rm -rf $(ALLOC_STAGE_DIR)
	rm -f $(ALLOC_LLBC_FILE)

# Full clean: drop the LLBC and the build cache too.
clean: clean-generated alloc-clean
	rm -f $(LLBC_FILE)
	rm -rf $(LEAN_DIR)/.lake

# -----------------------------------------------------------------------------
# Tests: a small Rust crate (./tests) that exercises items from `core::*` and
# `std::*`
# -----------------------------------------------------------------------------

tests: lean
	$(MAKE) -C tests

tests-clean:
	$(MAKE) -C tests clean

# -----------------------------------------------------------------------------
# Coverage report: how much of real core/alloc the model crates provide.
# (rustdoc-JSON based; independent of the charon/aeneas pipeline above.)
# -----------------------------------------------------------------------------

# Regenerate COVERAGE.md + tools/core-coverage/coverage.json.
coverage:
	./tools/core-coverage/gen.sh
