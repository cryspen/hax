HAX ?= cargo hax
# `cfg(charon)` marks the Lean pipeline in the model sources: it enables the
# `aeneas::exclude` annotations and drops the specs Aeneas cannot translate.
RUSTFLAGS ?= "--cfg charon"

# Absolute path to the `hax-lib` crate, for the alloc-staging step below.
# The workspace Cargo.toml reaches it as a *relative* path (`..`), which
# the staged copy cannot reuse: a workspace-inherited path dependency
# resolves against the workspace root, and $(ALLOC_STAGE_DIR) is one level
# below it. Resolving to an absolute path here keeps the two independent of
# where the staging directory sits.
HAX_LIB_DIR := $(abspath ..)

LEAN_DIR = ../proof-libs/lean
# `cargo hax into lean` writes here (Lean files and LLBC alike); `patch`
# installs into $(LEAN_DIR) the subset the library needs.
EXTRACT_DIR = .lean-extract
FSTAR_DIR = ../proof-libs/fstar/core
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
ALLOC_STAGE_DIR = .alloc-extract

# Items in the `alloc` crate that must not reach Aeneas, either because it
# crashes on them (even after the rename trick) or because they are
# `#[hax_lib::opaque]` models whose Rust body is a type-checker placeholder
# rather than a specification (`sort_by`): hax drops those bodies, but Aeneas
# would extract them verbatim and hand Lean a wrong definition.
# They are independent of the patcher's Lean-text comment-out logic.
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

# Items whose Rust body cannot model std, but whose *signature* we still want
# downstream (unlike `--exclude`, `--opaque` keeps the declaration and drops the
# body, so aeneas emits an uninterpreted function instead of a wrong one).
#   - `Vec::drain` ignores its range argument: `RangeBounds` is not modelled.
#   - `fmt::format` returns the empty string: `fmt::Arguments` is not modelled.
ALLOC_CHARON_OPAQUE = \
    --opaque 'alloc_models::vec::_::drain' \
    --opaque 'alloc_models::fmt::format'

.PHONY: all extract patch lean build clean clean-generated tests \
        tests-clean alloc-stage alloc-extract alloc-clean \
        coverage fstar fstar-clean fstar-prune fstar-core-models fstar-std fstar-alloc \
        fstar-rand-core

all: lean fstar coverage

# Our two model crates share one Lean package (`CoreModels/{Core,Alloc}`), so
# the recipes below override hax's per-crate `-subdir`. hax warns about that.
AENEAS_ARGS = -all-computable

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

# 1. Run charon + Aeneas, writing the Lean files into $(EXTRACT_DIR)/CoreModels/Core/.
# `HAX_CORE_MODELS_EXTRACTION_MODE=on` is what lets the library be named
# `CoreModels`: hax reserves that module root, since every package it generates
# has one, and unlocks it only for the models' own extraction.
extract: alloc-extract
	cd $(CORE_MODELS_DIR) && RUSTFLAGS=$(RUSTFLAGS) \
	    HAX_CORE_MODELS_EXTRACTION_MODE=on $(HAX) into \
	    --output-dir $(abspath $(EXTRACT_DIR)) lean \
	    --charon-args="$(CHARON_EXCLUDES)" \
	    --aeneas-args="-subdir CoreModels/Core $(AENEAS_ARGS)"

# -----------------------------------------------------------------------------
# alloc/ extraction (with the `alloc_models` crate-name workaround)
# -----------------------------------------------------------------------------

# Stage a renamed copy of `alloc/` so charon sees a crate named `alloc_models`
# (avoids the Aeneas builtin name collision on `alloc::vec::Vec`). The src/
# tree is symlinked so any source edit is picked up automatically.
# Depends on the Makefile too: the recipe below bakes manifest content in,
# so a change here has to re-stage rather than leave a stale copy in place.
$(ALLOC_STAGE_DIR)/Cargo.toml: alloc/Cargo.toml Makefile
	rm -rf $(ALLOC_STAGE_DIR)
	mkdir -p $(ALLOC_STAGE_DIR)
	cp alloc/Cargo.toml $(ALLOC_STAGE_DIR)/Cargo.toml
	ln -s ../alloc/src $(ALLOC_STAGE_DIR)/src
	# Rename the package and inline the workspace-inherited `hax-lib` dep so
	# the staged crate can be built standalone (the `[workspace]` block
	# appended at the end opts the staged crate out of our root workspace).
	perl -i -pe 's|^name = "alloc"$$|name = "alloc_models"|' $(ALLOC_STAGE_DIR)/Cargo.toml
	perl -i -pe 's|^hax-lib\.workspace = true$$|hax-lib = { path = "$(HAX_LIB_DIR)" }|' $(ALLOC_STAGE_DIR)/Cargo.toml
	printf '\n[workspace]\n' >> $(ALLOC_STAGE_DIR)/Cargo.toml

alloc-stage: $(ALLOC_STAGE_DIR)/Cargo.toml

# Extract the staged crate, writing into $(EXTRACT_DIR)/CoreModels/Alloc/.
# `-subdir CoreModels/Alloc` makes Aeneas emit `import CoreModels.Alloc.<X>` rather
# than the auto-derived `Alloc_models.<X>` prefix.
alloc-extract: $(ALLOC_STAGE_DIR)/Cargo.toml
	cd $(ALLOC_STAGE_DIR) && RUSTFLAGS=$(RUSTFLAGS) $(HAX) into \
	    --output-dir $(abspath $(EXTRACT_DIR)) lean \
	    --charon-args="$(ALLOC_CHARON_EXCLUDES) $(ALLOC_CHARON_OPAQUE)" \
	    --aeneas-args="-subdir CoreModels/Alloc $(AENEAS_ARGS)"

# 2. Move generated files into $(LEAN_DIR)/CoreModels/ and apply our patches
#    (imports, opens, namespace rename, comment-outs of broken defs, etc.).
#
# Aeneas also writes `Specs.lean` and `ProofObligations.lean`, which the Lean
# library has no use for yet: they stay in $(EXTRACT_DIR).
GENERATED_LEAN = Funs.lean Types.lean \
                 FunsExternal_Template.lean TypesExternal_Template.lean

patch:
	@test -d $(EXTRACT_DIR)/CoreModels/Core -a -d $(EXTRACT_DIR)/CoreModels/Alloc \
	    || { echo "no extraction in $(EXTRACT_DIR): run 'make extract' first"; exit 1; }
	mkdir -p $(LEAN_DIR)/CoreModels/Core $(LEAN_DIR)/CoreModels/Alloc
	cd $(EXTRACT_DIR)/CoreModels/Core && \
	    cp $(GENERATED_LEAN) $(abspath $(LEAN_DIR))/CoreModels/Core/
	cd $(EXTRACT_DIR)/CoreModels/Alloc && \
	    cp $(GENERATED_LEAN) $(abspath $(LEAN_DIR))/CoreModels/Alloc/
	python3 patch_lean.py

# 3. Build the Lean library to verify it compiles.
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

# Drop the staged alloc copy.
alloc-clean:
	rm -rf $(ALLOC_STAGE_DIR)

# Full clean: drop the staged extraction (LLBC included) and the build cache too.
clean: clean-generated alloc-clean fstar-clean
	rm -rf $(EXTRACT_DIR)
	rm -rf $(LEAN_DIR)/.lake

FSTAR_CRATES = core-models std alloc rand_core

CORE_MODELS_FSTAR_INTERFACES = \
    '+!core_models::str::* +!**::num::error +!**::panicking::internal \
     +!core_models::borrow +!core_models::default +!core_models::error \
     +!core_models::hash +!core_models::hint +!core_models::ops::bit \
     +!core_models::ops::arith +!core_models::fmt +!core_models::fmt::rt \
     +!core_models::mem +!core_models::mem::*'


CORE_MODELS_FSTAR_EXCLUDES = -core_models::iter::range::**


STD_FSTAR_EXCLUDES = -core_models::**

ALLOC_FSTAR_INTERFACES = '+!**::collections::btree::**'


fstar-core-models:
	RUSTFLAGS= HAX_CORE_MODELS_EXTRACTION_MODE=on $(HAX) -C -p core-models \; \
	    into -i '$(CORE_MODELS_FSTAR_EXCLUDES)' \
	    fstar --interfaces $(CORE_MODELS_FSTAR_INTERFACES)
	cp $(CORE_MODELS_DIR)/proofs/fstar/extraction/*.fst* $(FSTAR_DIR)

fstar-std:
	RUSTFLAGS= HAX_CORE_MODELS_EXTRACTION_MODE=on $(HAX) -C -p std \; \
	    into -i '$(STD_FSTAR_EXCLUDES)' fstar --interfaces '+!**'
	cp std/proofs/fstar/extraction/*.fst* $(FSTAR_DIR)

fstar-alloc:
	RUSTFLAGS= HAX_CORE_MODELS_EXTRACTION_MODE=on $(HAX) -C -p alloc \; \
	    into fstar --interfaces $(ALLOC_FSTAR_INTERFACES)
	cp alloc/proofs/fstar/extraction/*.fst* $(FSTAR_DIR)

fstar-rand-core:
	RUSTFLAGS= HAX_CORE_MODELS_EXTRACTION_MODE=on $(HAX) -C -p rand_core \; \
	    into fstar --interfaces '+!**'
	cp rand_core/proofs/fstar/extraction/*.fst* $(FSTAR_DIR)

# Hand-written F* modules living alongside the extraction in $(FSTAR_DIR).
# Everything else there is generated, so `make fstar` deletes the rest before
# reinstalling: a module the extraction stops producing then disappears from the
# tree instead of lingering forever (`git status` shows the deletion, and CI's
# "committed extraction must match" check catches it). Without this, a stale
# module keeps type-checking as part of `ROOTS` and nothing ever notices.
FSTAR_HANDWRITTEN = \
    Core_models.Core_arch.Arm_shared.Neon.fsti \
    Core_models.Core_arch.fsti \
    Core_models.Core_arch.X86_64_.Sse2.fsti \
    Core_models.Core_arch.X86.fsti \
    Core_models.Core_arch.X86.Pclmulqdq.fsti \
    Core_models.Core_arch.X86.Sse2.fsti \
    Core_models.fst \
    Core_models.Iter.Adapters.Rev.fsti \
    Core_models.Iter.Sources.Repeat_with.fsti \
    Core_models.Iter.Traits.fst \
    Core_models.Mem.Maybe_uninit.fsti \
    Core_models.Mem.Transmutability.fsti \
    Core_models.Num.Checked_mul_spec.fst \
    Core_models.Num.Niche_types.fsti \
    Core_models.Num.Overflow_spec.fst \
    Core_models.Ops.Index.IndexMut.fst \
    Core_models.Str.fsti \
    Core_models.Time.fsti \
    Core_models.TypeClassPlaceHolder.fst \
    Rand.Distr.Distribution.fsti \
    Rand.Distributions.Distribution.fsti \
    Rand.Distributions.Integer.fsti \
    Rand.Distr.Integer.fsti \
    Rand.Rng.fsti

# Delete every generated module so the reinstall below cannot leave a stale one.
fstar-prune:
	@cd $(FSTAR_DIR) && for f in *.fst *.fsti; do \
	    [ -e "$$f" ] || continue; \
	    case " $(FSTAR_HANDWRITTEN) " in \
	        *" $$f "*) ;; \
	        *) rm -f "$$f" ;; \
	    esac; \
	done

# Prune first, then reinstall. Recursive make rather than a prerequisite list so
# the ordering holds under `-j`; the per-crate targets stay prune-free so they
# remain usable on their own.
fstar:
	$(MAKE) fstar-prune
	$(MAKE) fstar-core-models fstar-std fstar-alloc fstar-rand-core

fstar-clean:
	rm -rf $(foreach c,$(FSTAR_CRATES),$(c)/proofs)

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
