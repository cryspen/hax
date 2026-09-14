# Type-checks the committed Lean snapshots: no hax, no engine, nothing
# regenerated. `lake env` inside the proof library supplies the toolchain and
# the `LEAN_PATH` that `import Hax` needs, so the snapshots are checked where
# they lie, without a package or a module name of their own.

HAX_ROOT  ?= $(shell git rev-parse --show-toplevel)
SNAPSHOTS := $(HAX_ROOT)/tests/snapshots
PROOF_LIB := $(HAX_ROOT)/hax-lib/proof-libs/legacy-lean
HAX_OLEAN := $(PROOF_LIB)/.lake/build/lib/lean/Hax.olean

CACHE_DIR ?= $(CURDIR)/.cache

# The snapshots no prover is expected to accept live in
# `<test>/legacy-lean-xfail/`, so matching `*/legacy-lean/*` is the whole
# selection. `MATCHING` narrows the run locally: `just verify-lean legacy/tuples`.
MATCHING ?=
ROOTS  := $(shell find $(SNAPSHOTS) -path '*/legacy-lean/*.lean' \
            | grep -e '$(MATCHING)' | sort)
OLEANS := $(patsubst $(SNAPSHOTS)/%,$(CACHE_DIR)/%.olean,$(ROOTS))

ifeq ($(strip $(ROOTS)),)
ifeq ($(filter clean describe,$(MAKECMDGOALS)),)
$(error no Lean snapshot under $(SNAPSHOTS) matches '$(MATCHING)')
endif
endif

.DEFAULT_GOAL := all
.PHONY: all verify oleans proof-lib describe clean
.DELETE_ON_ERROR:

all verify: proof-lib
	$(Q)$(MAKE) -f $(firstword $(MAKEFILE_LIST)) oleans

proof-lib:
	$(Q)cd $(PROOF_LIB) && lake build

oleans: $(OLEANS)

$(CACHE_DIR)/%.olean: $(SNAPSHOTS)/% $(HAX_OLEAN) $(firstword $(MAKEFILE_LIST))
	$(Q)mkdir -p $(dir $@)
	$(Q)printf '[LEAN] %s\n' "$(patsubst %/legacy-lean/new_tests.lean,%,$*)"
	$(Q)cd $(PROOF_LIB) && lake env lean --root=$(SNAPSHOTS) -o $@ $<

describe:
	@echo "snapshots: $(words $(ROOTS))"
	@echo "proof-lib: $(PROOF_LIB)"
	@echo "cache:     $(CACHE_DIR)"

clean:
	rm -rf $(CACHE_DIR) $(CURDIR)/.lake $(CURDIR)/Snapshots \
	  $(CURDIR)/Snapshots.lean $(CURDIR)/lake-manifest.json

Q ?= @
