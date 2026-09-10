# Type-checks the committed F* snapshots: no hax, no engine, nothing
# regenerated. One `--dep full` over every root, so the `proof-libs` closure is
# one set of nodes in one graph, checked once, rather than once per snapshot.

HAX_ROOT  ?= $(shell git rev-parse --show-toplevel)
SNAPSHOTS := $(HAX_ROOT)/tests/snapshots

# `--lax` makes F* write `<module>.checked.lax`, not `<module>.checked`, hence
# a cache and a target name per mode, and a `.depend` generated with
# `$(OTHERFLAGS)`: make's targets have to be the files F* writes, or dependents
# start before their dependencies exist and concurrent runs tear the cache.
CACHE_SUFFIX = $(if $(findstring --lax,$(OTHERFLAGS)),-lax,)
CHECKED      = $(if $(findstring --lax,$(OTHERFLAGS)),.checked.lax,.checked)
CACHE_DIR ?= $(CURDIR)/.cache$(CACHE_SUFFIX)
HINT_DIR  ?= $(CURDIR)/.hints

FSTAR_BIN_DETECT := $(if $(shell command -v fstar.exe),fstar.exe,$(FSTAR_HOME)/bin/fstar.exe)
FSTAR_BIN ?= $(FSTAR_BIN_DETECT)

# The snapshots no prover is expected to accept live in `<test>/fstar-xfail/`,
# so matching `*/fstar/*` is the whole selection. `MATCHING` narrows the run
# locally: `just verify-fstar loops`.
MATCHING ?=
ROOTS := $(shell find $(SNAPSHOTS) -path '*/fstar/*.fst' -o -path '*/fstar/*.fsti' \
           | grep -e '$(MATCHING)' | sort)
DIRS  := $(sort $(dir $(ROOTS)))

INCLUDE_DIRS := $(DIRS) \
  $(HAX_ROOT)/hax-lib/proof-libs/fstar/core \
  $(HAX_ROOT)/hax-lib/proof-libs/fstar/rust_primitives \
  $(HAX_ROOT)/hax-lib/proofs/fstar/extraction

# `--lax`, as `test-driver` has always done here: checked, not proved.
# `OTHERFLAGS=` gives a full run.
OTHERFLAGS ?= --lax

FSTAR_FLAGS = \
  --warn_error -321-331-241-274-239-271-247 \
  --ext context_pruning --z3version 4.13.3 \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached "+Prims+FStar+LowStar+C+Spec.Loops+TestLib" \
  $(addprefix --include ,$(INCLUDE_DIRS))

FSTAR := $(FSTAR_BIN) $(FSTAR_FLAGS)

.PHONY: all verify unique-modules describe clean

all: unique-modules
	$(Q)$(MAKE) -f $(firstword $(MAKEFILE_LIST)) verify

# One cache and one include path make module names a global namespace, where a
# collision would check one snapshot and silently skip the other.
unique-modules:
	$(Q)dupes=$$(for root in $(ROOTS); do basename $$root; done | sort | uniq -d); \
	if [ -n "$$dupes" ]; then \
	  echo "error: several snapshots extract the same F* module:"; \
	  echo "$$dupes" | sed 's/^/  /'; \
	  exit 1; \
	fi

$(CACHE_DIR) $(HINT_DIR):
	$(Q)mkdir -p $@

.depend: $(ROOTS) | $(CACHE_DIR) $(HINT_DIR)
	$(Q)$(FSTAR) $(OTHERFLAGS) --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar' > $@

include .depend

$(CACHE_DIR)/%$(CHECKED): | .depend $(CACHE_DIR) $(HINT_DIR)
	$(Q)printf '[CHECK] %s\n' "$(basename $(notdir $*))"
	$(Q)$(FSTAR) $(OTHERFLAGS) $< --hint_file $(HINT_DIR)/$(notdir $*).hints

verify: $(addsuffix $(CHECKED),$(addprefix $(CACHE_DIR)/,$(notdir $(ROOTS))))

describe:
	@echo "roots:     $(words $(ROOTS))"
	@echo "snapshots: $(words $(DIRS))"
	@echo "fstar:     $(FSTAR_BIN)"
	@echo "cache:     $(CACHE_DIR)"
	@echo "flags:     $(OTHERFLAGS)"

clean:
	rm -rf $(CACHE_DIR) $(HINT_DIR) .depend

Q ?= @
