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

# `.depend` belongs to one mode and one set of roots: `--dep full` emits rules
# only for the roots it was given, under the names the mode writes. Keeping it
# in $(CACHE_DIR) stops a mode switch from reading the other mode's rules, and
# $(ROOTS_STAMP) rebuilds it when the selected set changes -- otherwise a
# narrower earlier run leaves targets with no prerequisite, which F* reports as
# `Error 5: No file provided`.
DEPEND      = $(CACHE_DIR)/depend.mk
ROOTS_STAMP = $(CACHE_DIR)/roots

FSTAR_BIN_DETECT := $(if $(shell command -v fstar.exe),fstar.exe,$(FSTAR_HOME)/bin/fstar.exe)
FSTAR_BIN ?= $(FSTAR_BIN_DETECT)

# The snapshots no prover is expected to accept live in `<test>/fstar-xfail/`,
# so matching `*/fstar/*` is the whole selection. `MATCHING` narrows the run
# locally: `just verify-fstar loops`.
MATCHING ?=
ROOTS := $(shell find $(SNAPSHOTS) -path '*/fstar/*.fst' -o -path '*/fstar/*.fsti' \
           | grep -e '$(MATCHING)' | sort)
DIRS  := $(sort $(dir $(ROOTS)))

# An empty selection would make every goal below succeed without checking
# anything, so refuse it. `clean` and `describe` still work, to debug just that.
ifeq ($(strip $(ROOTS)),)
ifeq ($(filter clean describe,$(MAKECMDGOALS)),)
$(error no F* snapshot under $(SNAPSHOTS) matches '$(MATCHING)')
endif
endif

INCLUDE_DIRS := $(DIRS) \
  $(HAX_ROOT)/hax-lib/proof-libs/fstar/core \
  $(HAX_ROOT)/hax-lib/proof-libs/fstar/rust_primitives \
  $(HAX_ROOT)/hax-lib/proofs/fstar/extraction

# `--lax`, as `test-driver` has always done here: checked, not proved.
# `OTHERFLAGS=` gives a full run.
OTHERFLAGS ?= --lax

FSTAR_FLAGS = \
  --warn_error -321-331-241-274-239-271 \
  --ext context_pruning --z3version 4.13.3 \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --already_cached "+Prims+FStar+LowStar+C+Spec.Loops+TestLib" \
  $(addprefix --include ,$(INCLUDE_DIRS))

FSTAR := $(FSTAR_BIN) $(FSTAR_FLAGS)

XFAIL_DIRS  := $(shell find $(SNAPSHOTS) -type d -name fstar-xfail | grep -e '$(MATCHING)' | sort)
XFAIL_CACHE := $(CURDIR)/.cache-xfail$(CACHE_SUFFIX)

# Set explicitly: the default goal is otherwise whichever target appears first,
# which a later edit can silently change -- adding `FORCE` below once made
# `make` do nothing at all and report success.
.DEFAULT_GOAL := all

.PHONY: all verify xfail unique-modules describe clean FORCE

all: unique-modules
	$(Q)$(MAKE) -f $(firstword $(MAKEFILE_LIST)) verify
	$(Q)$(MAKE) -f $(firstword $(MAKEFILE_LIST)) xfail

# One cache and one include path make module names a global namespace, where a
# collision would check one snapshot and silently skip the other. Compared on
# the module name, not the file name, so that `Foo.fst` in one snapshot and
# `Foo.fsti` in another do not slip through; the two together in one snapshot
# are an ordinary interface pair, hence the pairing with the directory.
unique-modules:
	$(Q)dupes=$$(for root in $(ROOTS); do \
	  printf '%s %s\n' "$$(basename $$root | sed 's/\.fsti\{0,1\}$$//')" "$$(dirname $$root)"; \
	done | sort -u | awk '{print $$1}' | uniq -d); \
	if [ -n "$$dupes" ]; then \
	  echo "error: several snapshots extract the same F* module:"; \
	  echo "$$dupes" | sed 's/^/  /'; \
	  exit 1; \
	fi

$(CACHE_DIR) $(HINT_DIR):
	$(Q)mkdir -p $@

# Rewritten only when the selected set changes, so that `.depend` is rebuilt
# then rather than on every run.
FORCE:

$(ROOTS_STAMP): FORCE | $(CACHE_DIR)
	$(Q)printf '%s\n' $(ROOTS) | cmp -s - $@ 2> /dev/null \
	  || printf '%s\n' $(ROOTS) > $@

$(DEPEND): $(ROOTS) $(ROOTS_STAMP) | $(CACHE_DIR) $(HINT_DIR)
	$(Q)$(FSTAR) $(OTHERFLAGS) --dep full $(ROOTS) --extract '* -Prims -LowStar -FStar' > $@

include $(DEPEND)

$(CACHE_DIR)/%$(CHECKED): | $(DEPEND) $(CACHE_DIR) $(HINT_DIR)
	$(Q)printf '[CHECK] %s\n' "$(basename $(notdir $*))"
	$(Q)$(FSTAR) $(OTHERFLAGS) $< --hint_file $(HINT_DIR)/$(notdir $*).hints

verify: $(addsuffix $(CHECKED),$(addprefix $(CACHE_DIR)/,$(notdir $(ROOTS))))

# `@fail(tc)` only ever meant "skip the prover", so a directive that has gone
# stale over-claims and nothing notices. Check the other direction too, after
# `verify` has filled $(CACHE_DIR) with the closure these runs read.
xfail: verify
	$(Q)FSTAR_BIN='$(FSTAR_BIN)' FSTAR_FLAGS='$(FSTAR_FLAGS) $(OTHERFLAGS)' \
	  CACHE_DIR='$(CACHE_DIR)' XFAIL_CACHE='$(XFAIL_CACHE)' \
	  SNAPSHOTS='$(SNAPSHOTS)' $(CURDIR)/xfail.sh $(XFAIL_DIRS)

describe:
	@echo "roots:     $(words $(ROOTS))"
	@echo "snapshots: $(words $(DIRS))"
	@echo "xfail:     $(words $(XFAIL_DIRS))"
	@echo "fstar:     $(FSTAR_BIN)"
	@echo "cache:     $(CACHE_DIR)"
	@echo "flags:     $(OTHERFLAGS)"

clean:
	rm -rf $(CURDIR)/.cache $(CURDIR)/.cache-lax $(CURDIR)/.cache-xfail \
	  $(CURDIR)/.cache-xfail-lax $(HINT_DIR) $(CURDIR)/.depend

Q ?= @
