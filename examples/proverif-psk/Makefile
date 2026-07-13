# ProVerif extraction + analysis for the proverif-psk example.
#
# Extraction uses the hax `proverif` backend, which lives in the `hax-proverif`
# opam switch (install/refresh with `HAX_OPAM_SWITCH=hax-proverif ../../setup-local.sh`).
# `check` runs ProVerif on the extracted model composed with the shipped symbolic
# libraries (primitives.pvl + cryptolib.pvl) and the handwritten analysis harness.

SWITCH     := hax-proverif
HAX_LIB    := ../../hax-lib/proof-libs/proverif
EXTRACTION := proofs/proverif/extraction

.PHONY: check extract clean

# Run ProVerif on the extracted model + the analysis harness.
check: $(EXTRACTION)/lib.pvl
	proverif -lib $(HAX_LIB)/primitives \
	         -lib $(HAX_LIB)/cryptolib \
	         -lib $(EXTRACTION)/missingdecl \
	         -lib $(EXTRACTION)/lib \
	         proofs/proverif/analysis.pv

# (Re-)extract the ProVerif model from the Rust source via the hax-proverif switch.
extract $(EXTRACTION)/lib.pvl:
	eval "$$(opam env --switch=$(SWITCH))" && cargo hax into proverif

clean:
	rm -f $(EXTRACTION)/lib.pvl
