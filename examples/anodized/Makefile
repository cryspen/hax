# Extract the same `#[spec(..)]` annotations through two backends, to check
# that `anodized`'s cfg flags reach both pipelines: F* gets them through
# `RUSTFLAGS`, while Lean goes through charon, which compiles proc-macro
# crates -- `anodized-macros` among them -- with `host.rustflags` instead.
.PHONY: default fstar lean clean

default: fstar lean

fstar:
	make -C proofs/fstar/extraction

lean:
	cargo hax into lean
	(cd proofs/lean && \
		elan default $$(cat lean-toolchain) && \
		lake exe cache get && \
		lake build)

clean:
	rm -f proofs/fstar/extraction/.depend
	rm -f proofs/fstar/extraction/*.fst
	-rm -rf proofs/lean/AnodizedExample/Extraction
	-cd proofs/lean && lake clean
