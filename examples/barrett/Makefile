.PHONY: default fstar rust clean

default: fstar rust aeneas-lean

aeneas-lean:
	cargo hax into aeneas-lean --aeneas-args="-core-models-lib"
	(cd proofs/aeneas-lean && \
		lake exe cache get && \
		lake build)

fstar:
	cargo hax into fstar
	make -C proofs/fstar/extraction

rust:
	cargo hax into rust
	cd proofs/rust/extraction
	cargo build

clean:
	find proofs/aeneas-lean/LeanBarrett/Extraction -type f ! -name FunsExternal.lean -delete
	(cd proofs/aeneas-lean && lake clean)
	rm -f proofs/fstar/extraction/.depend
	rm -f proofs/fstar/extraction/*.fst
	rm -f proofs/rust/extraction/*.rs
