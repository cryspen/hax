.PHONY: default fstar rust lean clean

default: fstar rust lean
	make -C proofs/fstar/extraction

fstar:
	cargo hax into fstar

rust:
	cargo hax into rust
	cd proofs/rust/extraction
	cargo build

lean:
	cargo hax into lean --aeneas-args="-core-models-lib"
	(cd proofs/lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	rm -f proofs/fstar/extraction/.depend
	rm -f proofs/fstar/extraction/*.fst
	rm -f proofs/rust/extraction/*.rs
	-find proofs/lean/Barrett/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/lean && lake clean
