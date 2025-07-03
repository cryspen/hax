.PHONY: default lean clean
default: lean
	make -C proofs/fstar/extraction

lean:
	cargo hax into lean

clean:
	rm -f proofs/fstar/extraction/.depend
	rm -f proofs/fstar/extraction/*.fst
