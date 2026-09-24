.PHONY: fstar

fstar:
	cargo hax extract sha256
	make -C proofs/sha256/fstar/extraction

clean:
	rm -f proofs/sha256/fstar/extraction/.depend
	rm -f proofs/sha256/fstar/extraction/*.fst
