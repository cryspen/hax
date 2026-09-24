.PHONY: fstar clean

fstar:
	cargo hax extract kyber-compress
	make -C proofs/kyber-compress/fstar/extraction

clean:
	rm -f proofs/kyber-compress/fstar/extraction/.depend
	rm -f proofs/kyber-compress/fstar/extraction/*.fst
