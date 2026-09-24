.PHONY: fstar clean

fstar:
	cargo hax extract chacha20
	make -C proofs/chacha20/fstar/extraction

clean:
	rm -f proofs/chacha20/fstar/extraction/.depend
	rm -f proofs/chacha20/fstar/extraction/*.fst
