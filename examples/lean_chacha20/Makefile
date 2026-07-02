.PHONY: default clean
default:
	cargo hax into legacy-lean
	(cd proofs/legacy-lean && \
   elan default v4.29.0-rc1 && \
   lake build)

clean:
	-rm -f proofs/legacy-lean/extraction/
	-cd proofs/legacy-lean && lake clean
