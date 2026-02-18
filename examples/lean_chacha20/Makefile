.PHONY: default clean
default:
	cargo hax into lean
	(cd proofs/lean && \
   elan default v4.29.0-rc1 && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/
	-cd proofs/lean && lake clean
