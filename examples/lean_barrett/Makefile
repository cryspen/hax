.PHONY: default clean
default:
	cargo hax into lean
	(cd proofs/lean && \
   elan default v4.29.0-rc1 && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/lean_barrett.lean
	-cd proofs/lean && lake clean
