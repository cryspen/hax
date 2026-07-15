.PHONY:  lean clean

lean:
	cargo hax into lean
	(cd proofs/lean && \
   lake exe cache get && \
   lake build)

clean:
	-find proofs/lean/LeanBarrett/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/lean && lake clean
