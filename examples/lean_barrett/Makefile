.PHONY:  lean clean

lean:
	cargo hax into lean --aeneas-args="-core-models-lib"
	(cd proofs/lean && \
   lake exe cache get && \
   lake build)

clean:
	-find proofs/lean/LeanBarrett/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/lean && lake clean
