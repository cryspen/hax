.PHONY:  aeneas-lean clean

aeneas-lean:
	cargo hax into aeneas-lean --aeneas-args="-core-models-lib"
	(cd proofs/aeneas-lean && \
   lake exe cache get && \
   lake build)

clean:
	-find proofs/aeneas-lean/LeanBarrett/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/aeneas-lean && lake clean
