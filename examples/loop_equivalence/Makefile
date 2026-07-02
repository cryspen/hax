.PHONY: default clean
default:
	cargo hax into aeneas-lean --aeneas-args="-core-models-lib"
	(cd proofs/aeneas-lean && \
   elan default v4.30.0-rc2 && \
   lake exe cache get && \
   lake build)

clean:
	-find proofs/aeneas-lean/LoopEquivalence/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/aeneas-lean && lake clean
