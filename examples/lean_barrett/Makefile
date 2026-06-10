.PHONY: default lean aeneas-lean clean
lean:
	cargo hax into lean
	(cd proofs/lean && \
   elan default v4.29.0-rc1 && \
   lake build)
   
aeneas-lean:
	cargo hax into aeneas-lean --aeneas-args="-core-models-lib"
	(cd proofs/aeneas-lean && \
   elan default v4.30.0-rc2 && \
   lake exe cache get && \
   lake build)
   
default: lean aeneas-lean

clean:
	-rm -f proofs/lean/extraction/Lean_barrett.lean
	-cd proofs/lean && lake clean
