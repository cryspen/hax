.PHONY: default lean aeneas-lean clean

default: lean aeneas-lean

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

clean:
	-rm -f proofs/lean/extraction/Lean_barrett.lean
	-cd proofs/lean && lake clean
	-rm -f proofs/aeneas-lean/LeanBarrett/Extraction/Funs.lean
	-cd proofs/aeneas-lean && lake clean
