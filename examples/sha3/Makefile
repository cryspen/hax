CHARON_EXE = charon
AENEAS_EXE = aeneas

AENEAS_OPTIONS ?= -loops-to-rec

.PHONY: extract
extract: sha3.llbc
	$(AENEAS_EXE) -backend lean sha3.llbc -split-files -dest proofs/Sha3 $(AENEAS_OPTIONS)

sha3.llbc: $(wildcard */*.rs)
	$(CHARON_EXE) cargo --preset=aeneas
	mv ../sha3.llbc ./sha3.llbc


.PHONY: default clean
default:
	extract
	(cd proofs/lean && \
   elan default v4.29.0-rc1 && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/*.lean
	-cd proofs/lean && lake clean
