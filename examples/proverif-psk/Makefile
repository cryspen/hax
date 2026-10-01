check: ./proofs/psk/proverif/extraction/lib.pvl
	timeout 30 proverif -lib ./proofs/psk/proverif/extraction/lib.pvl ./proofs/psk/proverif/analysis.pv

proofs/psk/proverif/extraction/lib.pvl:
	cargo hax extract psk

clean:
	rm -f proofs/psk/proverif/extraction/lib.pvl
