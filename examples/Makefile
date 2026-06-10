.PHONY: default
default:
	make -C limited-order-book
	make -C chacha20
	make -C sha3
	make -C sha256
	make -C barrett
	make -C kyber_compress
	make -C loop_equivalence
	make -C proverif-psk
	make -C lean_chacha20
	make -C lean_barrett

clean:
	make -C limited-order-book clean
	make -C chacha20           clean
	make -C sha3               clean
	make -C sha256             clean
	make -C barrett            clean
	make -C kyber_compress     clean
	make -C loop_equivalence   clean
	make -C proverif-psk       clean
	make -C lean_chacha20      clean
	make -C lean_barrett       clean
