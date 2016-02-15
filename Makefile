OASIS = oasis
COQC = coqc

default: all
all: coq haskell ocaml

world: all

.PHONY: coq
coq: 
	$(MAKE) -C coq all

coq/BCD.hs: coq
coq/BCD.ml: coq
coq/BCD.mli: coq

haskell/src/BCD.hs: coq/BCD.hs
	cp coq/BCD.hs haskell/src/

.PHONY: haskell
haskell: haskell/src/BCD.hs
	$(MAKE) -C haskell all


ocaml/src/extracted/BCD.ml: coq/BCD.ml coq/BCD.mli
	cp coq/BCD.ml coq/BCD.mli ocaml/src/extracted/

ocaml/Makefile: ocaml/src/extracted/BCD.ml
	cd ocaml && $(OASIS) setup -setup-update dynamic

.PHONY: ocaml
ocaml: ocaml/Makefile
	$(MAKE) -C ocaml all

.PHONY: clean
clean:
	$(MAKE) -C coq mrproper 
	$(MAKE) -C haskell clean
	$(MAKE) -C ocaml mrproper


