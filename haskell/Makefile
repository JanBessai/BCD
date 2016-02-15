CABAL = cabal
CABAL_FLAGS =

all: cabal_configure cabal_build

cabal.sandbox.config:
	$(CABAL) $(CABAL_FLAGS) sandbox init

cabal_dependencies: cabal.sandbox.config
	$(CABAL) $(CABAL_FLAGS) install --dependencies-only

cabal_configure: cabal_dependencies
	$(CABAL) $(CABAL_FLAGS) configure

cabal_build: 
	$(CABAL) $(CABAL_FLAGS) build

.PHONY: clean
clean:
	$(CABAL) clean
	$(CABAL) sandbox delete
