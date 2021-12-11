.ONESHELL:

clean-lib:
	cd lib && $(MAKE) clean
.PHONY: clean-lib

clean-src:
	cd src && $(MAKE) clean
.PHONY: clean-src

lib:
	cd lib
	coq_makefile *.v -f _CoqProject -o Makefile
	$(MAKE)
.PHONY: lib

src:
	cd src
	coq_makefile *.v -f _CoqProject -o Makefile
	$(MAKE)
.PHONY: src