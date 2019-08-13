# from https://github.com/DistributedComponents/coqproject/blob/master/Makefile

.PHONY: default
default: Makefile.coq
	$(MAKE) -f Makefile.coq

.PHONY: install
install: Makefile.coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

.PHONY: clean
clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq Makefile.coq.conf
