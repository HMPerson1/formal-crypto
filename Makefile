# from https://github.com/DistributedComponents/coqproject/blob/master/Makefile

default: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq Makefile.coq.conf

.PHONY: default clean
