default: RecordSet.vo

examples: Examples.vo

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

%.vo: %.v Makefile.coq
	make -f Makefile.coq $@

clean:
	make -f Makefile.coq clean

install:
	make -f Makefile.coq install

.PHONY: default examples clean install
