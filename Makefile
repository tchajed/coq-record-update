default: RecordSet.vo

examples: Examples.vo

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

Examples.vo: Examples.v RecordSet.vo
	coqc -R . RecordSet -q $< -o $@


%.vo: %.v Makefile.coq
	make -f Makefile.coq $@

clean:
	make -f Makefile.coq clean

install: RecordSet.vo
	make -f Makefile.coq install

.PHONY: default examples clean install
