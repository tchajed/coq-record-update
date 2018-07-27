V_FILES := $(wildcard *.v)
VO_FILES := $(V_FILES:.v=.vo)

default: $(VO_FILES)

%.vo: %.v
	coqc -q $< -o $@

Examples.vo: RecordSet.vo
