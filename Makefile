V_FILES := $(wildcard *.v)
VO_FILES := $(V_FILE:.v=vo)

default: $(VO_FILES)

%.vo: %.v
	coqc -q $< -o $@
