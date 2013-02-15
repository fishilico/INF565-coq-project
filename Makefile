COQC=coqc -batch
SOURCES=$(wildcard *.v)
OBJECTS=$(SOURCES:%.v=%.vo)
GLOBS=$(SOURCES:%.v=%.glob)

.PHONY: all clean doc

all: $(OBJECTS)

clean:
	rm -f $(OBJECTS) $(GLOBS)
	rm -rf doc

doc: $(OBJECTS)
	[ -d $@ ] || mkdir $@
	coqdoc -d $@ $(SOURCES)

%.vo: %.v
	$(COQC) -batch $<
	@rm -f $(GLOB_TMP_FILE)

beta_reduction.vo: lterm.vo substitution.vo
free_variables.vo: Arith_ext.vo lterm.vo
substitute_list.vo: Arith_ext.vo free_variables.vo lterm.vo substitute_varlist.vo
substitute_varlist.vo: Arith_ext.vo lterm.vo substitution.vo
substitution.vo: Arith_ext.vo free_variables.vo lterm.vo
