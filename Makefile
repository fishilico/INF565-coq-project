COQC=coqc -batch
SOURCES=$(wildcard *.v)
OBJECTS=$(SOURCES:%.v=%.vo)
GLOBS=$(SOURCES:%.v=%.glob)

.PHONY: all clean deps doc

all: $(OBJECTS)

clean:
	rm -f $(OBJECTS) $(GLOBS)
	rm -rf doc

doc: $(OBJECTS)
	[ -d $@ ] || mkdir $@
	coqdoc -d $@ $(SOURCES)

%.vo: %.v
	$(COQC) $<
	@rm -f $(GLOB_TMP_FILE)

# Compute file dependencies
deps: $(SOURCES)
	@for SRC in $^ ; do \
		sed -n -e 's/^Require Import \(.*\)\./ \1 /p' < $$SRC | \
		sed -n -e 's/ List / /' -e 's/ Arith / /' -e 's/^ *$$//' \
			-e 's/ /.vo /g' -e 's/ $$//' -e 's/^.vo/'"$${SRC}"'o:/p' ; \
	done | sort

beta_reduction.vo: lterm.vo substitution.vo
compiler_correct.vo: beta_reduction.vo compiler.vo krivine.vo lterm.vo substitute_list.vo
compiler.vo: free_variables.vo krivine.vo lterm.vo substitute_list.vo
free_variables.vo: Arith_ext.vo lterm.vo
identity.vo: compiler.vo free_variables.vo krivine.vo lterm.vo
substitute_list.vo: Arith_ext.vo free_variables.vo lterm.vo substitute_varlist.vo
substitute_varlist.vo: Arith_ext.vo lterm.vo substitution.vo
substitution.vo: Arith_ext.vo free_variables.vo lterm.vo
