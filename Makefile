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
compiler_correct.vo: beta_reduction.vo compiler.vo free_variables.vo krivine.vo
compiler_correct.vo: lterm.vo substitute_list.vo substitute_varlist.vo
compiler.vo: free_variables.vo krivine.vo lterm.vo substitute_list.vo
free_variables.vo: lterm.vo
identity.vo: beta_reduction.vo compiler.vo compiler_correct.vo free_variables.vo krivine.vo lterm.vo
substitute_list.vo: free_variables.vo lterm.vo substitution.vo substitute_varlist.vo
substitute_varlist.vo: lterm.vo substitution.vo
substitution.vo: free_variables.vo lterm.vo
