OCAMLC = ocamlc
OCAMLDEP = ocamldep
OCAMLC_FLAGS = -annot -g
OCAMLLD = ocamlc
OCAMLLD_FLAGS = -g
RM = rm -f

FILES = $(wildcard *.ml)

# OCAMLC wants its object files in the right order so the modules get
# initialized correctly.  Ideally `make' should do this job (it already has
# the dependency info and knows all too weel how to do a topological sort),
# but I don't know how to get `make' to do what I want, so I used some `sed'
# magic to massage the .depend in a form that `tsort' can take.
ORDERED_OBJECTS = $(shell sed -e '/\([^ :]*\.cmo\) *:/{ : start; s/^\([^ :]*\) *: *\([^ :\\][^ :\\]*\)/\2 \1\n\1:/; t loop2; /\\$$/{; N; s/\\.//; b start}; d; : loop2; P; D}; d' .depend | tsort)

all: typer

%.cmi %.cmo: %.ml
	$(OCAMLC) $(OCAMLC_FLAGS) -c $<

clean:
	$(RM) *.cmo *.cmi *.cmx *.annot

typer: $(ORDERED_OBJECTS) #$(FILES:.ml=.cmo)
	$(OCAMLLD) $(OCAMLLD_FLAGS) -o $@ $(ORDERED_OBJECTS)

.PHONY: test
# The "OCAMLRUNPARAM=-b" is so as to cause ocamlrun to print a backtrace
# when an exception is not caught.
test: typer
	OCAMLRUNPARAM=-b ./typer test.typer

depend:
	$(OCAMLDEP) $(FILES) > .depend

-include .depend
