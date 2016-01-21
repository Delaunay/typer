



all: typer debug tests

typer: 
	ocamlbuild src/main.byte

debug: 
	ocamlbuild src/debug.byte

# how to change exec dir ??
# tried  -install-bin-dir _build -build-dir _build

# currently each tests has its own executable
# Best would be one executable to print debug info
# and another one doing all the tests
tests: 
	ocamlbuild tests/prelexer_debug.byte -I src  # debug print
	ocamlbuild tests/lexer_debug.byte -I src	 # debug print

# Make language doc    
doc-tex:
	texi2pdf ./doc/manual.texi --pdf --build=clean

# Make implementation doc
doc-ocaml:
	ocamldoc 

.PHONY: typer
.PHONY: debug
.PHONY: tests
