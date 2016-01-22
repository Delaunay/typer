
TEST_FILES := $(wildcard ./tests/*_test.ml)

all: typer debug tests

typer: 
	ocamlbuild src/main.byte
	mv _build/src/main.byte _build/typer # move and rename executable

debug: 
	ocamlbuild tests/prelexer_debug.byte -I src  # debug print
	mv _build/tests/prelexer_debug.byte _build/prelexer_debug
	ocamlbuild tests/lexer_debug.byte -I src     # debug print
	mv _build/tests/lexer_debug.byte _build/lexer_debug

tests: 
	# Build tests
	$(foreach test, $(TEST_FILES), ocamlbuild $(subst ./,,$(subst .ml,.byte,$(test))) -I src;)

	# Run tests
	ocamlbuild tests/utest_main.byte
	./_build/tests/utest_main.byte

# Make language doc    
doc-tex:
	texi2pdf ./doc/manual.texi --pdf --build=clean

# Make implementation doc
doc-ocaml:
	ocamldoc 

.PHONY: typer
.PHONY: debug
.PHONY: tests
