RM=rm -f

SRC_FILES := $(wildcard ./src/*.ml)
CPL_FILES := $(wildcard ./_build/src/*.cmo)
TEST_FILES := $(wildcard ./tests/*_test.ml)

CFLAG = -cflag -rectypes -build-dir _build

all: ityper typer debug tests

typer:
	# ============================
	#     Build typer
	# ============================
	ocamlbuild src/main.native $(CFLAG)
	@mv _build/src/main.native _build/typer

# debug file eval
debug:
	# ============================
	#     Build debug utils
	# ============================
	ocamlbuild src/full_debug.native -I src $(CFLAG)
	@mv _build/src/full_debug.native _build/full_debug

# interactive typer
ityper:
	# ============================
	#    Build ityper
	# ============================
	ocamlbuild src/REPL.native -I src $(CFLAG)
	@mv _build/src/REPL.native _build/ityper

tests-build:
	# ============================
	#     Build tests
	# ============================
	@$(foreach test, $(TEST_FILES), ocamlbuild $(subst ./,,$(subst .ml,.native,$(test))) -I src $(CFLAG);)
	@ocamlbuild tests/utest_main.native -I src $(CFLAG)
	@mv _build/tests/utest_main.native _build/tests/utests

tests-run:
	# ============================
	#     Run tests
	# ============================
	@./_build/tests/utests --verbose= 3

tests: tests-build tests-run

# Make language doc
doc-tex:
	texi2pdf ./doc/manual.texi --pdf --build=clean

# Make implementation doc
doc-ocaml:
	ocamldoc -html -d _build/doc  $(SRC_FILES)

# everything is expected to be compiled in the "./_build/" folder
clean:
	-rm -rf _build

.PHONY: ityper typer debug tests
