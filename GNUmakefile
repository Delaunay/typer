RM=rm -f

SRC_FILES := $(wildcard ./src/*.ml)
CPL_FILES := $(wildcard ./_build/src/*.cmo)
TEST_FILES := $(wildcard ./tests/*_test.ml)

OBFLAGS = -build-dir _build

all: ityper typer debug tests-build

typer:
	# ============================
	#     Build typer
	# ============================
	ocamlbuild src/main.native $(OBFLAGS)
	@mv _build/src/main.native _build/typer

# debug file eval
debug:
	# ============================
	#     Build debug utils
	# ============================
	ocamlbuild src/debug_util.native -I src $(OBFLAGS)
	@mv _build/src/debug_util.native _build/debug_util

# interactive typer
ityper:
	# ============================
	#    Build ityper
	# ============================
	ocamlbuild src/REPL.native -I src $(OBFLAGS)
	@mv _build/src/REPL.native _build/ityper

tests-build:
	# ============================
	#     Build tests
	# ============================
	@$(foreach test, $(TEST_FILES), ocamlbuild $(subst ./,,$(subst .ml,.native,$(test))) -I src $(OBFLAGS);)
	@ocamlbuild tests/utest_main.native -I src $(OBFLAGS)
	@mv _build/tests/utest_main.native _build/tests/utests

tests-run:
	@./_build/tests/utests --verbose= 2

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
