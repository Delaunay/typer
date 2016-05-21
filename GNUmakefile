RM=rm -f

SRC_FILES := $(wildcard ./src/*.ml)
CPL_FILES := $(wildcard ./_build/src/*.cmo)
TEST_FILES := $(wildcard ./tests/*_test.ml)

OBFLAGS = -build-dir _build
# COMPILE_MODE = native

all: typer debug tests-build

ifeq ($(OS), Windows_NT)
# Windows need '-r' and building to native can be problematic (linking error)
# So we build to byte instead
OBFLAGS = $(OBFLAGS) -r
endif

COMPILE_MODE = byte




# debug file eval
debug:
	# ============================
	#     Build debug utils
	# ============================
	ocamlbuild src/debug_util.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv _build/src/debug_util.$(COMPILE_MODE)  _build/debug_util

# interactive typer
typer:
	# ============================
	#    Build typer
	# ============================
	ocamlbuild src/REPL.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv _build/src/REPL.$(COMPILE_MODE)  _build/typer

tests-build:
	# ============================
	#     Build tests
	# ============================
	@$(foreach test, $(TEST_FILES), ocamlbuild $(subst ./,,$(subst .ml,.$(COMPILE_MODE) ,$(test))) -I src $(OBFLAGS);)
	@ocamlbuild tests/utest_main.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv _build/tests/utest_main.$(COMPILE_MODE)  _build/tests/utests

tests-run:
	@./_build/tests/utests --verbose= 3

test-file:
	ocamlbuild src/test.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv _build/src/test.$(COMPILE_MODE)  _build/test

# There is nothing here. I use this to test if opam integration works
install: tests

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

.PHONY: typer debug tests

run/typecheck:
	@./_build/debug_util ./samples/test__.typer -typecheck

run/debug_util:
	@./_build/debug_util ./samples/test__.typer -fmt-type=on -fmt-index=off -fmt-pretty=on

run/typer:
	@./_build/typer

run/tests:
	@./_build/tests/utests --verbose= 1

run/typer-file:
	@./_build/typer ./samples/test__.typer

run/test-file:
	@./_build/test
