RM=rm -f

BUILDDIR        := _build

SRC_FILES := $(wildcard ./src/*.ml)
CPL_FILES := $(wildcard ./$(BUILDDIR)/src/*.cmo)
TEST_FILES := $(wildcard ./tests/*_test.ml)

OBFLAGS = -lflags -g -cflags -g -build-dir $(BUILDDIR)
# COMPILE_MODE = native

all: typer debug tests-build

# ifeq ($(OS), Windows_NT)
# Windows need '-r' and building to native can be problematic (linking error)
# So we build to byte instead
# OBFLAGS = $(OBFLAGS) -r
# endif

COMPILE_MODE = byte

# debug file eval
debug:
	# ============================
	#     Build debug utils
	# ============================
	ocamlbuild src/debug_util.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv $(BUILDDIR)/src/debug_util.$(COMPILE_MODE)  $(BUILDDIR)/debug_util

# interactive typer
typer:
	# ============================
	#    Build typer
	# ============================
	ocamlbuild src/REPL.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv $(BUILDDIR)/src/REPL.$(COMPILE_MODE)  $(BUILDDIR)/typer

tests-build:
	# ============================
	#     Build tests
	# ============================
	@$(foreach test, $(TEST_FILES), 				  \
	   ocamlbuild $(subst ./,,$(subst .ml,.$(COMPILE_MODE) ,$(test))) \
	              -I src $(OBFLAGS);)
	@ocamlbuild tests/utest_main.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv $(BUILDDIR)/tests/utest_main.$(COMPILE_MODE) \
	    $(BUILDDIR)/tests/utests

tests-run:
	@./$(BUILDDIR)/tests/utests --verbose= 3

test-file:
	ocamlbuild src/test.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@mv $(BUILDDIR)/src/test.$(COMPILE_MODE)  $(BUILDDIR)/test

# There is nothing here. I use this to test if opam integration works
install: tests

tests: tests-build tests-run

# Make language doc
doc-tex:
	texi2pdf ./doc/manual.texi --pdf --build=clean

# Make implementation doc
doc-ocaml:
	ocamldoc -html -d $(BUILDDIR)/doc  $(SRC_FILES)

# everything is expected to be compiled in the "./$(BUILDDIR)/" folder
clean:
	-rm -rf $(BUILDDIR)

.PHONY: typer debug tests

run/typecheck:
	@./$(BUILDDIR)/debug_util ./samples/test__.typer -typecheck

run/debug_util:
	@./$(BUILDDIR)/debug_util ./samples/test__.typer \
	                          -fmt-type=on -fmt-index=off -fmt-pretty=on

run/typer:
	@./$(BUILDDIR)/typer

run/tests:
	@./$(BUILDDIR)/tests/utests --verbose= 1

run/typer-file:
	@./$(BUILDDIR)/typer ./samples/test__.typer

run/test-file:
	@./$(BUILDDIR)/test
