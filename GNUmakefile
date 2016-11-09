RM=rm -f
MV=mv
OCAMLBUILD=ocamlbuild

BUILDDIR        := _build

SRC_FILES := $(wildcard ./src/*.ml)
CPL_FILES := $(wildcard ./$(BUILDDIR)/src/*.cmo)
TEST_FILES := $(wildcard ./tests/*_test.ml)

OBFLAGS = -lflags -g -cflags -g -build-dir $(BUILDDIR)
# OBFLAGS         := -I $(SRCDIR) -build-dir $(BUILDDIR) -pkg str
# OBFLAGS_DEBUG   := -tag debug -tag profile -tag "warn(+20)"
# OBFLAGS_RELEASE := -tag unsafe -tag inline
COMPILE_MODE = byte
# COMPILE_MODE = native

# DEBUG           ?= 1
# VERBOSE         ?= 1

all: typer debug tests-build

# ifeq ($(OS), Windows_NT)
# Windows need '-r' and building to native can be problematic (linking error)
# So we build to byte instead
# OBFLAGS = $(OBFLAGS) -r
# endif

# ifeq ($(DEBUG), 1)
# 	OBFLAGS += $(OBFLAGS_DEBUG)
# else
# 	OBFLAGS += $(OBFLAGS_RELEASE)
# endif

help: ## Prints help for targets with comments
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST)   \
		| { echo -e 'typer:  ## Build Typer'; sort; } \
		| awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'

# debug file eval
debug:
	# ============================
	#     Build debug utils
	# ============================
	$(OCAMLBUILD) src/debug_util.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@$(MV) $(BUILDDIR)/src/debug_util.$(COMPILE_MODE)  $(BUILDDIR)/debug_util

# interactive typer
typer:
	# ============================
	#    Build typer
	# ============================
	$(OCAMLBUILD) src/REPL.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@$(MV) $(BUILDDIR)/src/REPL.$(COMPILE_MODE)  $(BUILDDIR)/typer

tests-build:
	# ============================
	#     Build tests
	# ============================
	@$(foreach test, $(TEST_FILES), 				  \
	   $(OCAMLBUILD) $(subst ./,,$(subst .ml,.$(COMPILE_MODE) ,$(test))) \
	              -I src $(OBFLAGS);)
	@$(OCAMLBUILD) tests/utest_main.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@$(MV) $(BUILDDIR)/tests/utest_main.$(COMPILE_MODE) \
	    $(BUILDDIR)/tests/utests

tests-run:
	@./$(BUILDDIR)/tests/utests --verbose= 3

test-file:
	$(OCAMLBUILD) src/test.$(COMPILE_MODE)  -I src $(OBFLAGS)
	@$(MV) $(BUILDDIR)/src/test.$(COMPILE_MODE)  $(BUILDDIR)/test

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
