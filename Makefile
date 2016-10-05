
# TODO : find a way to have debug only function

# Name of the target binary program
TARGET          := typer
CC              := ocamlbuild
RM              := rm -rf
MV              := mv

#COMPILE_MODE    := native
COMPILE_MODE    := byte

BUILDDIR        := _build
TESTDIR         := tests
SRCDIR          := src

OBFLAGS         := -I $(SRCDIR) -build-dir $(BUILDDIR) -pkg str
OBFLAGS_DEBUG   := -tag debug -tag profile -tag "warn(+20)"
OBFLAGS_RELEASE := -tag unsafe -tag inline

DEBUG           ?= 1
VERBOSE         ?= 1

#---------------------------------------------------------------------------------
#DO NOT EDIT BELOW THIS LINE
#---------------------------------------------------------------------------------

ifeq ($(DEBUG), 1)
	OBFLAGS += $(OBFLAGS_DEBUG)
else
	OBFLAGS += $(OBFLAGS_RELEASE)
endif

BUILDTEST    := $(BUILDDIR)/$(TESTDIR)
BUILDSRC     := $(BUILDDIR)/$(SRCDIR)


SRC_FILES    := $(wildcard $(SRCDIR)/*.ml)
CPL_FILES    := $(patsubst $(SRCDIR)/%,$(BUILDSRC)/%,$(SRC_FILES:.ml=.cmo))
TEST_FILES   := $(wildcard ./$(TESTDIR)/*_test.ml)


TESTTARGETS  := $(patsubst ./$(TESTDIR)/%,$(BUILDTEST)/%,$(TEST_FILES:.ml=.$(COMPILE_MODE)))

all: $(TARGET) debug tests-build ## Build typer, debug-util and tests

ifndef SYSTEMROOT
help: ## Prints help for targets with comments
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) \
		| { echo -e 'typer:  ## Build Typer'; sort; } \
		| awk 'BEGIN {FS = ":.*?## "}; {printf "\033[36m%-30s\033[0m %s\n", $$1, $$2}'
endif

generate_debug_fun:
ifeq ($(DEBUG), 1)
ifeq ($(VERBOSE), 1)
	@sed 's/__debug__/true/' src/debug_fun.ml.tpl > src/debug_fun.ml
	@echo -e "Debug logging enabled"
else
	@sed 's/__debug__/false/' src/debug_fun.ml.tpl > src/debug_fun.ml
	@echo -e "Debug logging disabled"
endif
else
	@sed 's/__debug__/false/' src/debug_fun.ml.tpl > src/debug_fun.ml
	@echo -e "Debug logging disabled"
endif


# debug file eval
debug: generate_debug_fun $(SRCDIR)/debug_util.ml ## Build debug utils
	# ============================
	#     Build debug utils
	# ============================
	@$(CC) src/debug_util.$(COMPILE_MODE)  $(OBFLAGS)
	@$(MV) _build/src/debug_util.$(COMPILE_MODE)  _build/debug_util

# interactive typer
$(TARGET): generate_debug_fun $(SRC_FILES) ## Build typer
	# ============================
	#    Build typer
	# ============================
	@$(CC) src/REPL.$(COMPILE_MODE)  $(OBFLAGS)
	@$(MV) _build/src/REPL.$(COMPILE_MODE)  _build/$(TARGET)

tests-build: $(TESTTARGETS)
	# ============================
	#     Build tests
	# ============================
	@$(CC) tests/utest_main.$(COMPILE_MODE) $(OBFLAGS)
	@$(MV) _build/tests/utest_main.$(COMPILE_MODE)  _build/tests/utests

$(BUILDTEST)/%.$(COMPILE_MODE): $(TESTDIR)/%.ml
	@$(CC) $(<:.ml=.$(COMPILE_MODE)) $(OBFLAGS)

tests-run:
	@./_build/tests/utests --verbose= 3

test-file:
	@$(CC) src/test.$(COMPILE_MODE)  $(OBFLAGS)
	@$(MV) _build/src/test.$(COMPILE_MODE)  _build/test

# There is nothing here. I use this to test if opam integration works
install: tests

tests: generate_debug_fun tests-build tests-run ## Build tests

# Make language doc
doc-tex: ## Make language doc
	@texi2pdf ./doc/manual.texi --pdf --build=clean
	@make -C ./doc/rapport

# Make implementation doc
doc-ocaml: ## Make implementation doc
ifndef SYSTEMROOT
	@ls $(SRC_FILES)\
		| grep -v "src/unify.ml"\
		| grep -v "src/elaborate.ml"\
		| grep -v "ulexp.ml"\
		| grep -v "src/subst.ml"\
		| grep -v "javascript.ml"\
		| awk 'BEGIN { FS = "[/.]" }\
		{ printf "%s/%s%s\n", $$1, substr($$2,1,1), substr($$2,2) }' > project.odocl
	@$(CC) project.docdir/index.html $(OBFLAGS) # -docflag "-charset 'UTF8'"
	@sed -i.bak 's/iso-8859-1/UTF-8/' _build/project.docdir/*.html
endif

# everything is expected to be compiled in the "./_build/" folder
clean: ## Clean everything in BUILDDIR
	@$(RM) $(BUILDDIR)
	@$(RM) project.docdir
	@$(RM) *.odocl

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

