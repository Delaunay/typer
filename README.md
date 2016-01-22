
Typer
=====

# How to build Typer

## Requirement

* Ocaml 4.01

## Build

By default ocamlbuild creates a '_build' folder which holds all the compiled files.

* make typer: build typer interpreter       'typer'
* make debug: build typer with debug info   'debug'
* make tests: run interpreter's tests       '/.tests/utest_main.byte'

# Directory layout

* src/ interpreter's source
* doc/ interpreter's doc files
* sample/ typer code sample for testing purposes
* tests/  ocaml test files
    
# Emacs files

    /typer-mode.el
    
    