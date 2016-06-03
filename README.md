
Typer
=====

# How to build Typer

Status [![Build Status](https://travis-ci.org/Delaunay/typer.svg?branch=master)](https://travis-ci.org/Delaunay/typer)

## Requirement

* Ocaml 4.01

## Build

By default ocamlbuild creates a '_build' folder which holds all the compiled files.

* `make typer`: build typer interpreter       './typer'
* `make debug`: build typer with debug info   './debug_util'
* `make tests`: run interpreter's tests       './tests/utests'

# Directory layout

* `src/` interpreter's source
* `doc/` interpreter's doc files
* `sample/` typer code sample for testing purposes
* `tests/`  ocaml test files
* `btl/`    builtin typer library

# Emacs files

    /typer-mode.el

