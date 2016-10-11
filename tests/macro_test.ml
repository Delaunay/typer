(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * --------------------------------------------------------------------------- *)

open Util
open Utest_lib

open Sexp
open Lexp

open Lparse     (* eval string      *)
open Eval       (* reset_eval_trace *)

open Builtin
open Env


(* default environment *)
let lctx = default_lctx
let rctx = default_rctx

let _ = (add_test "MACROS" "macros base" (fun () ->

    (* define 'lambda x -> x * x' using macros *)
    let dcode = "
    my_fun = lambda (x : List Sexp) ->
        let hd = head(a := Sexp) x in
            (node_ (symbol_ \"_*_\") (cons(a := Sexp) hd (cons(a := Sexp) hd (nil(a := Sexp)))));

    sqr = Macro_ my_fun;
    " in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let ecode = "(sqr 3);" in

    let ret = eval_expr_str ecode lctx rctx in

        match ret with
            | [Vint(r)] -> expect_equal_int r (3 * 3)
            | _ -> failure ())
)


let _ = (add_test "MACROS" "macros decls" (fun () ->
    let dcode = "
      decls-impl = lambda (x : List Sexp) ->
        cons(a := Sexp) (node_ (symbol_ \"_=_\")
          (cons(a := Sexp) (symbol_ \"a\") (cons(a := Sexp) (integer_ 1) (nil(a := Sexp)))))
       (cons(a := Sexp) (node_ (symbol_ \"_=_\")
        (cons(a := Sexp) (symbol_ \"b\") (cons(a := Sexp) (integer_ 2) (nil(a := Sexp))))) (nil(a := Sexp)));

      my-decls = Macro_ decls-impl;

      my-decls Nat;" in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let ecode = "a; b;" in

    let ret = eval_expr_str ecode lctx rctx in

        match ret with
            | [Vint(a); Vint(b)] ->
                if (a = 1 && b = 2) then success () else failure ()

            | _ -> failure ())
)


(* run all tests *)
let _ = run_all ()
