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
let ectx = default_ectx
let rctx = default_rctx

let _ = (add_test "MACROS" "macros base" (fun () ->

    (* define 'lambda x -> x * x' using macros *)
    let dcode = "
    my_fun = lambda (x : List Sexp) ->
        let hd = (case x
          | cons hd tl => hd
          | nil => symbol_ \"x\") : Sexp in
            (node_ (symbol_ \"_*_\")
              (cons hd (cons hd nil)));

    sqr = Macro_ my_fun;
    " in

    let rctx, ectx = eval_decl_str dcode ectx rctx in

    let ecode = "(lambda (x : Int) -> sqr 3) 5;" in

    let ret = eval_expr_str ecode ectx rctx in

        match ret with
            | [Vint(r)] -> expect_equal_int r (3 * 3)
            | _ -> failure ())
)


let _ = (add_test "MACROS" "macros decls" (fun () ->
    let dcode = "
      decls-impl = lambda (x : List Sexp) ->
        cons (node_ (symbol_ \"_=_\")
          (cons (symbol_ \"a\") (cons (integer_ 1) nil)))
       (cons (node_ (symbol_ \"_=_\")
        (cons (symbol_ \"b\") (cons (integer_ 2) nil))) nil);

      my-decls = DMacro_ decls-impl;

      my-decls Nat;" in

    let rctx, ectx = eval_decl_str dcode ectx rctx in

    let ecode = "a; b;" in

    let ret = eval_expr_str ecode ectx rctx in

        match ret with
            | [Vint(a); Vint(b)] ->
                if (a = 1 && b = 2) then success () else failure ()

            | _ -> failure ())
)


(* run all tests *)
let _ = run_all ()
