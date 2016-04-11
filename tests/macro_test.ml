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


let get_int lxp =
    let lxp = get_value_lexp lxp in
    match lxp with
        | Imm(Integer(_, l)) -> l
        | _ -> (-40);
;;


(* default environment *)
let lctx = default_lctx ()
let rctx = default_rctx ()


let _ = (add_test "MACROS" "Variable Cascade" (fun () ->
    reset_eval_trace ();

    let dcode = "
        a = 10;
        b = a;
        c = b;
        d = c;" in

    let rctx, lctx = eval_decl_str dcode lctx rctx in

    let ecode = "d;" in

    let ret = eval_expr_str ecode lctx rctx in

        match ret with
            | [r] -> expect_equal_int (get_int r) 10
            | _ -> failure ())
);;


(* run all tests *)
run_all ()
;;