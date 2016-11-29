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
open Lparse

open Builtin
open Env


let rctx = default_rctx

let make_val value = Vstring(value)


let _ = (add_test "ENV" "Set Variables" (fun () ->

    if 10 <= (!_global_verbose_lvl) then (

        let var = [
            ((Some "a"), DB.type_int, (make_val "a"));
            ((Some "b"), DB.type_int, (make_val "b"));
            ((Some "c"), DB.type_int, (make_val "c"));
            ((Some "d"), DB.type_int, (make_val "d"));
            ((Some "e"), DB.type_int, (make_val "e"));
        ] in

        let n = (List.length var) - 1 in

        let rctx = List.fold_left (fun ctx (n, t, _) ->
            add_rte_variable n (Vdummy) ctx)
            rctx var in

        print_rte_ctx rctx;

        let rctx, _ = List.fold_left
                        (fun (ctx, idx) (n, _, v) ->
                          (set_rte_variable idx n (Vdummy) ctx);
                          (ctx, idx - 1))
                        (rctx, n) var in

        print_rte_ctx rctx;

        success ()
    )
    else
        success ()

))


(* run all tests *)
let _ = run_all ()
