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
open Debruijn


let lctx = default_lctx ()

let make_val value = Imm(String(dloc, value))


let _ = (add_test "DEBRUIJN" "Set Variables" (fun () ->

    if 10 <= (!_global_verbose_lvl) then (

        let var = [
            ("za", Some type_float, type_int, Some type_int, type_float);
            ("zb", Some type_float, type_int, Some type_int, type_float);
            ("zc", Some type_float, type_int, Some type_int, type_float);
            ("zd", Some type_float, type_int, Some type_int, type_float);
        ] in

        let n = (List.length var) - 1 in

        let lctx = List.fold_left (fun ctx (n, l, t, _, _) ->
            env_extend ctx (dloc, n) l t) lctx var in

        print_lexp_ctx lctx;

        let _, _ = List.fold_left (fun (ctx, idx) (n, _, _, l, t) ->
            let _ = (env_set_var_info ctx ((dloc, n), idx) l t) in
            (ctx, idx - 1))
            (lctx, n) var in

        print_lexp_ctx lctx;

        success ()
    )
    else
        success ()

))



(* run all tests *)
let _ = run_all ()
