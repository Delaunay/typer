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

open Utest_lib

open Pexp
open Lexp
open Lparse     (* add_def       *)

open Builtin

(* default environment *)
let ectx = default_ectx
let rctx = default_rctx

(*)
let _ = (add_test "LEXP" "lexp_print" (fun () ->

    let dcode = "
sqr : (x : Int) -> Int;
sqr = lambda (x : Int) ->
  (x * x);

cube : (x : Int) -> Int;
cube = lambda (x : Int) ->
  (x * (sqr x));

mult : (x : Int) -> (y : Int) -> Int;
mult = lambda (x : Int) ->
  lambda (y : Int) ->
    (x * y);

twice : (y : Int) -> Int;
twice = (mult 2);

let_fun : (x : Int) -> Int;
let_fun = lambda (x : Int) ->
  let a : Int;
    a = (twice x); in
      let b : Int;
        b = (mult 2 x); in
          (a + b);" in

    let ret1, _ = lexp_decl_str dcode ectx in

    let to_str decls =
        let str = _lexp_str_decls pretty_ppctx (List.flatten ret1) in
            List.fold_left (fun str lxp -> str ^ "\n" ^ lxp) "" str in

    (* Cast to string *)
    let str1 = (to_str ret1) ^ "\n" in

    print_string str1;

    (* read code again *)
    let ret2, _ = lexp_decl_str str1 ectx in

    (* Cast to string *)
    let str2 = to_str ret2 in

    if str1 = str2 then success () else failure ()
)) *)

(*
let set_to_list s =
    StringSet.fold (fun g a -> g::a) s []

let _ = (add_test "LEXP" "Free Variable" (fun () ->

    let dcode = "
        a = 2;
        b = 3;
        f = lambda n -> (a + n);           % a is a fv
        g = lambda x -> ((f b) + a + x);   % f,a,b are fv
    " in

    let ret = pexp_decl_str dcode in
    let g = match List.rev ret with
        | (_, g, _)::_ -> g
        | _ -> raise (Unexpected_result "Unexpected empty list") in

    let (bound, free) = free_variable g in

    let bound = set_to_list bound in
    let (free, _) = free in

    match bound with
        | ["x"] ->(
            match free with
                | ["_+_"; "f"; "b"; "a"] -> success ()
                | _ -> failure ())
        | _ -> failure ()

)) *)

(* run all tests *)
let _ = run_all ()
