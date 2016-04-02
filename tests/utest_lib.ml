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
 * ---------------------------------------------------------------------------
 *
 *      Description:
 *          utest library utility.  Tests register themselves
 *
 * --------------------------------------------------------------------------- *)

open Util
open Fmt

module StringMap =
    Map.Make (struct type t = string let compare = String.compare end)
;;


type test_fun = (unit -> int)
type tests = (test_fun) StringMap.t
type sections = ((tests) StringMap.t) * string list

let success () = 0;;
let failure () = (-1);;

(*
 *  SECTION NAME - TEST NAME   - FUNCTION (() -> int)
 *      "Let"    - "Base Case" - (fun () -> success )
 *      "Let"    - "Recursive"
 *      "Lambda" - "Base Case"
 *      "Lambda" - "Nested"
 *)
let _global_sections = ref StringMap.empty
let _insertion_order = ref []
let _ret_code = ref 0
let _number_test = ref 0

(*  Exception *)
exception Unexpected_result of string

(*  Argument Parsing                        *)
(* ---------------------------------------- *)

(*
 *  0: Nothing
 *  1: Print:            (x/N) file_test .................... pass
 *  2: Print Each composing Test
 *  3: use debug
 *)
let _global_verbose_lvl = ref 0
let _global_sample_dir = ref ""

let arg_defs = [
    ("--verbose=",
        Arg.Int (fun g -> _global_verbose_lvl := g), " Set verbose level");
    ("--samples=",
        Arg.String (fun g -> _global_sample_dir := g), " Set sample directory");
];;

let parse_args () = Arg.parse arg_defs (fun s -> ()) ""


(* Utest printing function                  *)
(* ---------------------------------------- *)
let ut_string vb msg = if vb <= (!_global_verbose_lvl) then print_string msg else ()
let ut_string2 = ut_string 2


(* Value Checking                                           *)
(*      USAGE: expect_something_type value expected_value   *)
(*          return success() if match else failure ()       *)
let unexpected_throw sk tk e =
    ut_string2 (red ^ "[   FAIL] " ^ sk ^ " - " ^ tk ^ "\n");
    ut_string2        "[       ]     UNEXPECTED THROW:\n";
    ut_string2        "[       ]  "; ut_string2 ((Printexc.to_string e) ^ "\n" ^ reset);
;;

let _expect_equal_t to_string value expect =
    if value = expect then
        success ()
    else(
        ut_string2 (red ^ "[       ]     EXPECTED: " ^ (to_string expect)^ "\n");
        ut_string2 (      "[       ]          GOT: " ^ (to_string value) ^ "\n" ^ reset);
        failure ())
;;

let expect_equal_int   = _expect_equal_t string_of_int
let expect_equal_float = _expect_equal_t string_of_float
let expect_equal_str   = _expect_equal_t (fun g -> g)


let add_section sname =
    try
        StringMap.find sname (!_global_sections)
    with
        Not_found ->
            _insertion_order := sname::(!_insertion_order);
            (StringMap.empty, ref [])
;;

(* USAGE *)
(*
 *   (add_test "LET" "Base Case" (fun () ->
 *      let r = eval_string "let a = 2; b = 3; in a + b;" in
 *      let v = (get_int r) in
 *          if v = 5 then success () else failure ()))
 *
 *  sname: Section Name
 *  tname: Test Name
 *  tfun : test function (unit -> int)
 *)
let add_test sname tname tfun =

    (* Does Section Exist ? *)
    let (tmap, lst) = add_section sname in

    try let _ = StringMap.find tname tmap in
        ut_string2 "TEST ALREADY EXISTS"
    with
        Not_found ->

    lst := tname::(!lst);

    (* add test *)
    let ntmap = StringMap.add tname tfun tmap in
        _global_sections := StringMap.add sname (ntmap, lst) (!_global_sections);

    _number_test := (!_number_test + 1)
;;

(*  sk  : Section Key
 *  tmap: test_name -> tmap
 *  tk  : Test Key                  *)
let for_all_tests sk tmap tk =
    let tv = StringMap.find tk tmap in
    flush stdout;
    try
        let r = tv () in
            if r = 0 then(
                ut_string2 (green ^ "[     OK] " ^ sk ^ " - " ^ tk ^ "\n" ^ reset))
            else(
                ut_string2 (red ^ "[   FAIL] " ^ sk ^ " - " ^ tk ^ "\n" ^ reset);
                _ret_code := failure ())
    with e ->
        _ret_code := failure ();
        unexpected_throw sk tk e
;;

let for_all_sections sk =
    let tmap, tst = StringMap.find sk (!_global_sections) in
        ut_string2 ("[RUN    ] " ^ sk ^ " \n");
        tst := List.rev (!tst);
        List.iter (for_all_tests sk tmap) (!tst)
;;

(* Run all *)
let run_all () =
    parse_args ();

    _insertion_order := List.rev (!_insertion_order);

    (* iter over all sections *)
    List.iter for_all_sections (!_insertion_order);

    (* return success or failure *)
    exit !_ret_code
;;
