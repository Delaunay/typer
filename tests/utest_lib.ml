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
 


module StringMap = 
    Map.Make (struct type t = string let compare = String.compare end)
;;
 
 
type test_fun = (unit -> int)
type tests = (test_fun) StringMap.t
type sections = (tests) StringMap.t

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


(* USAGE *)
(*  
 *   (add_test "LET" "Base Case" (fun () ->
 *      let r = eval_string "let a = 2; b = 3; in a + b;" in
 *      let v = (get_int r) in
 *          if v = 5 then success () else failure ()))
 *)
let add_test sname tname tfun = 
        
    (* Does Section Exists ? *)
    let tmap = 
        try 
            StringMap.find sname (!_global_sections)
        with
            Not_found -> StringMap.empty in
    
    (* add test *)
    let ntmap = StringMap.add tname tfun tmap in
        _global_sections := StringMap.add sname ntmap (!_global_sections);
;;
    
(* Run all *)
let run_all () =
    (* iter over all sections *)
    StringMap.iter (fun sk sv ->
        print_string ("[RUN    ] " ^ sk ^ " \n");
        (* iter over all tests in the current sections *)
        StringMap.iter (fun tk tv ->
            (* RUN TEST*)
            let r = tv () in
                if r = 0 then
                    (print_string ("[     OK] " ^ sk ^ " - " ^ tk ^ "\n"))
                else
                    (print_string ("[   FAIL] " ^ sk ^ " - " ^ tk ^ "\n"))
            )
            sv
        )
        (!_global_sections)

 
let expect_equal_int value expectation =
    if value = expectation then
        success ()
    else(
        print_string ("[       ]     EXPECTED " ^ (string_of_int expectation) ^ "\n");
        print_string ("[       ]          GOT " ^ (string_of_int value) ^ "\n");
        failure ())
;;



