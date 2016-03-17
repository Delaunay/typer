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
 *          Basic utest program run all tests
 *
 * --------------------------------------------------------------------------- *)
 
 
let cut_name str =
    String.sub str 0 (String.length str - 12)
;;
 
(* search *_test.byte executable en run them 
    Usage:
        ./utest_main tests_folder root_folder *)
let main () = 
    let arg_n = Array.length Sys.argv in
    
    (* read where tests files are*)
    let folder = (if arg_n > 1 then Sys.argv.(1) else "./_build/tests/") in

    print_string  "         \n";
    print_string  "              Running Unit Tests \n";
    print_string  "         \n";
    (*print_string ("[       ] Test folder: " ^ folder ^ "\n"); *)

    (* get tests files *)
    let files = Sys.readdir folder in
    let files_n = Array.length files in
    
    let exit_code = ref 0 in
    let failed_test = ref 0 in
    let tests_n = ref 0 in
    let root_folder = (if arg_n > 2 then Sys.argv.(2) else "./") in (* /_build/tests/ *)
    
    for i = 0 to files_n - 1 do
        flush stdout;
        (* Check if file is a test => if it is run it *)
        (if (Filename.check_suffix files.(i) "_test.byte") ||
            (Filename.check_suffix files.(i) "_test.native") then 
        begin
            
            tests_n := !tests_n + 1;

            exit_code := Sys.command (folder ^ files.(i) ^ " " ^ root_folder);
            
        end)
    done;
    
    print_string   "\n\n\n";
    print_endline  "  =========== Test Summary ===========\n";
    print_string   "    Test Ran    : "; print_int !tests_n;
    print_string "\n    Test Failed : "; print_int !failed_test;
    print_string "\n    Test Passed : "; print_int (!tests_n - !failed_test);
    print_endline "\n  =========== Test Summary ===========\n";
;;

main ();
