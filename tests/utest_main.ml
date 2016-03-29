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
open Fmt

let cut_name str =
    String.sub str 0 (String.length str - 12)
;;

let _global_verbose_lvl = ref 1
let _global_sample_dir = ref "./"
let _global_tests_dir = ref "./_build/tests/"

let arg_defs = [
    ("--verbose=",
        Arg.Int (fun g -> _global_verbose_lvl := g), " Set verbose level");
    ("--samples=",
        Arg.String (fun g -> _global_sample_dir := g), " Set sample directory");
    ("--tests=",
        Arg.String (fun g -> _global_tests_dir := g), " Set tests directory");
];;

let parse_args () = Arg.parse arg_defs (fun s -> ()) ""

let ut_string vb msg = if vb <= (!_global_verbose_lvl) then print_string msg else ()


let print_file_name i n name pass =
    let line_size = 80 - (String.length name) - 16 in
    print_string "    (";
    ralign_print_int i 2; print_string "/";
    ralign_print_int n 2; print_string ") ";
    print_string name;
    print_string (make_line '.' line_size);
    if pass then print_string "..OK\n" else print_string "FAIL\n"
;;

let verbose n = (n <= (!_global_verbose_lvl))


(* search *_test.byte executable en run them
    Usage:
        ./utest_main tests_folder root_folder *)
let main () =
    parse_args ();

    print_string  "         \n";
    print_string  "              Running Unit Tests \n";
    print_string  "         \n";
    (*print_string ("[       ] Test folder: " ^ folder ^ "\n"); *)

    (* get tests files *)
    let folder = !_global_tests_dir in
    let root_folder = !_global_sample_dir in

    let files = try Sys.readdir folder
        with e ->(
            print_string ("The folder: " ^ (! _global_tests_dir) ^ " does not exist.\n" ^
            "Have you tried \"./utests --tests= ./tests\" ?\n");
            raise e;
        ) in

    let check name =
        if (Filename.check_suffix name "_test.byte") ||
           (Filename.check_suffix name "_test.native") then true else false in

    (* select files that are executable tests *)
    let files = Array.fold_left
        (fun acc elem -> if check elem then elem::acc else acc)
         [] files in

    let files_n = List.length files in

    (if files_n = 0 then (
        print_string "No tests were found. Did you compiled them? \n"));

    let exit_code = ref 0 in
    let failed_test = ref 0 in
    let tests_n = ref 0 in
    let test_args = " --samples= " ^ root_folder ^
                    " --verbose= " ^ (string_of_int !_global_verbose_lvl) in

    List.iter (fun file ->
        flush stdout;

        tests_n := !tests_n + 1;
        exit_code := Sys.command (folder ^ file ^ test_args);

        (if !exit_code != 0 then(
            (if verbose 1 then print_file_name (!tests_n) files_n file false);
            failed_test := !failed_test + 1)
        else
            (if verbose 1 then print_file_name (!tests_n) files_n file true);
        );

        (if verbose 2 then print_newline ());

    ) files;

    print_string   "\n\n";
    print_string   "    Test Ran    : "; print_int !tests_n;
    print_string "\n    Test Failed : "; print_int !failed_test;
    print_string "\n    Test Passed : "; print_int (!tests_n - !failed_test);
    print_endline "\n";
;;

main ();
