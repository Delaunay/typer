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
 *          Declare new print function which align printed values.
 *
 * ---------------------------------------------------------------------------*)
 
(*  Compute the number of character needed to print an integer*)
let str_size_int value =
    (int_of_float (log10 (float value))) + 1
;;

(* print n char 'c' *)
let rec make_line c n = 
    print_string c;
    if n >= 1 then (make_line c (n - 1));
;;
     
(* print an integer right-aligned *)
let ralign_print_int value nb =
    make_line " " (nb - (str_size_int value));
    print_int value;
;;

let lalign_print_int value nb =
    print_int value;
    make_line " " (nb - (str_size_int value));
;;

let ralign_print_string str nb =
    make_line " " (nb - String.length str);
    print_string str;
;;

let lalign_print_string str nb =
    print_string str;
    make_line " " (nb - String.length str);
;;

(* print n char 'c' *)
let rec prerr_make_line c n = 
    prerr_string c;
    if n >= 1 then (make_line c (n - 1));
;;
     
(* print an integer right-aligned *)
let ralign_prerr_int value nb =
    prerr_make_line " " (nb - (str_size_int value));
    prerr_int value;
;;

let lalign_prerr_int value nb =
    prerr_int value;
    prerr_make_line " " (nb - (str_size_int value));
;;

let ralign_prerr_string str nb =
    prerr_make_line " " (nb - String.length str);
    prerr_string str;
;;

let lalign_prerr_string str nb =
    prerr_string str;
    prerr_make_line " " (nb - String.length str);
;;
