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
let rec make_line c n = String.make n c;;

(*  Big numbers are replaced by #### *)
let cut_int (v:int) (start:int) (len:int): int = 0;;
     
(*  LALIGN 
 * ----------------------- *)
let ralign_generic get_size print_str print_elem cut_elem elem col =
    let n = get_size elem in
    if n > col then 
        print_elem (cut_elem elem 0 col)
    else begin
        print_str (make_line ' ' (col - n));
        print_elem elem; end
;;

let ralign_print_string = 
    ralign_generic String.length print_string print_string String.sub;;

let ralign_print_int =
    ralign_generic str_size_int print_string print_int cut_int;;
    

(*  LALIGN 
 * ----------------------- *)
let lalign_generic get_size print_str print_elem cut_elem elem col =
    let n = get_size elem in
    if n > col then 
        print_elem (cut_elem elem 0 col)
    else begin
        print_elem elem; 
        print_str (make_line ' ' (col - n)); end
;;  
    
let lalign_print_string = 
    lalign_generic String.length print_string print_string String.sub;;

let lalign_print_int =
    lalign_generic str_size_int print_string print_int cut_int;;

(* Table Printing helper *)
let make_title title = 
    let title_n = String.length title in
    let p = title_n mod 2 in
    let sep_n = (80 - title_n - 4) / 2 in
    let lsep = (make_line '=' sep_n) in
    let rsep = (make_line '=' (sep_n + p)) in
        ("    " ^ lsep ^ title ^ rsep ^ "\n")
;;

let make_rheader (head: (((char* int) option  * string) list)) =
    print_string "    | ";
    
    List.iter (fun (o, name) ->
        let _ = match o with
            | Some ('r', size) -> ralign_print_string name size
            | Some ('r', size) -> lalign_print_string name size
            | _ -> print_string name in
        print_string " | ")
        head;
    
    print_string "\n"
;;
    
let make_sep c = "    " ^ (make_line c 76) ^ "\n";;


    
    
