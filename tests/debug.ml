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
 *          Provide helper functions to print out 
 *                  extracted Pretoken
 *                  extracted Sexp 
 *
 * --------------------------------------------------------------------------- *)

(* removes some warnings *) 
open Util
open Prelexer
open Lexer
open Sexp
 
(* print debug info *)
let print_loc (loc : Util.location) = 
    (*print_string loc.file; *) (* Printing the file is too much*)
    print_string "ln "; 
    Fmt.ralign_print_int loc.line 3;
    print_string ", cl ";
    Fmt.ralign_print_int loc.column 3;
;;


(* Print aPretokens *)
let rec debug_pretokens_print pretoken =
    print_string " ";
    match pretoken with
        | Preblock(loc, pts,_)
         -> print_string "Preblock:\t"; 
            print_string "["; print_loc loc; print_string "]\t";
            print_string "{"; 
                pretokens_print pts; 
            print_string " }"
            
        | Pretoken(loc, str) 
         -> print_string "Pretoken:\t"; 
            print_string "["; print_loc loc; print_string "]\t"; 
                print_string str; 
            print_string "\n"
            
        | Prestring(loc, str)
         -> print_string "Prestring:\t"; 
            print_string "["; print_loc loc; print_string "]\t";
            print_string "\""; 
                print_string str; 
            print_string "\"\n";
;;

(* Print a List of Pretokens *)
let rec debug_pretokens_print_all pretokens =
  List.iter (fun pt -> debug_pretokens_print pt) pretokens
;;
  
(* Sexp Print *)
let rec debug_sexp_print sexp =
  let print_loc = print_loc in
  match sexp with
    | Epsilon 
        -> print_string "Epsilon "  (* "ε" *)
        
    | Block(loc, pts, _) 
        -> print_string "Block:  "; 
            print_string "["; print_loc loc; print_string "]\t{ ";
            pretokens_print pts; 
           print_string " }"
            
    | Symbol(loc, name) 
        -> print_string "Symbol: "; 
            print_string "["; print_loc loc; print_string "]\t";
            print_string name
            
    | String(loc, str)
        -> print_string "String: "; 
            print_string "["; print_loc loc; print_string "]\t";
            print_string "\""; print_string str; print_string "\""
            
    | Integer(loc, n) 
        -> print_string "Integer:"; 
            print_string "["; print_loc loc; print_string "]\t";
            print_int n
            
    | Float(loc, x) 
        -> print_string "Float:  ";
            print_string "["; print_loc loc; print_string "]\t";
            print_float x
            
    | Node(f, args) 
        -> print_string "Node:   ";
            print_string "["; print_loc (sexp_location f); print_string "]\t";
            sexp_print f; print_string " \t "; 
                List.iter (fun sexp -> sexp_print sexp; print_string " @ ")
                                 args;
            print_string " "
;;
  
(* Print a list of sexp *)  
let debug_sexp_print_all tokens =
  List.iter (fun pt ->
         print_string " ";
         debug_sexp_print pt;
         print_string "\n";
        )
        tokens
;;

