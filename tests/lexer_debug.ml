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
 *          print out read Sexp (Syntactic expression)
 *              i.e lexer's tokens
 *
 * --------------------------------------------------------------------------- *)

open Util
open Prelexer
open Sexp
open Lexer

let default_stt =
  let stt = Array.create 256 false
  in stt.(Char.code ';') <- true;
     stt.(Char.code ',') <- true;
     stt.(Char.code '(') <- true;
     stt.(Char.code ')') <- true;
     stt


let rec debug_sexp_print sexp =
  let print_loc = Debug.print_loc in
  match sexp with
    | Epsilon 
        -> print_string "Epsilon()\n"  (* "ε" *)
        
    | Block(loc, pts, _) 
        -> print_string "Block: \t{"; 
            print_string "["; print_loc loc; print_string "]\t";
            pretokens_print pts; 
           print_string " }"
            
    | Symbol(loc, name) 
        -> print_string "Symbol: \t"; 
            print_string "["; print_loc loc; print_string "]\t";
            print_string name
            
    | String(loc, str)
        -> print_string "String: \t"; 
            print_string "["; print_loc loc; print_string "]\t";
            print_string "\""; print_string str; print_string "\""
            
    | Integer(loc, n) 
        -> print_string "Integer: \t"; 
            print_string "["; print_loc loc; print_string "]\t";
            print_int n
            
    | Float(loc, x) 
        -> print_string "Float: \t";
            print_string "["; print_loc loc; print_string "]\t";
            print_float x
            
    | Node(f, args) 
        -> print_string "Node: \t"; 
            print_string "(";sexp_print f;
                List.iter (fun sexp -> print_string " "; sexp_print sexp)
                                 args;
            print_string ")"
;;
                       
let debug_sexp_print_all tokens =
  List.iter (fun pt ->
         print_string " ";
         debug_sexp_print pt;
         print_string "\n";
        )
        tokens
;;

let main () = 
    (*
     *  print tokens/sexp of the file given as first arg
     *
     ********************************************************)
    
    let file = Sys.argv.(1) in
    print_string file;
    print_string "\n";
    
    (* Todo read file from prog args *)
    (* get pretokens*)
    let pretoks = prelex_file file in
    
    (* get tokens *)
    let toks = lex default_stt pretoks in
    
    (* print tokens *)
    debug_sexp_print_all toks
;;

main ();;

(* Command Line * )
let command =
  Command.basic
    ~summary:"Print Compiler Debug Info"
    ~readme:(fun () -> "More detailed information")
    Command.Spec.(empty +> anon ("filename" %: string))
    main

let () =
  Command.run ~version:"1.0" ~build_info:"RWO" command * *)

(*(main Sys.argv.(1));;*)
