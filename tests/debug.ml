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
 *                  extracted token
 *                  extracted expression
 *
 * --------------------------------------------------------------------------- *)

(* removes some warnings *) 
open Util
 
(* print debug info *)
let print_loc (loc : Util.location) = 
    print_string loc.file; 
    print_string ": ln "; 
    Fmt.ralign_print_int loc.line 3;
    print_string ", cl ";
    Fmt.ralign_print_int loc.column 3;
;;


(*open Token 
open Token

(* Print token with debug info *)
let print_token tok = 
    (* Shortcut *)
    let lalign str = Fmt.lalign_print_string str 20 in
    
    (* When we need to print only the name *)
    let quick_print name loc = 
        lalign name;
        print_string "["; print_loc loc; print_string "]  ";
        print_string "\n" in
        
    let long_print name loc elem =
        lalign name;
        print_string "["; print_loc loc; print_string "]  ";
        print_string "'";
        print_string elem;
        print_string "'\n" in
        
    let print_kwd name loc ch = 
        lalign name;
        print_string "["; print_loc loc; print_string "]  ";
        print_char ch;
        print_string "\n" in
        
    let print_float name loc ch = 
        lalign name;
        print_string "["; print_loc loc; print_string "]  ";
        print_float ch;
        print_string "\n" in
        
    let print_integer name loc ch =
        lalign name;
        print_string "["; print_loc loc; print_string "]  ";
        print_int ch;
        print_string "\n" in
        
    (* Print tokens *)
    match tok with
        | Token.Arw(loc, str)     -> long_print "Arw"    loc str;
        | Token.Assign(loc, str)  -> long_print "Assign" loc str;
        | Token.Colon(loc, str)   -> long_print "Colon"  loc str;
        | Token.Lambda(loc)       -> quick_print "Lambda"    loc;
        | Token.Case(loc)         -> quick_print "Case"      loc;
        | Token.Inductive(loc)    -> quick_print "Inductive" loc;
        | Token.Let(loc)          -> quick_print "Let" loc;
        | Token.In(loc)           -> quick_print "In"  loc;
        | Token.Ident(loc, str)   -> long_print "Identifier" loc str;
        | Token.Kwd(loc, ch)      -> print_kwd "Kwd" loc ch;
        | Token.Float(loc, value) -> print_float "Float" loc value;
        | Token.Integer(loc, value) -> print_integer "Integer" loc value;
        | Token.String(loc, str)  -> long_print "String" loc str;
;;
 
(*  Lexer print
 *--------------------------------------------------*)

(* Print the list of token *)
let debug_lex file_name  =

  let file_stream = open_in file_name in

    (* Create a stream of tokens *)
    let lex_stream = Lexer.lex file_name (Stream.of_channel file_stream) in
    
        (* Print each tokens *)
        Stream.iter (fun tok -> print_token tok) lex_stream;
;;

(*  Parser print
 *--------------------------------------------------(**)
let debug_parser file_name = 

  let file_stream = open_in file_name in

    (* Create a stream of tokens *)
    let lex_stream = Lexer.lex file_name (Stream.of_channel file_stream) in
    
    (* Parse token's stream *)
    Toplevel.main_loop lex_stream
;; **)


let main () = 
    debug_lex "./typer_test/lexer_test.typer"; (**)
    
    (*debug_parser "kiwi_code/lexer_test.kwi";**)
;;

main ();*)
