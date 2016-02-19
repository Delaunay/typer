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
 *          print out each steps of the compilation
 *
 * --------------------------------------------------------------------------- *)

open Debug
open Prelexer
open Lexer
open Sexp
open Grammar
open Pexp


let main () = 

    let arg_n = Array.length Sys.argv in
    let usage = 
        "  Usage: \n    " ^ Sys.argv.(0) ^ " <file_name> [options] \n\n" in
    
    (*  Print Usage *)
    if arg_n == 1 then
        begin
        print_string usage;
        print_string "  Options:\n";
        end
    else
    begin
        let filename = Sys.argv.(1) in
        
        (* Read additional Args if any *)
        
        (* Print Pretokens *)
        print_string "\n\t====\n";
        print_string "\t  PreTokens\n";
        print_string "\t=======================\n";
        
        (* get pretokens*)
        let pretoks = prelex_file filename in
        
        debug_pretokens_print_all pretoks;
        
        (* Print Sexp *)
        print_string "\n\t====\n";
        print_string "\t  Base Sexp\n";
        print_string "\t=======================\n";
        
        (* get sexp/tokens *)
        let toks = lex default_stt pretoks in
        
        debug_sexp_print_all toks;
        
        (* Print Node Sexp *)
        print_string "\n\t====\n";
        print_string "\t  Node Sexp\n";
        print_string "\t=======================\n";
        
        (* get node sexp  *)
        let nodes = sexp_parse_all_to_list default_grammar toks (Some ";") in
        
        debug_sexp_print_all nodes;
        
        (* Print pexp *)
        print_string "\n\t====\n";
        print_string "\t  Pexp\n";
        print_string "\t=======================\n";
        
        let pexps = pexp_parse_all nodes in
        
        debug_pexp_print_all pexps;
        
        (* Print Lexp *)
        print_string "\n\t====\n";
        print_string "\t  Lexp\n";
        print_string "\t=======================\n";
        
        (** )
        let lexps = lexp_parse_all pexps in
        
        debug_lexp_print_all lexps; ( **)

    end
;;

main ()
;;

