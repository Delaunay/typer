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
open Pexp

(* Print aPretokens *)
let rec debug_pretokens_print pretoken =
    print_string " ";
    let print_info msg loc =
        print_string msg; 
        print_string "["; print_loc loc; print_string "]\t" in
        
    match pretoken with
        | Preblock(loc, pts,_)
         -> print_info "Preblock:  " loc;
            print_string "{";   pretokens_print pts;    print_string " }"
            
        | Pretoken(loc, str) 
         -> print_info "Pretoken:  " loc;
                print_string ("'" ^ str ^ "'"); 
            
        | Prestring(loc, str)
         -> print_info "Prestring: " loc;
            print_string ("\"" ^ str ^ "\"");
;;

(* Print a List of Pretokens *)
let rec debug_pretokens_print_all pretokens =
  List.iter (fun pt -> debug_pretokens_print pt; print_string "\n") pretokens
;;
  
(* Sexp Print *)
let rec debug_sexp_print sexp =
  let print_info msg loc =
    print_string msg; 
    print_string "["; print_loc loc; print_string "]\t" in
  match sexp with
    | Epsilon 
        -> print_string "Epsilon  "  (* "ε" *)
        
    | Block(loc, pts, _) 
        -> print_info "Block:   " loc; 
           print_string "{"; pretokens_print pts; print_string " }"
            
    | Symbol(loc, name) 
        -> print_info "Symbol:  " loc; print_string name
            
    | String(loc, str)
        -> print_info "String:  " loc;
           print_string "\""; print_string str; print_string "\""
            
    | Integer(loc, n) 
        -> print_info "Integer: " loc;   print_int n
            
    | Float(loc, x) 
        -> print_info "Float:   " loc;   print_float x
            
    | Node(f, args) 
        -> print_info "Node:    " (sexp_location f);
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
         print_string "\n";)
    tokens
;;


(* Print a Pexp with debug info *)
let debug_pexp_print pexp =
    print_string " ";
    let l = pexp_location pexp in
    let print_info msg loc pex = 
        print_string msg; print_string "["; 
        print_loc loc; 
        print_string "]\t";
        pexp_print pexp in
    match pexp with
        | Pimm _                 -> print_info "Pimm       " l pexp
        | Pvar (_,_)             -> print_info "Pvar       " l pexp
        | Phastype (_,_,_)       -> print_info "Phastype   " l pexp
        | Pmetavar (_, _)        -> print_info "Pmetavar   " l pexp
        | Plet (_, _, _)         -> print_info "Plet       " l pexp
        | Parrow (_, _, _, _, _) -> print_info "Parrow     " l pexp
        | Plambda (_,_, _, _)    -> print_info "Plambda    " l pexp
        | Pcall (_, _)           -> print_info "Pcall      " l pexp
        | Pinductive (_, _, _)   -> print_info "Pinductive " l pexp
        | Pcons (_,_)            -> print_info "Pcons      " l pexp
        | Pcase (_, _, _)        -> print_info "Pcase      " l pexp
        | _                      -> print_info "Not Impl   " l pexp
;;

(* Print a list of pexp *)
let debug_pexp_print_all pexps =
    List.iter 
        (fun px -> 
            debug_pexp_print px; 
            print_string "\n") 
        pexps
;;

(* Print lexp with debug info *)

(* Print a list of lexp *)


