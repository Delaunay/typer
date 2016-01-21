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
 *          print out read pexp (primary expression)
 *
 * --------------------------------------------------------------------------- *)

 
let rec debug_pexp_print pexp =
    match pexp with
        | Pimm(exp) 
            ->
        | Pvar(p)
            ->
        | Phastype(l, exp2, exp1)
            ->
;;

let debug_pexp_print_all pexp =
  List.iter (fun pt ->
         print_string " ";
         debug_pexp_print pt;
         print_string "\n";
        )
        pexp
;;

(* Language config *)

let default_stt =
  let stt = Array.create 256 false
  in stt.(Char.code ';') <- true;
     stt.(Char.code ',') <- true;
     stt.(Char.code '(') <- true;
     stt.(Char.code ')') <- true;
     stt
;;

let default_grammar : grammar
  = List.fold_left (fun g (n, ll, rl) -> SMap.add n (ll, rl) g)
                   SMap.empty
                   [("^", Some 171, Some 159);
                    ("/", Some 148, Some 160);
                    ("-", Some 92, Some 110);
                    ("+", Some 93, Some 111);
                    ("!=", Some 94, Some 75);
                    (">=", Some 95, Some 76);
                    ("<=", Some 96, Some 77);
                    (">", Some 97, Some 78);
                    ("<", Some 98, Some 79);
                    ("&&", Some 64, Some 81);
                    ("||", Some 39, Some 51);
                    (",", Some 26, Some 26);
                    ("then", Some 1, Some 0);
                    ("=", Some 99, Some 80);
                    ("type", None, Some 27);
                    (";", Some 15, Some 15);
                    ("*", Some 137, Some 137);
                    (":", Some 173, Some 115);
                    ("]", Some 3, None);
                    ("->", Some 126, Some 114);
                    ("=>", Some 126, Some 113);
                    ("≡>", Some 126, Some 112);
                    ("in", Some 2, Some 53);
                    ("else", Some 0, Some 52);
                    ("|", Some 40, Some 40);
                    (")", Some 4, None);
                    ("[", None, Some 3);
                    ("case", None, Some 28);
                    ("lambda", None, Some 126);
                    ("letrec", None, Some 2);
                    ("let", None, Some 2);
                    ("if", None, Some 1);
                    ("(", None, Some 4);
                   ]
;;

let main filename () = 
    
    (* Todo read file from prog args *)
    (* get pretokens*)
    let pretoks = prelex_file filename in
    
    (* get sexp/tokens *)
    let toks = lex default_stt pretoks in
    
    (* get pexp *)
    let pxp = sexp_parse_all grm toks limit in
    
    (* print pxp *)
    debug_pexp_print_all pxp
;;

(* Command Line *)
open Core.Std

let command =
  Command.basic
    ~summary:"Print Compiler Debug Info"
    ~readme:(fun () -> "More detailed information")
    Command.Spec.(empty +> anon ("filename" %: string))
    main

let () =
  Command.run ~version:"1.0" ~build_info:"RWO" command
  


