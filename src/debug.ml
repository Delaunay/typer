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
 *          Provide helper functions to print out extracted
 *                      Pretoken, Sexp, pexp and lexp
 *
 * --------------------------------------------------------------------------- *)

(* removes some warnings *)
open Util
open Fmt

open Prelexer
open Lexer

open Sexp
open Pexp
open Lexp

open Debruijn
open Grammar

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
            print_string ("\"" ^ str ^ "\"")

(* Print a List of Pretokens *)
let rec debug_pretokens_print_all pretokens =
  List.iter (fun pt -> debug_pretokens_print pt; print_string "\n") pretokens

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
            sexp_print f; print_string " [";
                List.iter (fun sexp -> print_string " "; sexp_print sexp)
                                 args;
            print_string "]"

(* Print a list of sexp *)
let debug_sexp_print_all tokens =
  List.iter (fun pt ->
         print_string " ";
         debug_sexp_print pt;
         print_string "\n";)
    tokens


(* Print a Pexp with debug info *)
let debug_pexp_print ptop =
    print_string " ";
    let l = pexp_location ptop in
    let print_info msg loc pex =
        print_string msg; print_string "[";
        print_loc loc;
        print_string "]\t";
        pexp_print pex in
    match ptop with
        | Pimm _                 -> print_info "Pimm       " l ptop
        | Pvar (_,_)             -> print_info "Pvar       " l ptop
        | Phastype (_,_,_)       -> print_info "Phastype   " l ptop
        | Pmetavar (_, _)        -> print_info "Pmetavar   " l ptop
        | Plet (_, _, _)         -> print_info "Plet       " l ptop
        | Parrow (_, _, _, _, _) -> print_info "Parrow     " l ptop
        | Plambda (_,_, _, _)    -> print_info "Plambda    " l ptop
        | Pcall (_, _)           -> print_info "Pcall      " l ptop
        | Pinductive (_, _, _)   -> print_info "Pinductive " l ptop
        | Pcons (_,_)            -> print_info "Pcons      " l ptop
        | Pcase (_, _, _)        -> print_info "Pcase      " l ptop
      (*| _                      -> print_info "Not Impl   " l ptop *)

let debug_pexp_decls decls =
  let print_loc l = print_string "["; print_loc l; print_string "]  " in

    List.iter (fun e ->
      print_string " ";

      let _ = match e with
        | Pexpr ((l, name), pxp) ->
          lalign_print_string (pexp_to_string pxp) 15;
          print_loc l; print_string " = "; pexp_print pxp

        | Ptype ((l, name), ptp) ->
          lalign_print_string (pexp_to_string ptp) 15;
          print_loc l; print_string " : "; pexp_print ptp

        | Pmcall((l, op), args)  ->
          lalign_print_string "Macro Decls" 15;
          print_loc l; sexp_print (Node(Symbol(l, op), args)) in

      print_string "\n")

          decls


(* Print a list of pexp *)
let debug_pexp_print_all pexps =
    List.iter
        (fun px ->
            debug_pexp_print px;
            print_string "\n")
        pexps

let debug_lexp_decls decls =
    let sep = " : " in
    List.iter (fun e ->
            let ((loc, name), lxp, ltp) = e in

            print_string " ";
            lalign_print_string (lexp_to_string lxp) 15;
            print_string "["; print_loc loc; print_string "]";

            let str = _lexp_str_decls (!debug_ppctx) [e] in

            (* First col size = 15 + 1 + 2 + 3 + 5 + 6
             *                = 32                          *)

            let str = match str with
                | fst::tl -> print_string (sep ^ fst); print_string "\n"; tl
                | _ -> [] in

            (* inefficient but makes things pretty iff -fmt-pretty=on *)
            let str = List.flatten (List.map (fun g -> str_split g '\n') str) in

            let str = match str with
                | scd::tl ->
                    print_string " FILE: ";
                    lalign_print_string loc.file 25;
                    print_string (sep ^ scd); print_string "\n"; tl
                | _ -> [] in

            List.iter (fun g ->
                print_string ((make_line ' ' 32) ^ sep);
                print_string g; print_string "\n")
                str;

        ) decls
