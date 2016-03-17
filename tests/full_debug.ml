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
 *          print out each compilation' steps
 *
 * --------------------------------------------------------------------------- *)

open Debug
open Prelexer
open Lexer
open Sexp
open Grammar
open Pexp
open Util
open Fmt

let dloc = dummy_location;;

open Debruijn
open Myers
open Lparse
open Eval
open Lexp


let dummy_decl = Imm(String(dloc, "Dummy"));;

(*
let pexp_lexp_all nodes ctx =

    let rec loop nodes ctx acc = 
        match nodes with
            | [] -> ((List.rev acc), ctx)
            | hd::tl  -> 
                let lxp, new_ctx = pexp_lexp_one hd ctx in
                    (loop tl new_ctx (lxp::acc)) in
    (loop nodes ctx [])
;;



let add_rte_def name ctx = 
    (add_rte_variable (Some name) dummy_decl ctx);;
    

let eval_until_nth xpr n rctx =

    let rec loop xpr nb rctx =
        match xpr, nb with
            | [], _ -> rctx
            | _, nb when nb = n -> rctx
            | hd::tl, _ -> 
                let c, rctx = eval_toplevel hd rctx in
                    print_eval_result nb c;
                    loop tl (nb + 1) rctx in  
        loop xpr 0 rctx
;; *)
        
let discard v = ();;
        
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

        print_string (make_title " ERRORS ");
        (* get pretokens*)
        let pretoks = prelex_file filename in
        
        (* get sexp/tokens *)
        let toks = lex default_stt pretoks in
        
        (* get node sexp  *)
        let nodes = sexp_parse_all_to_list default_grammar toks (Some ";") in
        
        (* Parse All Declaration *)
        let pexps = pexp_decls_all nodes in
        (* let pexps = pexp_parse_all nodes in *)

        (* get lexp *)
        let ctx = make_lexp_context in
        (*  Those are hardcoded operation *)
            let ctx = add_def "_+_" ctx in
            let ctx = add_def "_*_" ctx in
  
        (* let lexps, new_ctx = lexp_parse_all pexps ctx in *)
        let lexps, nctx = lexp_decls pexps ctx in
            
        print_string "\n\n";
        (* Printing *)(*
        print_title "PreTokens";    debug_pretokens_print_all pretoks;
        print_title "Base Sexp";    debug_sexp_print_all toks;  *)
        print_string (make_title " Node Sexp "); debug_sexp_print_all nodes;
        print_string "\n";
        print_string (make_title " Pexp ");      debug_pexp_decls pexps;
        (*debug_pexp_print_all pexps;*)
        print_string "\n";
        print_string (make_title " Lexp ");      debug_lexp_decls lexps;       
        (* debug_lexp_print_all lexps; *)
        print_string "\n";

        print_string "\n";
        lexp_context_print nctx;
        print_string "\n";
        
        (* Eval Each Expression *)
        print_string (make_title " Eval Print ");
        
        
        (* Eval declaration *)
        let rctx = make_runtime_ctx in 
        let rctx = eval_decls lexps rctx in
          
        let _ = 
        try
            (* Check if main is present *)
            let main = (senv_lookup "main" nctx) in
            (* Push main args here if any *)
            
            (* get main body *)
            let body = (get_rte_variable main rctx) in
            (* eval main *)
            let r = (eval body rctx) in
                print_eval_result 0 r
                
        with 
            Not_found ->  print_string "No declared main\n" in
            
        (*  Print info *)
        print_string "\n\n";
        print_rte_ctx rctx; 
            
            
        print_call_trace ();
    end
;;

main ()
;;
