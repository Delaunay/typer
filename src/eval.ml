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
 *          Simple interpreter
 *
 * --------------------------------------------------------------------------- *)
 
open Util
open Lexp 
open Lparse
open Myers
open Sexp
open Fmt



let print_myers_list l print_fun = 
    let n = (length l) in
    
    print_string "-------------------\n";
    print_string " Environement: \n";
    print_string "-------------------\n";
    
    for i = 0 to n - 1 do
        ralign_print_int (i + 1) 4;
        print_string ")    ";
        print_fun (nth i l);
    done;
    print_string "-------------------\n";
;;

let get_function_name fname =
    match fname with
        | Var(v) -> let ((loc, name), idx) = v in name
        | _ -> "Name Lookup failure"
;;

let get_int lxp =
    match lxp with
        | Imm(Integer(_, l)) -> l
        | _ -> lexp_print lxp; -1
;;

(*  Runtime Environ *)
type runtime_env = lexp myers
let make_runtime_ctx = nil;;
let add_rte_variable x l = (cons x l);;
let get_rte_variable idx l = (nth (idx) l);;

let print_rte_ctx l = print_myers_list l 
    (fun g -> lexp_print g; print_string "\n")
;;

(*  Evaluation reduce an expression x to an Lexp.Imm *)
let rec eval lxp ctx: (lexp * runtime_env) = 
        
    match lxp with
        (*  This is already a leaf *)
        | Imm(v) -> lxp, ctx
        
        (*  Return a value stored in the environ *)
        | Var((loc, name), idx) -> begin
            try
                (get_rte_variable idx ctx), ctx
            with 
                Not_found ->
                    print_string ("Variable: " ^ name ^ " was not found | "); 
                    print_int idx; print_string "\n";
                    raise Not_found end
                
        (*  this works for non recursive let *)
        | Let(_, decls, inst) -> begin
            (*  First we evaluate all declaration then we evaluate the instruction *)
            let nctx = build_ctx decls ctx in
            let value, nctx = eval inst nctx in
            (*  return old context as we exit let's scope*)
                value, ctx end
                
        (*  Function call *)
        | Call (fname, args) ->
            (*  Add args in the scope *)
            let nctx = build_arg_list args ctx in
            
            (* We need to seek out the function declaration and eval the body *)
            (* but currently we cannot declare functions so I hardcoded + *)
   (*       let bdy = get_body fname in
                eval bdy nctx                *)
            
            (*  fname is currently a var *)
            let name = get_function_name fname in
                (*  Hardcoded function for now *)
                if name = "_+_" then begin

                    (*  Get the two args *)
                    let l = get_int (get_rte_variable 0 nctx) in
                    let r = get_int (get_rte_variable 1 nctx) in
                    
                    Imm(Integer(dummy_location, l + r)), ctx end
                else
                    Imm(String(dummy_location, "Funct Not Implemented")), ctx 
                   
        | _ -> Imm(String(dummy_location, "Eval Not Implemented")), ctx
        
and build_arg_list args ctx =

    (*  Eval every args *)
    let arg_val = List.map (fun (k, e) -> let (v, c) = eval e ctx in v) args in
    
    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable v c) ctx arg_val

and build_ctx decls ctx =
    match decls with
        | [] -> ctx
        | hd::tl -> 
            let (v, exp, tp) = hd in
            let (value, nctx) = eval exp ctx in
            let nctx = add_rte_variable value nctx in  
                build_ctx tl nctx
;;

let print_eval_result lxp =
    print_string " >> ";
    match lxp with
        | Imm(v) -> sexp_print v; print_string "\n"
        | _ ->  print_string "Evaluation Failed\n"
;;

let evalprint lxp ctx = 
    let v, ctx = (eval lxp ctx) in
    print_eval_result v;
    ctx
;;

