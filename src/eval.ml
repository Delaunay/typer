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
open Grammar

let _eval_error loc msg = 
    msg_error "_eval" loc msg;
    raise (internal_error msg)
;;

let dloc = dummy_location
let _eval_warning = msg_warning "_eval"


let print_myers_list l print_fun = 
    let n = (length l) in
    let sep = "    " ^ (make_line '-' 76) ^ "\n" in
    
    print_string (sep ^ (make_line ' ' 30) ^ "Environement\n" ^ sep);  
    for i = 0 to n - 1 do
    print_string "    |";
        ralign_print_int i 4;
        print_string " | ";
        print_fun (nth i l);
    done;
    print_string sep;
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
type runtime_env = (string option * lexp) myers
let make_runtime_ctx = nil;;
let add_rte_variable name x l = (cons (name, x) l);;

let get_rte_variable idx l = let (_, x) = (nth (idx) l) in x;;

let print_rte_ctx l = print_myers_list l 
    (fun (n, g) -> 
        let _ = 
        match n with
            | Some m -> lalign_print_string m 10; print_string "  |  "
            | None -> print_string (make_line ' ' 10); print_string "  |  " in
        lexp_print g; print_string "\n")
;;

(*  _evaluation reduce an expression x to an Lexp.Imm *)
let rec _eval lxp ctx: (lexp * runtime_env) = 
        
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
            (*  First we _evaluate all declaration then we eval the instruction *)
            
            let nctx = build_ctx decls ctx in
            
            (*
            print_rte_ctx ctx;
            print_rte_ctx nctx; *)
            
            let value, nctx = _eval inst nctx in
            (*  return old context as we exit let's scope*)
                value, ctx end
                
        (*  Function call *)
        | Call (lname, args) -> (
            (*  Try to extract name *)
            match lname with
                (*  Function declaration *)
                | Var((loc, name), _) when name = "_=_" ->
                    (*  Save declaration in environment *)
                    let (vr, body) = match args with 
                        | [(_, a); (_, b)] -> a, b
                        | _ ->  _eval_error loc "Wrong number of Args" in
                    
                    let vname = get_function_name vr in
                    let nctx = add_rte_variable (Some vname) body ctx in
                        body, nctx
                
                (*  Hardcoded functions *)
                | Var((_, name), _) when name = "_+_" ->
                    let nctx = build_arg_list args ctx in
                    let l = get_int (get_rte_variable 0 nctx) in
                    let r = get_int (get_rte_variable 1 nctx) in
                    Imm(Integer(dloc, l + r)), ctx 
                    
                | Var((_, name), _) when name = "_*_" ->
                    let nctx = build_arg_list args ctx in
                    let l = get_int (get_rte_variable 0 nctx) in
                    let r = get_int (get_rte_variable 1 nctx) in
                    Imm(Integer(dloc, l * r)), ctx 
                
                (* This is a named function call *)
                (*  TODO: handle partial application *)
                | Var((_, _), idx) when idx >= 0 ->
                    (*  get function body *)
                    let body = get_rte_variable idx ctx in
                    (*  Add args in the scope *)
                    let nctx = build_arg_list args ctx in
                    let e, nctx = (_eval body nctx) in
                    (*  we exit function and send back old ctx *)
                        e, ctx
    
                (* TODO Everything else *)
                (*  Which includes a call to a lambda *)
                | _ -> Imm(String(dloc, "Funct Not Implemented")), ctx)
                        
        | Lambda(_, vr, _, body) -> begin 
            let (loc, name) = vr in
            let value = (get_rte_variable 0 ctx) in
            let nctx = add_rte_variable (Some name) value ctx in
            
            let rec build_body bd idx nctx = 
                match bd with
                    | Lambda(_, vr, _, body) ->
                        let (loc, name) = vr in
                        (*  Get Variable from call context *)
                        let value = (get_rte_variable idx ctx) in
                        (*  Build lambda context *)
                        let nctx = add_rte_variable (Some name) value nctx in
                            (build_body body (idx + 1) nctx)
                    | _ -> bd, nctx in
                    
            let body, nctx = build_body body 1 nctx in
                    
            let e, nctx = _eval body nctx in
                e, ctx end
       
        (*  Inductive is a type declaration. We have nothing to eval *)
        | Inductive (_, _, _, _) as e -> e, ctx
        
        (*  inductive-cons build a type too? *)
        | Cons (_, _) as e -> e, ctx
        
        (* Case *) 
        | Case (loc, target, _, pat, dflt) -> begin
            
            (* Eval target *)
            let v, nctx = _eval target ctx in
            
            (*  V must be a constructor Call *)
            let ctor_name, args = match v with
                | Call(lname, args) -> (match lname with
                    | Var((_, ctor_name), _) -> ctor_name, args
                    | _ -> _eval_error loc "Target is not a Constructor" )
                    
                | Cons((_, idx), (_, cname)) -> begin
                    (*  retrieve type definition *)
                    let info = get_rte_variable idx ctx in
                    let Inductive(_, _, _, ctor_def) = info in
                    try let args = SMap.find cname ctor_def in
                        cname, args
                    with 
                        Not_found ->
                            _eval_error loc "Constructor does not exist" end 
                            
                | _ -> lexp_print target;
                    _eval_error loc "Can't match expression" in
                
            (*  Check if a default is present *)
            let run_default df = 
                match df with
                | None -> Imm(String(loc, "Match Failure")), ctx
                | Some lxp -> _eval lxp ctx in
            
            let ctor_n = List.length args in
            
            (*  Build a filter option *)
            let is_true key value =
                let (_, pat_args, _) = value in
                let pat_n = List.length pat_args in
                    if pat_n = ctor_n && ctor_name = key then 
                        true
                    else 
                        false in
                        
            (*  Search for the working pattern *)
            let sol = SMap.filter is_true pat in
                if SMap.is_empty sol then
                    run_default dflt
                else
                    (*  Get working pattern *)
                    let key, (_, pat_args, exp) = SMap.min_binding sol in
                    
                    (* build context *)
                    let nctx = List.fold_left2 (fun nctx pat cl ->
                        match pat with
                            | None -> nctx 
                            | Some (_, (_, name)) -> let (_, xp) = cl in
                                add_rte_variable (Some name) xp nctx) 
                                
                        nctx pat_args args in
                        
                    let r, nctx = _eval exp nctx in
                    (* return old context as we exist the case *)
                        r, ctx end

        | _ -> Imm(String(dloc, "eval Not Implemented")), ctx 
        
and build_arg_list args ctx =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> let (v, c) = _eval e ctx in v) args in
    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and build_ctx decls ctx =
    match decls with
        | [] -> ctx
        | hd::tl -> 
            let (v, exp, tp) = hd in
            let (value, nctx) = _eval exp ctx in
            let nctx = add_rte_variable None value nctx in  
                build_ctx tl nctx
;;


let eval lxp ctx = 
    try
        _eval lxp ctx
    with 
        e -> print_rte_ctx ctx;
        Imm(String(dloc, "Evaluation Failed")), ctx
;;

let print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    match lxp with
        | Imm(v) -> sexp_print v; print_string "\n"
        | e ->  lexp_print e; print_string "\n"
;;

let evalprint lxp ctx = 
    let v, ctx = (eval lxp ctx) in
    print_eval_result 0 v;
    ctx
;;

(*
let eval_string (str: string) tenv grm limit lxp_ctx rctx =
    let pretoks = prelex_string str in
    let toks = lex tenv pretoks in
    let sxps = sexp_parse_all_to_list grm toks limit in
    let pxps = pexp_parse_all sxps in
    let lxp, lxp_ctx = lexp_parse_all pxps lxp_ctx in
        (eval lxp rctx), lxp_ctx
;;

*)

