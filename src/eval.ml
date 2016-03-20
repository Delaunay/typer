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
open Debruijn
open Grammar


let _eval_error loc msg = 
    msg_error "eval" loc msg;
    raise (internal_error msg)
;;

let dloc = dummy_location
let _eval_warning = msg_warning "eval"

type call_trace_type = (int * lexp) list
let global_trace = ref []

let add_call cll i = global_trace := (i, cll)::!global_trace

let reinit_call_trace () =  global_trace := []

let print_myers_list l print_fun = 
    let n = (length l) - 1 in
    
    print_string (make_title " ENVIRONMENT ");
    make_rheader [(None, "INDEX"); (None, "VARIABLE NAME"); (None, "VALUE")];
    print_string (make_sep '-');
    
    for i = 0 to n do
    print_string "    | ";
        ralign_print_int (n - i) 5;
        print_string " | ";
        print_fun (nth (n - i) l);
    done;
    print_string (make_sep '=');
;;

let get_function_name fname =
    match fname with
        | Var(v) -> let ((loc, name), idx) = v in name
        | _ -> "Name Lookup failure"
;;

let get_int lxp =
    match lxp with
        | Imm(Integer(_, l)) -> l 
        | _ -> lexp_print lxp; -40
;;

(*  Runtime Environ *)
type runtime_env = (string option * lexp) myers
let make_runtime_ctx = nil;;
let add_rte_variable name x l = (cons (name, x) l);;



let get_rte_variable (idx: int) (l: runtime_env): lexp = 
    let (_, x) = (nth idx l) in x
;;

let print_rte_ctx l = print_myers_list l 
    (fun (n, g) -> 
        let _ = 
        match n with
            | Some m -> lalign_print_string m 12; print_string "  |  "
            | None -> print_string (make_line ' ' 12); print_string "  |  " in
        lexp_print g; print_string "\n")
;;


let nfirst_rte_var n ctx =
    let rec loop i acc = 
        if i < n then
            loop (i + 1) ((get_rte_variable i ctx)::acc)
        else
            List.rev acc in
    loop 0 []
;;


(* _eval is an internal definition you should use eval or eval_decls *)
let rec _eval lxp ctx i: lexp = 
    add_call lxp i;
    match lxp with
        (*  This is already a leaf *)
        | Imm(v) -> lxp
        
        (*  Return a value stored in the environ *)
        | Var((loc, name), idx) as e -> begin
            (* find variable binding i.e we do not want a another variable *)
            let rec var_crawling expr i k =
                (if k > 255 then(
                    lexp_print expr; print_string "\n"; flush stdout;
                    raise (internal_error "Variable lookup failed")));
                match expr with
                    | Var(_, j) -> 
                        let p = (get_rte_variable (i + j) ctx) in
                            var_crawling p (i + j) (k + 1)
                    | _ -> expr in
                    
            try
                (var_crawling e 0 0)
            with 
                Not_found ->
                    print_string ("Variable: " ^ name ^ " was not found | "); 
                    print_int idx; print_string "\n"; flush stdout;
                    raise Not_found end
                
        (*  this works for non recursive let *)
        | Let(_, decls, inst) -> 
            (*  First we _evaluate all declaration then we eval the instruction *)
            let nctx = build_ctx decls ctx i in
                _eval inst nctx (i + 1) 
                
        (*  Function call *)
        | Call (lname, args) -> (
            (*  Try to extract name *)
            let n = List.length args in
            match lname with
                (*  Hardcoded functions *)
                
                (* + is read as a nested binary operator *)
                | Var((_, name), _) when name = "_+_" ->
                    let nctx = build_arg_list args ctx i in
                    
                    let l = get_int (get_rte_variable 0 nctx) in
                    let r = get_int (get_rte_variable 1 nctx) in 
                    Imm(Integer(dloc, l + r))
                    
                (* _*_ is reas as a single function with x args *)
                | Var((_, name), _) when name = "_*_" ->
                    let nctx = build_arg_list args ctx i in
                    
                    let vint = (nfirst_rte_var n nctx) in
                    let varg = List.map (fun g -> get_int g) vint in
                    let v = List.fold_left (fun a g -> a * g) 1 varg in

                    Imm(Integer(dloc, v))
                
                (* This is a named function call *)
                (*  TODO: handle partial application *)
                | Var((_, name), idx) ->
                    
                    (*  get function body *)
                    let body = get_rte_variable idx ctx in
                    (*  Add args in the scope *)
                    let nctx = build_arg_list args ctx i in
                        _eval body nctx (i + 1)
    
                (* TODO Everything else *)
                (*  Which includes a call to a lambda *)
                | _ -> Imm(String(dloc, "Funct Not Implemented")))
                        
        | Lambda(_, vr, _, body) -> begin 
            let (loc, name) = vr in
            (*  Get first arg *)
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
                _eval body nctx (i + 1) end
       
        (*  Inductive is a type declaration. We have nothing to eval *)
        | Inductive (_, _, _, _) as e -> e
        
        (*  inductive-cons build a type too? *)
        | Cons (_, _) as e -> e
        
        (* Case *) 
        | Case (loc, target, _, pat, dflt) -> begin
            
            (* Eval target *)
            let v = _eval target ctx (i + 1) in
            let nctx = ctx in
            
            (*  V must be a constructor Call *)
            let ctor_name, args = match v with
                | Call(lname, args) -> (match lname with
                    | Var((_, ctor_name), _) -> ctor_name, args
                    | _ -> _eval_error loc "Target is not a Constructor" )
                
                | Cons((_, idx), (_, cname)) -> begin
                    (*  retrieve type definition *)
                    print_int idx;
                    let info = get_rte_variable idx ctx in
                    let Inductive(_, _, _, ctor_def) = info in
                    try let args = SMap.find cname ctor_def in
                        cname, args
                    with 
                        Not_found ->
                            _eval_error loc "Constructor does not exist" end 
                            
                | _ -> lexp_print target; print_string "\n";
                    lexp_print v; print_string "\n";
                    _eval_error loc "Can't match expression" in
                
            (*  Check if a default is present *)
            let run_default df = 
                match df with
                | None -> Imm(String(loc, "Match Failure"))
                | Some lxp -> _eval lxp ctx (i + 1) in
            
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
                        
                    let r = _eval exp nctx (i + 1) in
                    (* return old context as we exist the case *)
                        r end

        | _ -> Imm(String(dloc, "eval Not Implemented"))
        
and build_arg_list args ctx i =
    (*  _eval every args *)
    let arg_val = List.map (fun (k, e) -> _eval e ctx (i + 1)) args in
            
    (*  Add args inside context *)
    List.fold_left (fun c v -> add_rte_variable None v c) ctx arg_val

and build_ctx decls ctx i =
    let f nctx e = 
        let (v, exp, tp) = e in
        let value = _eval exp ctx (i + 1) in
            add_rte_variable None value nctx in

    List.fold_left f ctx decls
                
and eval_decl ((l, n), lxp, ltp) ctx =
    add_rte_variable (Some n) lxp ctx
    
(*  Eval a declaration if a main is found it is returned *)
and eval_decls (decls: ((vdef * lexp * ltype) list)) 
               (ctx: runtime_env): runtime_env =
    let rec loop decls ctx =
        match decls with 
            | [] -> ctx
            | hd::tl -> 
                let ((_, n), lxp, ltp) = hd in
                let nctx = add_rte_variable (Some n) lxp ctx in
                    loop tl nctx in

    loop decls ctx
      
and print_eval_result i lxp =
    print_string "     Out[";
    ralign_print_int i 2;
    print_string "] >> ";
    match lxp with
        | Imm(v) -> sexp_print v; print_string "\n"
        | e ->  lexp_print e; print_string "\n"
;;


let print_first n l f =
    let rec loop i l =
        match l with
            | [] -> ()
            | hd::tl -> 
                if i < n then ((f i hd); loop (i + 1) tl;)
                else () in
    loop 0 l
;;

let _print_ct_tree i =
    print_string "    ";
    let rec loop j =
        if j = i then () else
        match j with 
            | _ when (j mod 2) = 0 -> print_char '|'; loop (j + 1)
            | _ -> print_char ':'; loop (j + 1) in
    loop 0
;;  

let print_call_trace () =
    print_string (make_title " CALL TRACE ");
    
    let n = List.length !global_trace in
    print_string "        size = "; print_int n; print_string "\n";
    print_string (make_sep '-');
    
    let racc = List.rev !global_trace in
        print_first 20 racc (fun j (i, g) -> 
            _print_ct_tree i; print_string "+- ";
            print_string (lexp_to_string g); print_string ": ";
            lexp_print g; print_string "\n");
            
    print_string (make_sep '=');
;;

let eval lxp ctx = 
    try
        _eval lxp ctx 1
    with e -> (
        print_rte_ctx ctx;
        print_call_trace ();
        raise e)
;;


(*  Eval a list of lexp *)
let eval_all lxps rctx = List.map (fun g -> eval g rctx) lxps;;


(*  Eval String
 * ---------------------- *)
let eval_expr_str str lctx rctx =
    global_trace := [];
    let lxps, lctx = lexp_expr_str str lctx in
        (eval_all lxps rctx)
;;

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
        (eval_decls lxps rctx), lctx
;;


