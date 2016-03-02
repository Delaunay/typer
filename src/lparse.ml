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
 *          parse pexp expression into lexp
 *
 * --------------------------------------------------------------------------- *)

open Util
open Sexp
open Pexp
open Lexp
open Grammar
open Debruijn
open Fmt

(* Shortcut => Create a Var *)
let make_var name index loc = 
    Var(((loc, name), index))
;;

let not_implemented_error () =
    internal_error "not implemented"
;;

let lexp_error loc msg = 
    msg_error "LEXP" loc msg;
    raise (internal_error msg)
;;

let dloc = dummy_location
let lexp_warning = msg_warning "LEXP"

(*  Print back in CET (Close Enough Typer) easier to read *)
              (*  pretty ? * indent level * print_type? *)
type print_context = (bool * int * bool)

(* Vdef is exactly similar to Pvar but need to modify our ctx *)
let pvar_to_vdef p =
    p
;;
(*  PEXP is not giving SEXP types this is why types are always unknown *)

(*
 *  The main job of lexp (currently) is to determine variable name (index)
 *  and to regroup type specification with their variable 
 *)
 
let rec lexp_parse (p: pexp) (ctx: lexp_context): (lexp * lexp_context) =
    (* So I don't have to extract it *)
    let tloc = pexp_location p in
    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value -> Imm(value), ctx
            
        (*  Symbol i.e identifier /!\ A lot of Pvar are not variables /!\ *)
        | Pvar (loc, name) -> 
            let idx = senv_lookup name ctx in
            (* This should be an error but we accept it for debugging *)
            if idx < 0 then
                lexp_warning tloc ("Variable: '" ^ name ^ "' does not exist");
            (make_var name (idx) loc), ctx; 
        
        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->         (* /!\ HERE *)    
            let decl, nctx = lexp_parse_let decls (add_scope ctx) in
            let bdy, nctx = lexp_parse body nctx in
            (*  Send back old context as we exit the inner scope *)
            Let(tloc, decl, bdy), ctx
            
        (* ->/=> *)
        | Parrow (kind, Some var, tp, loc, expr) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let ltyp, ctx = lexp_parse tp ctx in
            let lxp, ctx = lexp_parse expr ctx in
            Arrow(kind, Some nvar, ltyp, tloc, lxp), ctx
            
        | Parrow (kind, None, tp, loc, expr) ->
            let ltyp, ctx = lexp_parse tp ctx in
            let lxp, ctx = lexp_parse expr ctx in
            Arrow(kind, None, ltyp, tloc, lxp), ctx
            
        (*  *)
        | Plambda (kind, var, Some ptype, body) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let ltyp, ctx = lexp_parse ptype ctx in
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, ltyp, lbody), ctx
            
        | Plambda (kind, var, None, body) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)(* /!\ Missing Type *)
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, UnknownType(tloc), lbody), ctx 
            
        (* Function Call *)
        | Pcall (fname, _args) ->
            (*  Why function names are pexp ? *)
            let fname, ctx = lexp_parse fname ctx in
            
            let pargs = pexp_parse_all _args in
            let largs, fctx = lexp_parse_all pargs ctx in 
            
            (*  Make everything explicit for now *)
            let new_args = List.map (fun g -> (Aexplicit, g)) largs in

            Call(fname, new_args), ctx

        (* Pinductive *)
        | Pinductive (label, _, ctors) ->
            let dummy = (Aexplicit, (dummy_location, "a"), UnknownType(tloc))::[] in
            let map_ctor, nctx = lexp_parse_constructors ctors ctx in
            (*  We exit current context, return old context *)
            Inductive(tloc, label, dummy, map_ctor), ctx
            
        (* Pcons *)
        | Pcons(var, sym) -> (* vref, symbol*)
            let (loc, name) = var in
            let idx = 0 in
            Cons(((pvar_to_vdef var), idx), sym), ctx
            
        (* Pcase *)
        | Pcase (loc, target, patterns) ->

            let lxp, ltp = lexp_p_infer target ctx in
            
            (*  Read patterns one by one *)
            let rec loop ptrns merged dflt =
                match ptrns with
                    | [] -> merged, dflt
                    | hd::tl -> 
                        let (pat, exp) = hd in
                        (*  Parse the pattern first then parse the expr *)
                        let (name, iloc, arg) = lexp_read_pattern pat exp lxp in
                        let exp, nctx = lexp_parse exp ctx in
                        if name = "_" then
                            loop tl merged (Some exp)
                        else
                            let merged = SMap.add name (iloc, arg, exp) merged in
                            loop tl merged dflt in
                                
            let (lpattern, dflt) = loop patterns SMap.empty None in
            Case(loc, lxp, ltp, lpattern, dflt), ctx 
            
        | _ 
            -> UnknownType(tloc), ctx
    
(*  Read a pattern and create the equivalent representation *)    
and lexp_read_pattern pattern exp target: 
                     (string * location * (arg_kind * vdef) option list) =

    match pattern with
        | Ppatany (loc) ->            (* Catch all expression nothing to do  *)
            ("_", loc, [])  
            
        | Ppatvar (loc, name) ->      (* Create a variable containing target *)
            (*let nctx = add_variable name loc ctx in
            let idx = get_var_index name nctx in
            let info = (idx, (loc, name), target, UnknownType(loc)) in
            let nctx = add_variable_info info nctx in *)
                (name, loc, [])

        | Ppatcons (ctor_name, args) ->
            let (loc, name) = ctor_name in

            (* read pattern args *)
            let args = lexp_read_pattern_args args in
                (name, loc, args)
            
(*  Read patterns inside a constructor *)
and lexp_read_pattern_args args:((arg_kind * vdef) option list) =

    let rec loop args acc =
        match args with
            | [] -> (List.rev acc)
            | hd::tl -> 
                let (_, pat) = hd in
                match pat with
                    (* Nothing to do *)
                    | Ppatany (loc) -> loop tl (None::acc)
                    | Ppatvar (loc, name) -> 
                        (* get kind from the call *)
                        let nacc = (Some (Aexplicit, (loc, name)))::acc in
                        loop tl nacc
                    | _ -> lexp_error dloc "Constructor inside a Constructor"; 

    in loop args []
 
(*  Parse inductive constructor *)
and lexp_parse_constructors ctors ctx =
    
    let make_args (args:(arg_kind * pvar option * pexp) list):
                                       (arg_kind * ltype) list * lexp_context = 
        let rec loop args acc ctx =
            match args with
                | [] -> (List.rev acc), ctx
                | hd::tl -> begin
                    match hd with
                        (* What does the optional Pvar do ?
                                        that expression does not exist in LEXP*)
                        | (kind, _, exp) -> 
                        let lxp, nctx = lexp_parse exp ctx in
                        loop tl ((kind, lxp)::acc) nctx end in
        loop args [] ctx in
         
    let rec loop ctors merged ctx =
        match ctors with
            | [] -> merged, ctx
            | hd::tl -> begin 
                match hd with   
                    | ((loc, name), args) ->
                        let largs, nctx = make_args args in
                        let nmerged = SMap.add name largs merged in
                        (loop tl nmerged ctx)
            end in 
            
    loop ctors SMap.empty ctx

(*  Parse let declaration *)
and lexp_parse_let decls ctx =

    (*  Merge Type info and declaration together                      *)
    (*  We use a list because order matters and Maps reorder elements *)
    let rec is_equal target (p:(vdef * pexp option * pexp option)): bool =
        let ((_, name), _, _) = p in
            if name == target then true else false in
            
    let rec loop (decls: (pvar * pexp * bool) list) merged: 
                                    (vdef * pexp option * pexp option) list =
                
        (*  we cant evaluate here because variable are not in the environment *)
        match decls with
            | [] -> List.rev merged
            | hd::tl ->
                match hd with
                (*  Type Info: Var:Type *)
                | ((loc, name), type_info, true) -> begin
                    try
                        (*  If found its means the instruction was declared 
                         *  before the type info. Should we allow this? *)
                        let (vd, inst, _) = List.find (is_equal name) merged in
                        let new_decl = (vd, inst, Some type_info) in
                        (loop tl (new_decl::merged))
                    with Not_found ->
                        let new_decl = (loc, name), None, Some type_info in
                        (loop tl (new_decl::merged)) end
                    
                (* Instruction: Var = expr *)
                | ((loc, name), inst, false) -> begin
                    try
                        let (vd, _, ptyp) = List.find (is_equal name) merged in
                        let new_decl = (vd, Some inst, ptyp) in
                        (loop tl (new_decl::merged))
                    with Not_found ->
                        let new_decl = ((loc, name), Some inst, None) in
                        (loop tl (new_decl::merged)) end in
                        
    let decls = loop decls [] in
    
    (*  Add Each Variable to the environment *)
    let rec add_var_env decls ctx =
        match decls with
            | [] -> ctx
            | hd::tl -> begin
                match hd with 
                    (*  Unused variable: No Instruction *)
                    (*  Warning will be printed later   *)
                    | ((loc, name), None, _) -> add_var_env tl ctx 
                    | ((loc, name), _, _) -> 
                        let ctx = senv_add_var name loc ctx in
                            add_var_env tl ctx end in
            
    let nctx = add_var_env decls ctx in
    
    (* lexp_parse instruction and types *)
    let rec parse_decls decls ctx acc =
        match decls with
            | [] -> (List.rev acc), ctx
            | hd::tl -> begin
                match hd with 
                    | ((loc, name), Some pinst, Some ptype) ->
                        let linst, nctx = lexp_parse pinst ctx in
                        let ltyp, nctx = lexp_parse ptype nctx in
                        let nacc = ((loc, name), linst, ltyp)::acc in
                        let nctx = 
                            env_add_var_info (0, (loc, name), linst, ltyp) nctx in
                        (parse_decls tl nctx nacc)
                    | ((loc, name), Some pinst, None) ->
                        let linst, nctx = lexp_parse pinst ctx in
                        (*  This is where UnknownType are introduced *)
                        (*  need Inference HERE *)
                        let nacc = ((loc, name), linst, UnknownType(loc))::acc in
                        let nctx = 
                            env_add_var_info (0, (loc, name), linst, UnknownType(loc)) nctx in
                        (parse_decls tl nctx nacc) 
                    (* Skip the variable *)
                    | ((loc, name), None, _) -> 
                        lexp_warning loc "Unused Variable";
                        (parse_decls tl ctx acc) 
                         end in
                        
    parse_decls decls nctx []
    
and lexp_parse_all (p: pexp list) (ctx: lexp_context): 
                                        (lexp list * lexp_context) =
    let rec loop (plst: pexp list) ctx (acc: lexp list) = 
        match plst with
            | [] -> ((List.rev acc), ctx)
            | _  -> let lxp, new_ctx = lexp_parse (List.hd plst) ctx in
                    (loop (List.tl plst) new_ctx (lxp::acc)) in
    (loop p ctx [])

(*
 *      Type Inference
 * --------------------- *)
(* Parsing a Pexp into an Lexp is really "elaboration", i.e. it needs to
 * infer the types and perform macro-expansion.  For won't really
 * do any of that, but we can already start structuring it accordingly.
 *
 * More specifically, we do it with 2 mutually recursive functions:
 * one takes a Pexp along with its expected type and return an Lexp
 * of that type (hopefully), whereas the other takes a Pexp and
 * infers its type (which it returns along with the Lexp).
 * This is the idea of "bidirectional type checking", which minimizes
 * the amount of "guessing" and/or annotations.  Basically guessing/annotations
 * is only needed at those few places where the code is not fully-normalized,
 * which in normal programs is only in "let" definitions.
 * So the rule of thumbs are:
 * - use lexp_p_infer for destructors, and use lexp_p_check for constructors.
 * - use lexp_p_check whenever you can.
 *)
 
and lexp_p_infer (p : pexp) (env : lexp_context) : lexp * ltype =
    let lxp, nctx = lexp_parse p env in
        lxp, UnknownType(dummy_location)

and lexp_p_check (env : lexp_context) (p : pexp) (t : ltype) : lexp =
  match p with
  | _
    -> let (e, inferred_t) = lexp_p_infer p env in
      (* FIXME: check that inferred_t = t!  *)
      e
(*
 *      Printing
 * --------------------- *)
(* So print can be called while parsing *)
and lexp_print_adv opt exp =
    let slexp_print = lexp_print_adv opt in (* short_lexp_print *)
    let (pty, indent, prtp) = opt in
    match exp with
        | Imm(value)             -> sexp_print value
        | Var ((loc, name), idx) -> 
            print_string name; 
            if idx > 0 then begin
                print_string "("; print_int idx; print_string ")"; end
        
        | Let (_, decls, body)   ->
            print_string "let"; lexp_print_decls (pty, indent + 1, prtp) decls; 
            if pty then make_line " " (indent * 4 + 4);
            print_string " in "; lexp_print_adv (pty, indent + 2, prtp) body
            
        | Arrow(kind, Some (_, name), tp, loc, expr) ->
            slexp_print tp; print_string ": "; print_string name;
            print_string " -> "; slexp_print expr;
            
        | Arrow(kind, None, tp, loc, expr) ->
            slexp_print tp; print_string " -> "; slexp_print expr;
            
        | Lambda(kind, (loc, name), ltype, lbody) ->
            print_string "lambda ("; print_string (name ^ ": "); 
            slexp_print ltype; print_string ") -> "; slexp_print lbody;
            
        | Cons(vf, symbol) ->
            let (loc, name) = symbol in
            let ((loc, vname), idx) = vf in
                print_string (name ^ "("); print_string (vname ^ ")");
            
        | Call(fname, args) -> begin  (*  /!\ Partial Print *)
            (*  get function name *)
            let str = match fname with
                | Var((_, name), _) -> name
                | _ -> "unkwn" in
                
            let print_arg arg = match arg with | (kind, lxp) -> 
                 lexp_print_adv (pty, 0, prtp) lxp in
                           
            let print_binop op lhs rhs = 
                print_arg lhs; print_string op; print_arg rhs in
                        
            match (str, args) with
                (* Special Operator *)
                | ("_=_", [lhs; rhs]) -> print_binop " = " lhs rhs
                | ("_+_", [lhs; rhs]) -> print_binop " + " lhs rhs
                | ("_-_", [lhs; rhs]) -> print_binop " - " lhs rhs
                | ("_/_", [lhs; rhs]) -> print_binop " / " lhs rhs
                | ("_*_", [lhs; rhs]) -> print_binop " * " lhs rhs
                (* not an operator *)
                | _ -> 
                    print_string ("(" ^ str);
                    List.iter (fun arg -> print_string " "; print_arg arg) args;
                    print_string ")" end

        | Inductive (_, (_, name), _, ctors) ->
            print_string ("inductive_ " ^ name ^ " ");
            lexp_print_ctors opt ctors;
            
        | Case (_, target, tpe, map, dflt) -> begin
            print_string "case "; slexp_print target;
            print_string ": "; slexp_print tpe; 
            
            if pty then print_string "\n";
            
            let print_arg arg =
                 List.iter (fun v -> 
                    match v with
                        | None -> print_string " _"
                        | Some (kind, (l, n)) -> print_string (" " ^ n)) arg in
            
            SMap.iter (fun key (loc, arg, exp) ->
                make_line " " (indent * 4);
                print_string ("| " ^ key); print_arg arg; 
                print_string " -> ";
                slexp_print exp; print_string "; ";
                if pty then print_string "\n";)
                map;
            
            match dflt with
                | None -> ()
                | Some df -> 
                    make_line " " (indent * 4);
                    print_string "| _ -> "; slexp_print df;
                    print_string ";"; if pty then print_string "\n"; end
            
        (* debug catch all *)
        | UnknownType (loc)      -> print_string "unkwn";
        | _ -> print_string "Printint Not Implemented"
        
        
and lexp_print_ctors opt ctors =
    SMap.iter (fun key value ->
            print_string ("(" ^ key ^ ": ");
            List.iter (fun (kind, arg) -> 
                lexp_print_adv opt arg; print_string " ") value;
            print_string ")")
        ctors

and lexp_print_decls opt decls =
    let (pty, indent, prtp) = opt in
    let print_type nm tp =
        print_string (" " ^ nm ^  ": "); lexp_print_adv opt tp; 
        print_string ";"; in

    List.iteri (fun idx g -> match g with
        | ((loc, name), expr, ltyp) ->
            if pty && idx > 0 then make_line " " (indent * 4);
            if prtp then print_type name ltyp; print_string " ";
            print_string (name ^ " = "); 
            lexp_print_adv opt expr; print_string ";";
            if pty then print_string "\n")
        decls
;;


let lexp_print = lexp_print_adv (false, 0, true)
            
