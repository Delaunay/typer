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

(* Shortcut => Create a Var *)
let make_var name index loc = 
    Var(((loc, name), index))
;;

let not_implemented_error () =
    internal_error "not implemented"
;;

(* Vdef is exactly similar to Pvar but need to modify our ctx *)
let pvar_to_vdef p =
    p
;;

(* This is used to merge let declaration *)
type declarations = (vdef * lexp * ltype) SMap.t 

(*
 *  The main job of lexp (currently) is determine variable name (index)
 *  and to regroup type specification with their variable 
 *)
 
let rec lexp_parse (p: pexp) (ctx: lexp_context): (lexp * lexp_context) =
    (* So I don't have to extract it *)
    let tloc = pexp_location p in
    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value -> Imm(value), ctx
            
        (*  Symbol i.e identifier *)
        | Pvar (loc, name) -> 
            let idx = get_var_index name ctx in
           (* This should be an error but we currently accept it for debugging *)
           if idx <= 0 then
                msg_warning ("Variable: '" ^ name ^ "' does not exist") tloc;
           (make_var name idx loc), ctx; 
        
        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->         (* /!\ HERE *)    
            let decl, nctx = lexp_parse_let decls ctx in
            let bdy, new_ctx = lexp_parse body nctx in
            Let(tloc, decl, bdy), nctx
            
        (* Parse Type and expression *)
        | Parrow (kind, Some var, tp, loc, expr) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let ltyp, ctx = lexp_parse tp ctx in
            let lxp, ctx = lexp_parse expr ctx in
            Arrow(kind, Some nvar, ltyp, tloc, lxp), ctx
            
        | Parrow (kind, None, tp, loc, expr) ->
            let ltyp, ctx = lexp_parse tp ctx in
            let lxp, ctx = lexp_parse expr ctx in
            Arrow(kind, None, ltyp, tloc, lxp), ctx
            
        | Plambda (kind, var, Some ptype, body) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let ltyp, ctx = lexp_parse ptype ctx in
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, ltyp, lbody), ctx
            
        | Plambda (kind, var, None, body) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, UnknownType(tloc), lbody), ctx (* /!\ Missing Type *)
            
        | _ 
            -> UnknownType(tloc), ctx

and lexp_parse_let decls ctx =

    (*  Merge Type info and declaration together  since we don't know where the
        type info will be a map is used to merge together declaration *)
    let rec loop (decls: (pvar * pexp * bool) list) (merged: declarations) ctx: 
                ((vdef * lexp * ltype) list * lexp_context) =
                
        match decls with
            | [] -> (SMap.fold (fun k d acc -> d::acc) merged []), ctx
            | hd::tl ->
                match hd with
                | ((loc, name), type_info, true) -> begin
                    let new_ltype, nctx = lexp_parse type_info ctx in
                    try
                        let (vd, inst, ltyp) = SMap.find name merged in
                        let new_map = SMap.add name (vd, inst, new_ltype) merged in
                        (loop tl new_map nctx)
                    with Not_found ->
                        let new_decl = (loc, name), UnknownType(loc), new_ltype in
                        let new_map = (SMap.add name new_decl merged) in
                        (loop tl new_map nctx) end
                    
                | ((loc, name), inst, false) -> begin
                    let new_inst, nctx = lexp_parse inst ctx in
                    try
                        let (vd, inst, ltyp) = SMap.find name merged in
                        let new_map = SMap.add name (vd, new_inst, ltyp) merged in
                        (loop tl new_map nctx)
                    with Not_found ->
                        let new_decl = ((loc, name), new_inst, UnknownType(loc)) in
                        let new_map = SMap.add name new_decl merged in
                        (loop tl new_map nctx) end in
    (* use the function *)
    loop decls SMap.empty ctx
;;

(*  Print back in CET (Close Enough Typer) *)
let rec lexp_print exp =
    match exp with
        | Imm(value)             -> sexp_print value
        | Var ((loc, name), idx) -> print_string name;
        
        | Let (_, decls, body)   ->
            print_string "let "; lexp_print_decls decls; 
            print_string " in "; lexp_print body
            
        | Arrow(kind, Some (_, name), tp, loc, expr) ->
            lexp_print tp; print_string ": "; print_string name;
            print_string " -> "; lexp_print expr;
            
        | Arrow(kind, None, tp, loc, expr) ->
            lexp_print tp; print_string " -> "; lexp_print expr;
            
        | Lambda(kind, (loc, name), ltype, lbody) ->
            print_string "lambda ("; print_string (name ^ ": "); 
            lexp_print ltype; print_string ") -> "; lexp_print lbody;

        (* debug catch all *)
        | UnknownType (loc)      -> print_string "unkwn";
        | _ -> print_string "expr"
            
and lexp_print_decls decls = 
    List.iter (fun g -> match g with
        | ((loc, name), expr, ltyp) ->
            print_string (name ^ ": "); lexp_print ltyp;
            print_string " = "; lexp_print expr; print_string "; ")
        decls
;;
            
    

        
       (* 
        | Plet (loc, decl, body)      
            ->  let (decls, letctx) = parse_decls decl (add_scope ctx) in
                let (lbody, _) = lexp_parse body letctx in
                Let(tloc, decls, lbody), ctx
            
        (*  Function Types *)
        | Parrow (kind, _, type1, loc, type2) 
            -> Arrow(kind, var, type1, tloc, type2), ctx
            
        (* *)
        | Plambda (kind , var, args, body)
            -> Lambda(Kind, vdef, ltype, body), ctx
            
        (* Function Call *)
        | Pcall (fname, args)
            -> Call(lex_parse fname ctx, parse_args args), ctx
            
        | Pinductive (label, args, ctors)
            -> Inductive(tloc, label, args, ctors_map), ctx
            
        | Pcons (name, sym)
            -> let new_ctx = add_variable name ctx in
               Cons(make_var name 0 tloc, sym), new_ctx
            
        (* Case Force default case to throw an error ? *)
        | Pcase (loc, target, patterns)
            -> Case(loc, lexp_parse target, ttype, patterns_map, def), ctx
            
        (* Default *)
        | _ -> internal_error "Forbidden Pexp"
        (*
            | Phastype (l,_,_) -> l
            | Pmetavar (l, _) -> l
         *)
         
(*
 *  DeBruijn indices for variables
 *      All new variable are named v0
 
  Example:
      b = 2;
      d = 3;

      let a = b, c = d in
          let g = a + c

  Example:
      b = 2;
      d = 3;

      let (a, c): a = v4, c = v3 in
          let (g): g = v3 + v2
          
 *  Order Matters
 *
 *)
 
 (*                       name   expr  type? 
 * - Plet of location * (pvar * pexp * bool) list * pexp
 *                              TO
 *  - Let of location * (vdef * lexp * ltype) list * lexp 
 *
 *  First we combine definition, then we determine debruijn indexing 
 *  because we need to know the number of parameter the let holds 
 
let a::Nat,
    a = b in

 *)
 
and parse_let loc decls body ctx =
    Let(loc, (Vdef(dummy_location, "??"), UnkownType , UnkownType), (UnkownType))
    
    (*
    (*  1. We merge declaration and type info *)
    let merge declist = (* ((str, loc, pexp, pexp), list) *)
        let first = List.hd decls in
        let sec = List.hd (List.hd decls) in
        
        match (first, sec) with
            | ((Pvar(loc, name1), type_info, true), 
               (Pvar(loc, name2), inst, false)) 
                ->  if name1 == name2 then
                        ((name1, loc, inst, Some type_info),
                         (List.tl (List.tl decls)), new_ctx)
                    else
                        ((name1, loc, inst, None), (List.tl decls))
                        
            | ((Pvar(loc, name1), inst, false), _)    
                -> ((name1, loc, inst, None), (List.tl decls)) in
        
    (*  2. make Plet decl *)
    let make_decl decls ctx = 
        let dec, declist = merge decls in
            match dec with
                | (name, loc, inst, None) 
                    -> let nctx = (add_variable ctx) in
                       (Vdef(loc, name), 
                          lexp_parse inst nctx, UnkownType), declist, nctx
                
                | (name, loc, inst, Some tp) 
                    ->  let nctx = (add_variable ctx) in
                        (Vdef(loc, name), 
                          lexp_parse inst nctx, lexp_parse tp), declist, nctx in
                        
    (*  3. make let *)
    let make_let decls body ctx = 
        let decl, declist, new_ctx = make_decl decls, ctx in
            match declist with
                | [] -> Let(loc, decl, body)
                | _ -> Let(loc, decl, parse_let loc declist body new_ctx) in
                
    make_let decls body ctx*)
        
and parse_args (args) = 
    (Aexplicit, UnkownType)
;;*)

let lexp_parse_all (p: pexp list) (ctx: lexp_context): 
                                        (lexp list * lexp_context) =
    let rec loop (plst: pexp list) ctx (acc: lexp list) = 
        match plst with
            | [] -> ((List.rev acc), ctx)
            | _  -> let lxp, new_ctx = lexp_parse (List.hd plst) ctx in
                    (loop (List.tl plst) new_ctx (lxp::acc)) in
    (loop p ctx [])
;;