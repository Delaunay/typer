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
            
        (*  Symbol i.e identifier /!\ A lot of Pvar are not variables /!\ *)
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
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, UnknownType(tloc), lbody), ctx (* /!\ Missing Type *)
            
        (* Function Call *)
        | Pcall (fname, args) ->
            let fname, ctx = lexp_parse fname ctx in
            Call(fname, (Aexplicit, UnknownType(tloc))::[]), ctx
            
        | _ 
            -> UnknownType(tloc), ctx

and lexp_parse_let decls ctx =

    (*  Merge Type info and declaration together  since we don't know where the
        type info will be a map is used to merge together declaration *)
    let rec loop (decls: (pvar * pexp * bool) list) (merged: declarations) ctx: 
                ((vdef * lexp * ltype) list * lexp_context) =
                
        print_int (List.length decls); print_string "\n";
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
                    
                (* if we declared a function *)
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
            
        | Call(fname, args) -> begin  (*  /!\ Partial Print *)
            let str = match fname with
                | Var((_, name), _) -> name
                | _ -> "unkwn" in
            match str with
                (* Special Operator *)
                | "_=_" -> print_string ("(lhs" ^ " = " ^ "rhs)")
                | "_+_" -> print_string ("(lhs" ^ " + " ^ "rhs)")
                | "_-_" -> print_string ("(lhs" ^ " - " ^ "rhs)")
                | "_/_" -> print_string ("(lhs" ^ " / " ^ "rhs)")
                | "_*_" -> print_string ("(lhs" ^ " * " ^ "rhs)")
                (* not an operator *)
                | _ -> print_string ("(" ^ str ^ ")") end

        (* debug catch all *)
        | UnknownType (loc)      -> print_string "unkwn";
        | _ -> print_string "expr"
            
and lexp_print_decls decls = 
    List.iter (fun g -> match g with
        | ((loc, name), expr, ltyp) ->
            print_string (name ^  ": "); lexp_print ltyp; print_string "; ";
            print_string (name ^ " = "); lexp_print expr; print_string "; ")
        decls
;;
            
let lexp_parse_all (p: pexp list) (ctx: lexp_context): 
                                        (lexp list * lexp_context) =
    let rec loop (plst: pexp list) ctx (acc: lexp list) = 
        match plst with
            | [] -> ((List.rev acc), ctx)
            | _  -> let lxp, new_ctx = lexp_parse (List.hd plst) ctx in
                    (loop (List.tl plst) new_ctx (lxp::acc)) in
    (loop p ctx [])
;;