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
 

open Sexp
open Pexp
open Lexp

(* Shortcut => Create a Var *)
let make_var name index loc = 
    Var(Vref(Vdef(loc, name), index))
;;

let not_implemented_error =
    internal_error "not implemented"
;;

let msg_warning msg loc =
    let print_loc = print_string "/!\ [";  print_loc loc; print_string "]\t";
    print_string (msg ^ "\n")
;;

(*   
 *      DeBruijn utilities
 *
 *  We recommend using the specified accessors to modify lexp_contex
 *)

(*  Map matching variable name and its distance in the current scope *)        
type scope = (int) SMap.t

(*  Constructor *)
let make_scope = SMap.empty;;

(*  offset is the number needed to exit current scope  *)     
              (* offset * outter scope * current scope *)
type lexp_contex = int ref * lexp_contex option * scope

(*  Constructor *)
let make_lexp_ctx = (0, None, make_scope);;

(*  Make recursion end *)
let _empty_lexp_ctx = lexp_contex;;

(*  private function *)
let _get_outter_scope ctx =
    match ctx with
        | (_, Some scope, _) -> scope
        | _ -> _empty_lexp_ctx
;;

let _get_inner_scope ctx =
    match ctx with
        | (_, _, scope) -> scope
;;

let _get_offset ctx = 
    match ctx with
        | (offset, Some outter, inner) -> !offset
;;

(*  Increment offset of a ctx object *)
let _inc_offset ctx:
    match ctx with
        | (offset, _, _) -> offset := !offset + 1

(*  Find local variable *)     
let find_local name ctx =
    let data = SMap.find name (_get_inner_scope ctx)
;;

(*  Find variable declared outside current scope *)
let find_outter name ctx = 
    let data = SMap.find name (_get_outter_scope ctx)
;;

(* find variable return its current DeBruijn index
 *  return -1 if the variable does not exist *)
let find_var name ctx =
    (*  Search *)
    let local_index = find_local name ctx in
    if  local_index then 
        local_index
    else
    begin
        let outter_index = find_outter name ctx in
        if outter_index then 
            find_outter + (_get_offset ctx)
        else
            -1  
    end
;;

(*  Alias *)
let get_var_index name ctx = find_var name ctx;
        
(* Add a variable in the current context *)
let add_var name loc ctx =
    (*  I think this should be an error and not a warning *)
    let local_index = find_local name ctx in
    if  local_index then
        msg_warning ("Variable Redefinition: " ^ name) loc;
        
    let outter_index = find_outter name ctx in
    if outter_index then
        msg_warning ("Variable Shadowing: " ^ name) loc;
        
    (* add the definition *)
    SMap.add name 0 (_get_inner_scope ctx);
    _inc_offset ctx;
    
    (*  return new var*)
    make_var name 0 loc
;;



(*
 *  The main job of lexp (currently) is determine variable name (index)
 *  and to regroup type specification with their variable 
 *)
 
let rec lexp_parse (p: pexp) (ctx: lexp_contex): lexp =
    (* So I don't have to extract it *)
    let tloc = pexp_location p in
    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value 
            -> Imm(value)
            
        (*  Symbol i.e identifier *)
        | Pvar (loc, Symbol(_, name))    
            -> (make_var name -1 tloc)
        
        | Plet (loc, decl, body)         
            -> Let(tloc, parse_decls decl, lexp_parse body)
            
        (*  Function Types *)
        | Parrow (kind, _, type1, loc, type2) 
            -> Arrow(kind, var, type1, tloc, type2) 
            
        (* *)
        | Plambda (kind , var, args, body)
            -> Lambda(Kind, vdef, ltype, body)
            
        (* Function Call *)
        | Pcall (fname, args)
            -> Call(lex_parse fname, parse_args args)
            
        | Pinductive (label, args, ctors)
            -> Inductive(tloc, label, args, ctors_map)
            
        | Pcons (name, sym)
            -> Cons(make_var name -1 tloc, sym)
            
        (* Case Force default case to throw an error ? *)
        | Pcase (loc, target, patterns)
            -> Case(loc, lexp_parse target, ttype, patterns_map, def)
            
        (* Default *)
        | _ -> internal_error "Forbidden Pexp"
        (*
            | Phastype (l,_,_) -> l
            | Pmetavar (l, _) -> l
         *)
         
(*
 *  DeBruijn indices for variables
 *      All new variable are named v0
 *
 *      Example:
 *          b = 2;
 *          d = 3;
 *
 *          let a = b, c = d in
 *              e = a + b
 *              f = e + a
 *              let g = f + e in
 *                  h = 2 * g
 *      Solution:
 *          v0 = 2;
 *          v0 = 3;
 *
 *          let v0 = v2, v0 = v2 in
 *              v0 = v3 + v5
 *              v0 = v1 + v4
 *              let v0 = v2 + v3 in
 *                  v0 = 2 * v2 
 *
 *  Order Matters
 *
 *)
and parse_decls decls =
    (*                       name   expr  type? 
     * - Plet of location * (pvar * pexp * bool) list * pexp
     *                              TO
     *  - Let of location * (vdef * lexp * ltype) list * lexp *)
    
    (* Get First two *)
    let get_decl decls : (pexp * ltype * (pvar * pexp * bool) list)=
        let expr = List.hd decls in
            let tpe = List.hd (List.hd decls) in
                match tpe with
                    | (_, _, true) -> (expr, tpe, List.tail (List.hd decls))
                    | (_, _, false) -> (expr, UnkownType, List.tail decls)
        
    
    


and parse_args args = not_implemented_error
    
