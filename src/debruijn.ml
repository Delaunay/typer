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
 *          Specifies recursive data structure for DeBruijn indexing
 *          methods starting with '_' are considered private and should not
 *          elsewhere in the project
 *
 *      Methods:
 *          make_context     : make an empty context
 *          add_scope ctx    : add new scope to the current context
 *          find_var name ctx: return the index of the variable 'name'
 *          add_variable name loc ctx : add a variable to the current context
 *
 * ---------------------------------------------------------------------------*)

open Util

let debruijn_error = msg_error "DEBRUIJN"
let debruijn_warning = msg_warning "DEBRUIJN"

(*  Type definitions
 * ---------------------------------- *)

(* This exist because I don't want that file to depend on anything *)
module StringMap
    = Map.Make (struct type t = string let compare = String.compare end)
;;

(*  Map matching variable name and its distance in the current scope *)        
type scope = (int) StringMap.t  (*  Map<String, int>*)

(* Offset is the number to take us out of the inner scope
 * Scope is the Mapping between Variable's names and its current index loc 
 *                Offset + Scope *)
type context_impl = int * scope 

(*  The recursive type that does everything  
 *                   inner Scope * Outer Scope  *)
type lexp_context = context_impl * lexp_context option 


(*  internal definitions: DO NOT USE
 * ---------------------------------- *)
 
let _make_scope = StringMap.empty;;
let _make_context_impl = (0, _make_scope);;

let _get_inner_ctx (ctx: lexp_context) =
    match ctx with
        | (ct, _) -> ct
;;

let _get_inner_scope (ctx: lexp_context): scope =
    let ictx = _get_inner_ctx ctx in 
    match ictx with
        | (_, scope) -> scope
;;

(*  get current offset *)
let _get_offset (ctx: lexp_context): int =
    let inner = _get_inner_ctx ctx in
    match inner with
        | offset, _ -> offset
;;

(*  increase the offset *)
let _inc_offset (ctx: lexp_context): lexp_context =
    (*  Because using ref is hell, we make a copy *)
    match ctx with
        | ((offset, scope), None) -> ((offset + 1, scope), None)
        | ((offset, scope), Some outter) -> ((offset + 1, scope), Some outter)
;;

(*  Public methods: DO USE
 * ---------------------------------- *)

(*  return its current DeBruijn index
 *  return -1 if the variable does not exist 
 *  return closest variable *)
let rec find_var (name: string) (ctx: lexp_context) =
    (*  Search *)
    let local_index = find_local name ctx in
    if  local_index >= 0 then 
        local_index
    else
    begin
        let outter_index = _find_outer name ctx in
        if outter_index >= 0 then 
            outter_index + (_get_offset ctx)
        else
            -1  
    end
    
and find_local (name: string) (ctx: lexp_context): int =
    try
        let inner = _get_inner_scope ctx in
            StringMap.find name inner
    with
        Not_found -> -1
    
(*  You should not use this function 'find_var' is the way
 *  the reason is _find_outer does not send back a correct index *)
and _find_outer (name: string) (ctx: lexp_context): int =
    match ctx with
        | (_, Some ct) -> (find_var name ct) 
        | _ -> -1
;;

(*  Alias *)
let get_var_index name ctx = find_var name ctx;;
     
let add_variable name loc ctx =
    (*  I think this should be illegal *)
    let local_index = find_local name ctx in
    if  local_index >= 0 then  (* This is the index not the number of element *)
        debruijn_warning loc ("Variable Redefinition: " ^ name);
        
    let outer_index = _find_outer name ctx in
    if  outer_index >= 0 then
        debruijn_warning loc ("Variable Shadowing: " ^ name);

    (*  Increase distance *)
    let scope = StringMap.map (fun value -> value + 1) (_get_inner_scope ctx) in
    (*  Add new Value *)
    let new_scope = StringMap.add name 0 scope in
        (* build new context *)
        match ctx with
            | ((offset, _), None) 
                -> ((offset + 1, new_scope), None)
            | ((offset, _), Some outter) 
                -> ((offset + 1, new_scope), Some outter)
;;

(*  Make a Global context *)
let make_context = (_make_context_impl, None);;

(*  Make a new Scope inside the outer context 'ctx' *)
let add_scope ctx = (_make_context_impl, Some ctx);;
     
(*  Print Functions for testing *)
let print_scope (scp: scope) (offset: int): unit =
    StringMap.iter 
        (fun key value 
            -> print_string (key ^ "\t"); 
                print_int (value + offset); 
                print_string "\n")
        scp
;;

let print_lexp_context (ctx: lexp_context): unit =
    print_string "  Context Print\n";
    
    let rec impl (ctx2: lexp_context) (offset: int) =
        let inner = _get_inner_scope ctx2 in
        match ctx2 with
            | (_, Some ct) 
                -> impl ct ((_get_offset ctx2) + offset);
                   (print_scope inner offset);
            | _ -> (print_scope inner offset) in
    (impl ctx 0)
;;