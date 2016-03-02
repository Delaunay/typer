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
 * ---------------------------------------------------------------------------*)

open Util
open Lexp
open Myers
open Fmt

let debruijn_error = msg_error "DEBRUIJN"
let debruijn_warning = msg_warning "DEBRUIJN"

(*  Type definitions
 * ---------------------------------- *)

(*  Index -> Variable Info *) 
type env_elem = (int * (location * string) * lexp * ltype)
type env_type = env_elem myers
 
(* This exist because I don't want that file to depend on anything *)
module StringMap
    = Map.Make (struct type t = string let compare = String.compare end)
;;

(*  Map matching variable name and its distance in the current scope *)        
type scope = (int) StringMap.t  (*  Map<String, int>*)

type senv_length = int  (*  Map length *)
type senv_type = senv_length * scope 

             (* name -> index * index -> info *)
type lexp_context = senv_type * env_type

(*  internal definitions: DO NOT USE
 * ---------------------------------- *)

let _make_scope = StringMap.empty;;
let _make_senv_type = (0, _make_scope);;
let _make_myers = nil

let _get_senv (ctx: lexp_context) =
    let (ct, _) = ctx in ct
;;

let _get_scope(ctx: lexp_context): scope =
    let ((_, ev), _) = ctx in ev
;;

let _get_env(ctx: lexp_context): env_type =
    let (_, ev) = ctx in ev
;;

let _add_var_env variable ctx =
    let (a, env) = ctx in cons variable env
;;

(*  Public methods: DO USE
 * ---------------------------------- *)

let make_lexp_context = (_make_senv_type, _make_myers);;
 
(*  return its current DeBruijn index *)
let rec senv_lookup (name: string) (ctx: lexp_context) =
    try
        let ((n, map), _) = ctx in
            n - (StringMap.find name map) - 1
    with Not_found -> -1
;;
     
(*  We first add variable into our map. Later on, we will add them into 
 *  the environment. The reason for this is that the type info is
 *  known after lexp parsing which need the index fist *)
let senv_add_var name loc ctx =
    let ((n, map), e) = ctx in
    let nmap = StringMap.add name n map in
        ((n + 1, nmap), e)
;;

(*  *)
let env_add_var_info var (ctx: lexp_context) =
    let (a, _) = ctx in
    (* let (rof, (loc, name), value, ltyp) = var in *)
    let nenv = _add_var_env var ctx in
        (a, nenv)
;;

let env_lookup_type_by_index index ctx = 
    try
        let (roffset, (_, name), _, t) = Myers.nth index (_get_env ctx) in
            Shift (index - roffset, t)
    with
        Not_found -> internal_error "DeBruijn index out of bounds!"
;;

let env_lookup_type ctx (v : vref) =
  let ((_, rname), dbi) = v in
  try let (recursion_offset, (_, dname), _, t) = Myers.nth dbi (_get_env ctx) in
      if dname = rname then
        Shift (dbi - recursion_offset, t)
      else
        internal_error "DeBruijn index refers to wrong name!"
  with Not_found -> internal_error "DeBruijn index out of bounds!"

let env_lookup_by_index index ctx = Myers.nth index (_get_env ctx);;
        
        
        
        
        
        
        
        