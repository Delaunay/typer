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
module L = Lexp
open Myers
open Fmt
(*open Typecheck  env_elem and env_type *)

module S = Subst

let debruijn_error l m = msg_error "DEBRUIJN" l m; internal_error m
let debruijn_warning = msg_warning "DEBRUIJN"

(*  Type definitions
 * ---------------------------------- *)


type property_key = (int * string)  (* rev_dbi * Var name *)
module PropertyMap
    = Map.Make (struct type t = property_key let compare = compare end)

module StringMap
    = Map.Make (struct type t = string let compare = String.compare end)

(* (* rev_dbi * Var name *) => (name * lexp) *)
type property_elem = lexp PropertyMap.t
type property_env = property_elem PropertyMap.t

(* easier to debug with type annotations *)
type env_elem = (int * vdef option * varbind * ltype)
type env_type = env_elem myers

type db_idx  = int (* DeBruijn index.  *)
type db_ridx = int (* DeBruijn reverse index (i.e. counting from the root).  *)

(*  Map matching variable name and its distance in the current scope *)
type scope = db_ridx StringMap.t  (*  Map<String, db_ridx>*)

type senv_length = int  (* it is not the map true length *)
type senv_type = senv_length * scope

type lexp_context = senv_type * env_type * property_env

(*  internal definitions
 * ---------------------------------- *)

let _make_scope = StringMap.empty
let _make_senv_type = (0, _make_scope)
let _make_myers = nil
let _get_env(ctx: lexp_context): env_type = let (_, ev, _) = ctx in ev

(*  Public methods: DO USE
 * ---------------------------------- *)

let make_lexp_context = (_make_senv_type, _make_myers, PropertyMap.empty)

let get_roffset ctx = let (_, _, (_, rof)) = ctx in rof

let get_size ctx = let ((n, _), _, _) = ctx in n

(*  return its current DeBruijn index *)
let rec senv_lookup (name: string) (ctx: lexp_context): int =
    let ((n, map), _, _) = ctx in
    let raw_idx =  n - (StringMap.find name map) - 1 in (*
        if raw_idx > (n - csize) then
            raw_idx - rof   (* Shift if the variable is not bound *)
        else *)
        raw_idx

let env_extend (ctx: lexp_context) (def: vdef) (v: varbind) (t: lexp) =
  let (loc, name) = def in
  let ((n, map), env, f) = ctx in
  (try let _ = senv_lookup name ctx in
       debruijn_warning loc ("Variable Shadowing " ^ name);
   with Not_found -> ());
  let nmap = StringMap.add name n map in
  (* FIXME: Why a db_offset of 1?  *)
  ((n + 1, nmap), cons (1, Some def, v, t) env, f)


let _name_error loc estr str =
    if estr = str then () else
    debruijn_error loc ("DeBruijn index refers to wrong name. " ^
                      "Expected: \"" ^ estr ^ "\" got \"" ^ str ^ "\"")


(* generic lookup *)
let _env_lookup ctx (v: vref): env_elem  =
    let ((dv_size, _), info_env, _) = ctx in
    let ((loc, ename), dbi) = v in

    try(let ret = (Myers.nth dbi info_env) in
        let _ = match ret with
          | (_, Some (_, name), _, _) ->
              (* Check if names match *)
              _name_error loc ename name;
          | _ -> () in

        ret)
    with
        Not_found -> debruijn_error loc "DeBruijn index out of bounds!"


let env_lookup_type ctx (v : vref): lexp =
  let (_, idx) = v in
  let (_, _, _, ltp) = _env_lookup ctx v in
    mkSusp ltp (S.shift (idx + 0))

let env_lookup_expr ctx (v : vref): lexp option =
  let (_, idx) = v in
  let (r, _, lxp, _) =  _env_lookup ctx v in
  match lxp with
  | LetDef lxp -> Some (L.push_susp lxp (S.shift (idx + 1 - r)))
  (* FIXME: why Sort here?  *)
  | _ -> None

let env_lookup_by_index index (ctx: lexp_context): env_elem =
    (Myers.nth index (_get_env ctx))

(* replace an expression by another *)
(* Most of the time it should be O(1) but it can be O(n)  *)
let replace_by ctx name by =
  let (a, env, b) = ctx in
  let idx = senv_lookup name ctx in
  (* lookup and replace *)
  let rec replace_by' ctx by acc =
    match ctx with
      | Mnil -> debruijn_error dummy_location
            ("Replace error. This expression does not exist: " ^  name)
      | Mcons((_, None, _, _) as elem, tl1, i, tl2) ->
          (* Skip some elements if possible *)
          if idx <= i then replace_by' tl1 by (elem::acc)
          else replace_by' tl2 by (elem::acc)
            (* replace_by' tl1 by (elem::acc) *)

      | Mcons((_, Some (b, n), _, _) as elem, tl1, i, tl2) ->
        if n = name then
          (cons by tl1), acc
        else
          (* Skip some elements if possible *)
          if idx <= i then replace_by' tl1 by (elem::acc)
          else replace_by' tl2 by (elem::acc)
            (* replace_by' tl1 by (elem::acc) *) in

  let nenv, decls = replace_by' env by [] in
  (* add old declarations *)
  let nenv = List.fold_left (fun ctx elem -> cons elem ctx) nenv decls in
    (a, nenv, b)

(* -------------------------------------------------------------------------- *)
(*          PropertyMap                                                       *)
(* -------------------------------------------------------------------------- *)


let add_property ctx (var_i, var_n) (att_i, att_n) (prop: lexp)
    : lexp_context =

  let (a, b, property_map) = ctx in
  let n = get_size ctx in

  (* get_var properties  *)
  let vmap = try PropertyMap.find (var_i, var_n) property_map
    with Not_found -> PropertyMap.empty in

  (* add property *)
  let nvmap = PropertyMap.add (n - att_i, att_n) prop vmap in

  (* update properties *)
  let property_map = PropertyMap.add (n - var_i, var_n) nvmap property_map in

    (a, b, property_map)

let get_property ctx (var_i, var_n) (att_i, att_n): lexp =
  let (a, b, property_map) = ctx in
  let n = get_size ctx in

  (* /!\ input index are reversed or not ? I think not so I shift them *)
  let pmap = try PropertyMap.find (n - var_i, var_n) property_map
    with Not_found ->
      debruijn_error dummy_location ("Variable \"" ^ var_n ^ "\" does not have any properties") in

  let prop = try PropertyMap.find (n - att_i, att_n) pmap
    with Not_found ->
      debruijn_error dummy_location ("Property \"" ^ att_n ^ "\" not found") in
        mkSusp prop (S.shift (var_i + 1))


let has_property ctx (var_i, var_n) (att_i, att_n): bool =
  let (a, b, property_map) = ctx in
  let n = get_size ctx in

  try
    let pmap = PropertyMap.find (n - var_i, var_n) property_map in
    let _ = PropertyMap.find (n - att_i, att_n) pmap in
    true
  with Not_found -> false


let dump_properties ctx =
  let (a, b, property_map) = ctx in
  print_string (make_title " Properties ");

  make_rheader [
        (Some ('l', 10), "V-NAME");
        (Some ('l',  4), "RIDX");
        (Some ('l', 10), "P-NAME");
        (Some ('l',  4), "RIDX");
        (Some ('l', 32), "LEXP")];

  print_string (make_sep '-');

  PropertyMap.iter (fun (var_i, var_n) pmap ->
    print_string "    | ";
    lalign_print_string var_n 10; print_string " | ";
    ralign_print_int var_i 4; print_string " | ";
    let first = ref true in

    PropertyMap.iter (fun (att_i, att_n) lxp ->
      (if (!first = false) then
        print_string (make_line ' ' 20)
      else
        first := false);

      lalign_print_string att_n 10; print_string " | ";
      ralign_print_int att_i 4; print_string " : ";
      lexp_print lxp; print_string "\n") pmap) property_map;

  print_string (make_sep '-');


