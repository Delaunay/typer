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
(*open Typecheck  env_elem and env_type *)

module S = Subst

let debruijn_error l m = msg_error "DEBRUIJN" l m; internal_error m
let debruijn_warning = msg_warning "DEBRUIJN"

(*  Type definitions
 * ---------------------------------- *)

(* easier to debug with type annotations *)
type env_elem = (int * vdef option * varbind * ltype)
type env_type = env_elem myers


(* This exist because I don't want that file to depend on anything *)
module StringMap
    = Map.Make (struct type t = string let compare = String.compare end)

type db_idx  = int (* DeBruijn index.  *)
type db_ridx = int (* DeBruijn reverse index (i.e. counting from the root).  *)

(*  Map matching variable name and its distance in the current scope *)
type scope = db_ridx StringMap.t  (*  Map<String, db_ridx>*)

type senv_length = int  (* it is not the map true length *)
type senv_type = senv_length * scope

(*
 * outer_size represent the size of the context before entering a "temporary" scope
 * (i.e, function call, case, lambda...)
 * it is used to determine if a variable is bound or not
 *
 *  if var_idx > outer_ctx_size - current_ctx_size then
 *      free_variable
 *  else
 *      bound_variable
 *
 * r_offset was used when parsing declarations. It represented the index of
 * the declaration being parsed
 *
 * Both were used in an older version I left them as we may need to determine
 * if a variable is free or not later on
 *)
(* name -> index * index -> info * (outer_size, r_offset) *)
type lexp_context = senv_type * env_type * (int * int)

(*  internal definitions
 * ---------------------------------- *)

let _make_scope = StringMap.empty
let _make_senv_type = (0, _make_scope)
let _make_myers = nil
let _get_env(ctx: lexp_context): env_type = let (_, ev, _) = ctx in ev

(*  Public methods: DO USE
 * ---------------------------------- *)

let make_lexp_context = (_make_senv_type, _make_myers, (0, 0))

let get_roffset ctx = let (_, _, (_, rof)) = ctx in rof

let get_size ctx = let ((n, _), _, _) = ctx in n

(*  return its current DeBruijn index *)
let rec senv_lookup (name: string) (ctx: lexp_context): int =
    let ((n, map), _, (csize, rof)) = ctx in
    let raw_idx =  n - (StringMap.find name map) - 1 in (*
        if raw_idx > (n - csize) then
            raw_idx - rof   (* Shift if the variable is not bound *)
        else *)
        raw_idx

(*  We first add variable into our map. Later on, we will add them into
 *  the environment. The reason for this is that the type info is
 *  known after lexp parsing which need the index fist *)
let senv_add_var (loc, name) ctx =
    let ((n, map), e, f) = ctx in
    (try let _ = senv_lookup name ctx in
         debruijn_warning loc ("Variable Shadowing " ^ name);
     with Not_found -> ());
    let nmap = StringMap.add name n map in
    ((n + 1, nmap), e, f)

let env_add_var_info var (ctx: lexp_context) =
    let (a, env, f) = ctx in
        (a, cons (var) env, f)

let env_extend (ctx: lexp_context) (def: vdef) (v: varbind) (t: lexp) =
  let ((n, map), e, f) = ctx in
    env_add_var_info (1, Some def, v, t) (senv_add_var def ctx)


let _name_error loc estr str =
    if estr = str then () else
    debruijn_error loc ("DeBruijn index refers to wrong name. " ^
                      "Expected: \"" ^ estr ^ "\" got \"" ^ str ^ "\"")

(*
let env_set_var_info ctx (def: vref) (v: lexp option) (t: lexp) =
    let ((dv_size, _), info_env, _) = ctx in
    let ((loc, ename), dbi) = def in

    try(let rf = (Myers.nth dbi info_env) in
        let (_, (_, name), _, _) = !rf in

        (* Check if names match *)
        _name_error loc ename name;

        rf := (0, (loc, ename), v, t))
    with
        Not_found -> debruijn_error loc "DeBruijn index out of bounds!" *)

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
    mkSusp ltp (S.shift (idx + 1))

let env_lookup_expr ctx (v : vref): lexp =
  let (_, idx) = v in
  let (r, _, lxp, _) =  _env_lookup ctx v in

  let lxp = match lxp with
    | LetDef lxp -> lxp
    | _ -> Sort (dummy_location, Stype (SortLevel (SLn 0))) in

     mkSusp lxp (S.shift (idx + 1 - r))

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
      | Mcons((_, Some (b, n), _, _) as elem, tl1, i, tl2) ->
        if n = name then
          (cons by tl1), acc
        else
          (* Skip some elements if possible *)
          if idx < i then replace_by' tl1 by (elem::acc)
          else replace_by' tl2 by (elem::acc)
            (* replace_by' tl1 by (elem::acc) *) in

  let nenv, decls = replace_by' env by [] in
  (* add old declarations *)
  let nenv = List.fold_left (fun ctx elem -> cons elem ctx) nenv decls in
    (a, nenv, b)

(* shift an entire expression by n  *)
let rec db_shift expr n =
  let db_shift lxp = db_shift lxp n in
    match expr with
    (* Nothing to shift *)
     | Imm _       -> expr
     | SortLevel _ -> expr
     | Sort _      -> expr
     | Builtin _   -> expr

     | Var (s, idx)       -> Var(s, idx + n)
     | Susp(lxp, s)       -> Susp(db_shift lxp, s)
     | Cons((s, idx), t)  -> Cons((s, idx + n), t)

     | Let(l, decls, lxp) ->
      let decls = List.map (fun (var, lxp, ltp) ->
        var, db_shift lxp, db_shift ltp) decls in
          Let(l, decls, db_shift lxp)

     | Arrow(kind, var, ltp, l, lxp) ->
      Arrow(kind, var, db_shift ltp, l, db_shift lxp)

     | Lambda(kind, var, ltp, lxp) ->
      Lambda(kind, var, db_shift ltp, db_shift lxp)

     | Call(lxp, args) ->
      let args = List.map (fun (kind, lxp) -> (kind, db_shift lxp)) args in
        Call(db_shift lxp, args)

     | Inductive(l, nm, fargs, ctors) ->
      let fargs = List.map (fun (kind, var, ltp) -> (kind, var, db_shift ltp))
        fargs in
      let ctors = SMap.map (fun args ->
        List.map (fun (kind, var, ltp) -> (kind, var, db_shift ltp)) args)
        ctors in
          Inductive(l, nm, fargs, ctors)

     | Case(l, tlxp, tltp, retltp, branch, dflt) ->
      let dflt = match dflt with
        | Some lxp -> Some (db_shift lxp)
        | None -> None in

      let branch = SMap.map (fun (l, args, lxp) ->
        (l, args, db_shift lxp)) branch in
          Case(l, db_shift tlxp, db_shift tltp, db_shift retltp, branch, dflt)


