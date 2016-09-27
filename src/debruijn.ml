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
module M = Myers
open Fmt

module S = Subst

let debruijn_error l m = msg_error "DEBRUIJN" l m; internal_error m
let debruijn_warning = msg_warning "DEBRUIJN"

(*  Type definitions
 * ---------------------------------- *)

let dloc   = dummy_location
let type0  = Sort (dloc, Stype (SortLevel SLz))
let dltype = type0

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
(* FIXME: This is the *lexp context*.  *)
type lexp_context = env_elem M.myers

type db_idx  = int (* DeBruijn index.  *)
type db_ridx = int (* DeBruijn reverse index (i.e. counting from the root).  *)

(*  Map matching variable name and its distance in the current scope *)
type scope = db_ridx StringMap.t  (*  Map<String, db_ridx>*)

type senv_length = int  (* it is not the map true length *)
type senv_type = senv_length * scope

(* This is the *elaboration context* (i.e. a context that holds
 * a lexp context plus some side info.  *)
type elab_context = senv_type * lexp_context * property_env

(* Extract the lexp context from the context used during elaboration.  *)
let ectx_to_lctx (ectx : elab_context) : lexp_context =
  let (_, lctx, _) = ectx in lctx

(*  internal definitions
 * ---------------------------------- *)

let _make_scope = StringMap.empty
let _make_senv_type = (0, _make_scope)
let _make_myers = M.nil
let _get_env(ctx: elab_context): lexp_context = let (_, ev, _) = ctx in ev

(*  Public methods: DO USE
 * ---------------------------------- *)

let make_elab_context = (_make_senv_type, _make_myers, PropertyMap.empty)

let get_roffset ctx = let (_, _, (_, rof)) = ctx in rof

let get_size ctx = let ((n, _), _, _) = ctx in n

(*  return its current DeBruijn index *)
let rec senv_lookup (name: string) (ctx: elab_context): int =
    let ((n, map), _, _) = ctx in
    let raw_idx =  n - (StringMap.find name map) - 1 in (*
        if raw_idx > (n - csize) then
            raw_idx - rof   (* Shift if the variable is not bound *)
        else *)
        raw_idx

let lexp_ctx_cons (ctx : lexp_context) offset d v t =
  assert (offset >= 0 &&
            (ctx = M.nil ||
               let (previous_offset, _, _, _) = M.car ctx in
               previous_offset >= 0 && previous_offset <= 1 + offset));
  M.cons (offset, d, v, t) ctx

let lctx_extend (ctx : lexp_context) (def: vdef) (v: varbind) (t: lexp) =
  lexp_ctx_cons ctx 0 (Some def) v t


let env_extend_rec r (ctx: elab_context) (def: vdef) (v: varbind) (t: lexp) =
  let (loc, name) = def in
  let ((n, map), env, f) = ctx in
  (try let _ = senv_lookup name ctx in
       debruijn_warning loc ("Variable Shadowing " ^ name);
   with Not_found -> ());
  let nmap = StringMap.add name n map in
  ((n + 1, nmap),
   lexp_ctx_cons env r (Some def) v t,
   f)

let env_extend (ctx: elab_context) (def: vdef) (v: varbind) (t: lexp) = env_extend_rec 0 ctx def v t

let lctx_extend_rec (ctx : lexp_context) (defs: (vdef * lexp * ltype) list) =
  let (ctx, _) =
    List.fold_left
      (fun (ctx, recursion_offset) (def, e, t) ->
        lexp_ctx_cons ctx recursion_offset (Some def) (LetDef e) t,
        recursion_offset - 1)
      (ctx, List.length defs) defs in
  ctx

let ectx_extend_rec (ctx: elab_context) (defs: (vdef * lexp * ltype) list) =
  (* FIXME: Use lctx_extend_rec!  *)
  List.fold_left
    (fun (ctx, recursion_offset) (def, e, t) ->
      let (loc, name) = def in
      let ((n, map), env, f) = ctx in
      (try let _ = senv_lookup name ctx in
           debruijn_warning loc ("Variable Shadowing " ^ name);
       with Not_found -> ());
      let nmap = StringMap.add name n map in
      ((n + 1, nmap),
       lexp_ctx_cons env recursion_offset (Some def) (LetDef e) t,
       f),
      recursion_offset - 1)
    (ctx, List.length defs) defs

let env_lookup_by_index index (ctx: elab_context): env_elem =
    (Myers.nth index (_get_env ctx))

(*  Print context  *)
let print_lexp_ctx (ctx : elab_context) =
    let ((n, map), env, f) = ctx in

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('l', 10), "NAME");
        (Some ('l',  7), "INDEX");
        (Some ('l', 10), "NAME");
        (Some ('l',  4), "OFF");
        (Some ('l', 29), "VALUE:TYPE")];

    print_string (make_sep '-');

    (* it is annoying to print according to StringMap order *)
    (* let's use myers list order *)
    let rec extract_names (lst: lexp_context) acc =
        match lst with
            | M.Mnil -> acc
            | M.Mcons (hd, tl, _, _) ->
                let name = match hd with
                  | (_, Some (_, name), _, _) -> name
                  | _ -> "" in
                    extract_names tl (name::acc) in

    let ord = extract_names env [] in

    let rec _print idx ord =
        match ord with
            | [] -> ()
            | hd::tl ->(
        let idx2 = StringMap.find hd map in

        (if idx2 != idx then ());

        print_string "    | ";  lalign_print_string hd 10;
        print_string    " | ";  lalign_print_int (n - idx - 1) 7;
        print_string    " | ";

        let ptr_str = "" in (*"    |            |         |            | " in *)

        try let r, name, exp, tp =
              match env_lookup_by_index (n - idx - 1) ctx with
                | (r, Some (_, name), LetDef exp, tp) -> r, name, Some exp, tp
                | _ -> 0, "", None, dltype in

            (*  Print env Info *)
            lalign_print_string name 10; (*   name must match *)
            print_string " | ";
             lalign_print_int r 4;
            print_string " | ";

            let _ = (match exp with
                | None -> print_string "<var>"
                | Some exp -> lexp_print exp)
                    (* let str = _lexp_to_str (!debug_ppctx) exp in
                    let str = (match str_split str '\n' with
                        | hd::tl -> print_string (hd ^ "\n"); tl
                        | _ -> []) in

                        List.iter (fun elem ->
                            print_string (ptr_str ^ elem ^ "\n")) str) *)in

            print_string (ptr_str ^ ": "); lexp_print tp; print_string "\n";

            _print (idx + 1) tl

        with Not_found ->
            (print_string "Not_found  |\n"; _print (idx + 1) tl)) in

    _print 0 ord; print_string (make_sep '=')


let _name_error loc estr str ctx =
    if estr = str then () else (
     print_lexp_ctx ctx;
    debruijn_error loc ("DeBruijn index refers to wrong name. " ^
                      "Expected: \"" ^ estr ^ "\" got \"" ^ str ^ "\""))


(* generic lookup *)
let _env_lookup ctx (v: vref): env_elem  =
    let ((dv_size, _), info_env, _) = ctx in
    let ((loc, ename), dbi) = v in

    try(let ret = (Myers.nth dbi info_env) in
        let _ = match ret with
          | (_, Some (_, name), _, _) ->
              (* Check if names match *)
              _name_error loc ename name ctx;
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
  | _ -> None

(* replace an expression by another *)
(* Most of the time it should be O(1) but it can be O(n)  *)
let replace_by ctx name by =
  let (a, env, b) = ctx in
  let idx = senv_lookup name ctx in
  (* lookup and replace *)
  let rec replace_by' ctx by acc =
    match ctx with
      | M.Mnil -> debruijn_error dummy_location
            ("Replace error. This expression does not exist: " ^  name)
      | M.Mcons((_, None, _, _) as elem, tl1, i, tl2) ->
          (* Skip some elements if possible *)
          if idx <= i then replace_by' tl1 by (elem::acc)
          else replace_by' tl2 by (elem::acc)
            (* replace_by' tl1 by (elem::acc) *)

      | M.Mcons((_, Some (b, n), _, _) as elem, tl1, i, tl2) ->
        if n = name then
          (M.cons by tl1), acc
        else
          (* Skip some elements if possible *)
          if idx <= i then replace_by' tl1 by (elem::acc)
          else replace_by' tl2 by (elem::acc)
            (* replace_by' tl1 by (elem::acc) *) in

  let nenv, decls = replace_by' env by [] in
  (* add old declarations *)
  let nenv = List.fold_left (fun ctx elem -> M.cons elem ctx) nenv decls in
    (a, nenv, b)

(* -------------------------------------------------------------------------- *)
(*          PropertyMap                                                       *)
(* -------------------------------------------------------------------------- *)


let add_property ctx (var_i, var_n) (att_i, att_n) (prop: lexp)
    : elab_context =

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


