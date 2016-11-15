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

let error l m = msg_error "DEBRUIJN" l m; internal_error m
let warning = msg_warning "DEBRUIJN"

(* Handling scoping/bindings is always tricky.  So it's always important
 * to keep in mind for *every* expression which is its context.
 *
 * In particular, this holds true as well for those expressions that appear
 * in the context.  Traditionally for dependently typed languages we expect
 * the context's rules to say something like:
 *
 *      ⊢ Γ    Γ ⊢ τ:Type
 *      —————————————————
 *          ⊢ Γ,x:τ
 *
 * Which means that we expect (τ) expressions in the context to be typed
 * within the *rest* of that context.
 *
 * This also means that when we look up a binding in the context, we need to
 * adjust the result, since we need to use it in the context where we looked
 * it up, which is different from the context where it was defined.
 *
 * More concretely, this means that lookup(Γ, i) should return an expression
 * where debruijn indices have been shifted by "i".
 *
 * This is nice for "normal bindings", but there's a complication in the
 * case of recursive definitions.  Typically, this is handled by using
 * something like a μx.e construct, which works OK for the theory but tends
 * to become rather inconvenient in practice for mutually recursive
 * definitions.  So instead, we annotate the recursive binding with
 * a "recursion_offset" (of type `db_offset`) to say that rather than being
 * defined in "the rest of the context", they're defined in a slightly larger
 * context that includes "younger" bindings.
 *)


(*  Type definitions
 * ---------------------------------- *)

let dloc   = dummy_location
let level0 = mkSortLevel SLz
let type0  = mkSort (dloc, Stype level0)
let dltype = type0

type property_key = (int * string)  (* rev_dbi * Var name *)
module PropertyMap
    = Map.Make (struct type t = property_key let compare = compare end)

(* (* rev_dbi * Var name *) => (name * lexp) *)
type property_elem = lexp PropertyMap.t
type property_env = property_elem PropertyMap.t

(* easier to debug with type annotations *)
type env_elem = (db_offset * vdef option * varbind * ltype)
type lexp_context = env_elem M.myers

type db_ridx = int (* DeBruijn reverse index (i.e. counting from the root).  *)

(*  Map matching variable name and its distance in the current scope *)
type scope = db_ridx SMap.t  (*  Map<String, db_ridx>*)

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

let _make_scope = SMap.empty
let _make_senv_type = (0, _make_scope)
let _make_myers = M.nil

(*  Public methods: DO USE
 * ---------------------------------- *)

let make_elab_context = (_make_senv_type, _make_myers, PropertyMap.empty)

let get_roffset ctx = let (_, _, (_, rof)) = ctx in rof

let get_size ctx = let ((n, _), _, _) = ctx in n

(*  return its current DeBruijn index *)
let rec senv_lookup (name: string) (ctx: elab_context): int =
    let ((n, map), _, _) = ctx in
    let raw_idx =  n - (SMap.find name map) - 1 in (*
        if raw_idx > (n - csize) then
            raw_idx - rof   (* Shift if the variable is not bound *)
        else *)
        raw_idx

let lexp_ctx_cons (ctx : lexp_context) offset d v t =
  assert (offset >= 0
          && (ctx = M.nil
             || let (previous_offset, _, _, _) = M.car ctx in
               previous_offset >= 0 (* General constraint.  *)
               (* Either `ctx` is self-standing (doesn't depend on us),
                * or it depends on us (and maybe other bindings to come), in
                * which case we have to depend on the exact same bindings.  *)
               && (previous_offset <= 1
                  || previous_offset = 1 + offset)));
  M.cons (offset, d, v, t) ctx

let lctx_extend (ctx : lexp_context) (def: vdef option) (v: varbind) (t: lexp) =
  lexp_ctx_cons ctx 0 def v t

let env_extend_rec r (ctx: elab_context) (def: vdef) (v: varbind) (t: lexp) =
  let (loc, name) = def in
  let ((n, map), env, f) = ctx in
  (try let _ = senv_lookup name ctx in
       warning loc ("Variable Shadowing " ^ name);
   with Not_found -> ());
  let nmap = SMap.add name n map in
  ((n + 1, nmap),
   lexp_ctx_cons env r (Some def) v t,
   f)

let env_extend (ctx: elab_context) (def: vdef) (v: varbind) (t: lexp) = env_extend_rec 0 ctx def v t

let ectx_extend (ectx: elab_context) (def: vdef option) (v: varbind) (t: lexp)
    : elab_context =
  match def with
  | None -> let ((n, map), lctx, f) = ectx in
           ((n + 1, map), lexp_ctx_cons lctx 0 None v t, f)
  | Some def -> env_extend ectx def v t

let lctx_extend_rec (ctx : lexp_context) (defs: (vdef * lexp * ltype) list) =
  let (ctx, _) =
    List.fold_left
      (fun (ctx, recursion_offset) (def, e, t) ->
        lexp_ctx_cons ctx recursion_offset (Some def) (LetDef e) t,
        recursion_offset - 1)
      (ctx, List.length defs) defs in
  ctx

let ectx_extend_rec (ctx: elab_context) (defs: (vdef * lexp * ltype) list) =
  let ((n, senv), lctx, f) = ctx in
  let senv', _ = List.fold_left
                   (fun (senv, i) ((_, vname), _, _) ->
                     SMap.add vname i senv, i + 1)
                   (senv, n) defs in
  ((n + List.length defs, senv'), lctx_extend_rec lctx defs, f)

let env_lookup_by_index index (ctx: lexp_context): env_elem =
  Myers.nth index ctx

(*  Print context  *)
let print_lexp_ctx_n (ctx : lexp_context) start =
    let n = (M.length ctx) - 1 in

    print_string (make_title " LEXP CONTEXT ");

    make_rheader [
        (Some ('l',  7), "INDEX");
        (Some ('l',  4), "OFF");
        (Some ('l', 10), "NAME");
        (Some ('l', 42), "VALUE:TYPE")];

    print_string (make_sep '-');

    (* it is annoying to print according to SMap order *)
    (* let's use myers list order *)
    let rec extract_names (lst: lexp_context) acc =
        let names = ref [] in
        for i = start to n do
          let name = match (M.nth (n - i) lst) with
            | (_, Some (_, name), _, _) -> name
            | _ -> "" in
              names := name::!names
        done; !names in

    let ord = extract_names ctx [] in

    let rec _print idx ord =
        match ord with
            | [] -> ()
            | hd::tl ->(

        print_string "    | ";  lalign_print_int (n - idx - 1) 7;
        print_string    " | ";

        let ptr_str = "    |         |      |            | " in

        try let r, name, exp, tp =
              match env_lookup_by_index (n - idx - 1) ctx with
                | (r, Some (_, name), LetDef exp, tp) -> r, name, Some exp, tp
                | (r, Some (_, name), _, tp) -> r, name, None, tp
                | (r, _, _, tp) -> r, "", None, tp in

            (*  Print env Info *)
            lalign_print_int r 4;
            print_string " | ";
            lalign_print_string name 10; (*   name must match *)
            print_string " | ";

            let _ = match exp with
                | None -> print_string "<var>"
                | Some exp -> (
                  let str = _lexp_to_str (!debug_ppctx) exp in
                    let str = (match str_split str '\n' with
                        | hd::tl -> print_string hd; tl
                        | _ -> []) in

                      List.iter (fun elem ->
                        print_string ("\n" ^ ptr_str ^ elem)) str) in

            print_string (": "); lexp_print tp; print_string "\n";

            _print (idx + 1) tl

        with Not_found ->
            (print_string "Not_found  |\n"; _print (idx + 1) tl)) in

    _print (start - 1) ord; print_string (make_sep '=')


(* Only print user defined variables *)
let print_lexp_ctx (ctx : lexp_context) =
  print_lexp_ctx_n ctx !L.builtin_size

(* Dump the whole context *)
let dump_lexp_ctx (ctx : lexp_context) =
  print_lexp_ctx_n ctx 0

(* generic lookup *)
let lctx_lookup (ctx : lexp_context) (v: vref): env_elem  =
    let ((loc, ename), dbi) = v in

    try(let ret = (Myers.nth dbi ctx) in
        let _ = match ret with
          | (_, Some (_, name), _, _) ->
             (* Check if names match *)
               if not (ename = name) then
                 (print_lexp_ctx ctx;
                  error loc ("DeBruijn index "
                                      ^ string_of_int dbi
                                      ^ " refers to wrong name.  "
                                      ^ "Expected: `" ^ ename
                                      ^ "` got `" ^ name ^ "`"))
          | _ -> () in

        ret)
    with
      Not_found -> error loc ("DeBruijn index "
                                      ^ string_of_int dbi ^ " out of bounds!")



let lctx_lookup_type (ctx : lexp_context) (vref : vref) : lexp =
  let (_, i) = vref in
  let (_, _, _, t) = lctx_lookup ctx vref in
  mkSusp t (S.shift (i + 1))

let lctx_lookup_value (ctx : lexp_context) (vref : vref) : lexp option =
  let (_, i) = vref in
  match lctx_lookup ctx vref with
  | (o, _, LetDef v, _) -> Some (push_susp v (S.shift (i + 1 - o)))
  | _ -> None

let env_lookup_type ctx (v : vref): lexp =
  lctx_lookup_type (ectx_to_lctx ctx) v

    (* mkSusp ltp (S.shift (idx + 1)) *)

let env_lookup_expr ctx (v : vref): lexp option =
  lctx_lookup_value (ectx_to_lctx ctx) v

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
      error dummy_location ("Variable \"" ^ var_n ^ "\" does not have any properties") in

  let prop = try PropertyMap.find (n - att_i, att_n) pmap
    with Not_found ->
      error dummy_location ("Property \"" ^ att_n ^ "\" not found") in
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


