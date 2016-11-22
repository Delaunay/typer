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
 *          Hold built-in types definition and built-in functions implementation
 *
 * ---------------------------------------------------------------------------*)

open Util

open Sexp   (* Integer/Float *)
open Pexp   (* arg_kind *)
open Lexp

module DB = Debruijn
open Env       (* get_rte_variable *)

let error loc msg = msg_error "BUILT-IN" loc msg; raise (internal_error msg)
let warning loc msg = msg_warning "BUILT-IN" loc msg

type predef_table = (lexp option ref) SMap.t

let predef_name = [
    "cons";
    "nil";
    "Unit";
    "True";
    "False";
    "Bool";
    "Macro";
    "expand_macro_";
    "expand_dmacro_";
    "Attribute";
]

let default_predef_map : predef_table =
    (* add predef name, expr will be populated when parsing *)
    List.fold_left (fun m name ->
        SMap.add name (ref None) m) SMap.empty predef_name

let predef_map = ref default_predef_map

let get_predef_raw (name: string) : lexp =
    match !(SMap.find name (!predef_map)) with
        | Some exp -> exp
        | None -> error dloc ("\""^ name ^ "\" was not predefined")

let get_predef_option (name: string) (ctx: DB.elab_context) =
  let r = (DB.get_size ctx) - !builtin_size - 0 in
    match !(SMap.find name (!predef_map)) with
        | Some exp -> Some (mkSusp exp (S.shift r))
        | None -> None

let get_predef (name: string) (ctx: DB.elab_context) =
  let r = (DB.get_size ctx) - !builtin_size - 0 in
  let p = get_predef_raw name in
    (mkSusp p (S.shift r))

let set_predef name lexp =
    SMap.find name (!predef_map) := lexp

let dump_predef () =
  let _ = SMap.iter (fun key item ->
    print_string key; print_string " ";
    let _ = match !item with
      | Some lxp -> lexp_print lxp
      | None -> print_string "None"; in
    print_string "\n") !predef_map in ()

(*                Builtin types               *)
let dloc    = DB.dloc
let level0  = DB.level0
let level1  = mkSortLevel (SLsucc level0)
let level2  = mkSortLevel (SLsucc level1)
let type0   = DB.type0
let type1   = mkSort (dloc, Stype level1)
let type2   = mkSort (dloc, Stype level2)
let type_omega = mkSort (dloc, StypeOmega)
let type_level = mkSort (dloc, StypeLevel)

let op_binary t =  Arrow (Aexplicit, None, t, dloc,
                        Arrow (Aexplicit, None, t, dloc, t))

let type_eq = let lv = (dloc, "l") in
   let tv = (dloc, "t") in
   Arrow (Aerasable, Some lv, type_level, dloc,
          Arrow (Aerasable, Some tv,
                 Sort (dloc, Stype (Var (lv, 0))), dloc,
                 Arrow (Aexplicit, None, Var (tv, 0), dloc,
                        Arrow (Aexplicit, None, Var (tv, 1), dloc,
                               type0))))

let type_int = Builtin((dloc, "Int"), type0, None)
let type_float = Builtin((dloc, "Float"), type0, None)
let type_string = Builtin((dloc, "String"), type0, None)


(* lexp Imm list *)
let olist2tlist_lexp lst ctx =
    let tcons = get_predef "cons" ctx in
    let tnil  = get_predef "nil" ctx in

    let rlst = List.rev lst in
        List.fold_left (fun tail elem ->
            Call(tcons, [(Aexplicit, (Imm(elem)));
                         (Aexplicit, tail)])) tnil rlst

(* typer list as seen during runtime *)
let olist2tlist_rte lst =
    let tnil  = Vcons((dloc, "nil"), []) in
    let rlst = List.rev lst in
        List.fold_left (fun tail elem ->
            Vcons((dloc, "cons"), [Vsexp(elem); tail])) tnil rlst


(* Typer list to Ocaml list *)
let rec tlist2olist acc expr =
    match expr with
        | Vcons((_, "cons"), [hd; tl]) -> tlist2olist (hd::acc) tl
        | Vcons((_, "nil"), []) -> List.rev acc
        | _ ->
            print_string (value_name expr); print_string "\n";
            value_print expr;
            error dloc "List conversion failure'"

let is_lbuiltin idx ctx =
    let bsize = 1 in
    let csize = DB.get_size ctx in

    if idx >= csize - bsize then
        true
    else
        false

let declexpr_impl loc largs ctx ftype =

  let (vi, vn) = match largs with
    | [Var((_, vn), vi)] -> (vi, vn)
    | _ -> error loc "declexpr expects one argument" in

  let lxp = match DB.env_lookup_expr ctx ((loc, vn), vi) with
    | Some lxp -> lxp
    | None -> error loc "no expr available" in
  (* ltp and ftype should be the same
  let ltp = env_lookup_type ctx ((loc, vn), vi) in *)
    lxp, ftype


let decltype_impl loc largs ctx ftype =

  let (vi, vn) = match largs with
    | [Var((_, vn), vi)] -> (vi, vn)
    | _ -> error loc "decltype expects one argument" in

  let ltype = DB.env_lookup_type ctx ((loc, vn), vi) in
    (* mkSusp prop (S.shift (var_i + 1)) *)
    ltype, type0







