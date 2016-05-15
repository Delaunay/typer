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

open Debruijn
open Env       (* get_rte_variable *)


let builtin_error loc msg =
    msg_error "BUILT-IN" loc msg;
    raise (internal_error msg)

type predef_table = (lexp option ref) SMap.t

let predef_name = [
    "cons";
    "nil"
]

let predef_map : predef_table =
    (* add predef name, expr will be populated when parsing *)
    List.fold_left (fun m name ->
        SMap.add name (ref None) m) SMap.empty predef_name

let get_predef name =
    match !(SMap.find name predef_map) with
        | Some exp -> exp
        | None -> builtin_error dloc "Try to access an empty predefined"

let set_predef name lexp =
    SMap.find name predef_map := lexp

(*                Builtin types               *)
let dloc    = dummy_location
let slevel0 = SortLevel (SLn 0)
let slevel1 = SortLevel (SLn 1)
let type0   = Sort (dloc, Stype slevel0)
let type1      = Sort (dloc, Stype slevel1)
let type_omega = Sort (dloc, StypeOmega)
let type_level = Sort (dloc, StypeLevel)
let type_level = Builtin ((dloc, "TypeLevel"), type_level)

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

let type_int = Builtin((dloc, "Int"), type0)
let type_float = Builtin((dloc, "Float"), type0)
let type_string = Builtin((dloc, "String"), type0)

(* Builtin of builtin * string * ltype *)
let _generic_binary_iop name f loc (args_val: value_type list)
                                                    (ctx: runtime_env) =

   let l, r = match args_val with
        | [l; r] -> l, r
        | _ -> builtin_error loc (name ^ " expects 2 Integers arguments") in

        match l, r with
            | Vint(v), Vint(w) -> Vint(f v w)
            | _ ->
                value_print l; print_string " "; value_print r;
                builtin_error loc (name ^ " expects Integers as arguments")

let iadd_impl  = _generic_binary_iop "Integer::add"  (fun a b -> a + b)
let isub_impl  = _generic_binary_iop "Integer::sub"  (fun a b -> a - b)
let imult_impl = _generic_binary_iop "Integer::mult" (fun a b -> a * b)
let idiv_impl  = _generic_binary_iop "Integer::div"  (fun a b -> a / b)


(* loc is given by the compiler *)
let none_fun : (location -> value_type list -> runtime_env -> value_type)
    = (fun loc args_val ctx ->
    builtin_error loc "Requested Built-in was not implemented")

let make_symbol loc args_val ctx  =
    (* symbol is a simple string *)
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("symbol_ expects 1 argument") in

        match lxp with
            | Vstring(str) -> Vsexp(Symbol(loc, str))
            | _ -> builtin_error loc ("symbol_ expects one string as argument")


(* lexp Imm list *)
let olist2tlist_lexp lst ctx =
    (* Get Constructor *)
    let considx = senv_lookup "cons" ctx in
    let nilidx  = senv_lookup  "nil" ctx in

    let tcons = Var((dloc, "cons"), considx) in
    let tnil  = Var((dloc,  "nil"),  nilidx) in

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
        | Vcons((_, "cons"), [hd; tl]) ->
            tlist2olist (hd::acc) tl
        | Vcons((_, "nil"), []) -> List.rev acc
        | _ ->
            value_print expr;
            builtin_error dloc "List conversion failure'"

let make_node loc args_val ctx    =

    let op, tlist = match args_val with
        | [Vsexp(op); lst] -> op, lst
        | _ -> builtin_error loc
            "node_ expects one 'Sexp' and one 'List Sexp'" in

    let args = tlist2olist [] tlist in

    let s = List.map (fun g -> match g with
        | Vsexp(sxp)  -> sxp
        (* eval transform sexp into those... *)
        | Vint (i)    -> Integer(dloc, i)
        | Vstring (s) -> String(dloc, s)
        | _ -> value_print g;
            builtin_error loc ("node_ expects sexp as arguments")) args in

        Vsexp(Node(op, s))

let make_string loc args_val ctx  =
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("string_ expects 1 argument") in

        match lxp with
            | Vstring(str) -> Vsexp(String(loc, str))
            | _ -> builtin_error loc ("string_ expects one string as argument")

let make_integer loc args_val ctx =
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("integer_ expects 1 argument") in

        match lxp with
            | Vint(str) -> Vsexp(Integer(loc, str))
            | _ -> builtin_error loc ("integer_ expects one string as argument")

let make_float loc args_val ctx   = Vdummy
let make_block loc args_val ctx   = Vdummy

let ttrue = Vcons((dloc, "True"), [])
let tfalse = Vcons((dloc, "False"), [])
let btyper b = if b then ttrue else tfalse

let string_eq loc args_val ctx =
    match args_val with
        | [Vstring(s1); Vstring(s2)] -> btyper (s1 = s2)
        | _ -> builtin_error loc "string_eq expects 2 strings"

let int_eq loc args_val ctx =
    match args_val with
        | [Vint(s1); Vint(s2)] -> btyper (s1 = s2)
        | _ -> builtin_error loc "int_eq expects 2 integer"

let sexp_eq loc args_val ctx =
    match args_val with
        | [Vsexp(s1); Vsexp(s2)] -> (
            match s1, s2 with
                | Symbol(_, s1), Symbol(_, s2)   -> btyper (s1 = s2)
                | String(_, s1), String(_, s2)   -> btyper (s1 = s2)
                | Integer(_, s1), Integer(_, s2) -> btyper (s1 = s2)
                | Float(_, s1), Float(_, s2)     -> btyper (s1 = s2)
                | _ -> tfalse)
        | _ -> builtin_error loc "int_eq expects 2 sexp"

(*
 *  Should we have a function that
 *      -> returns a new context inside typer ? (So we need to add a ctx type too)
 *      -> returns current context ?
 *      -> pexp_eval expr
 *      -> lexp_eval expr
 *      -> ou seulement: 'eval expr ctx'
 *)





let is_lbuiltin idx ctx =
    let bsize = 1 in
    let csize = get_size ctx in

    if idx >= csize - bsize then
        true
    else
        false
