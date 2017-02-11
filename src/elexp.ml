(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2017  Free Software Foundation, Inc.
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
 *          Type Erased Lexp expression
 *
 * --------------------------------------------------------------------------- *)


open Sexp (* Sexp type *)
open Pexp (* Aexplicit *)

module U = Util

type vname = U.vname
type vref = U.vref
type label = symbol

module SMap = U.SMap

type elexp =
    | Imm of sexp

    | Builtin of vname
    | Var of vref

    | Let of U.location * (vname * elexp) list * elexp
    | Lambda of vname * elexp
    | Call of elexp * elexp list
    | Cons of symbol
    | Case of U.location * elexp
              * (U.location * (vname option) list * elexp) SMap.t
              * (vname option * elexp) option
    (* Type place-holder just in case *)
    | Type
    (* Inductive takes a slot in the env that is why it need to be here *)
    | Inductive of U.location * label

let rec elexp_location e =
    match e with
        | Imm s -> sexp_location s
        | Var ((l,_), _) -> l
        | Builtin ((l, _)) -> l
        | Let (l,_,_) -> l
        | Lambda ((l,_),_) -> l
        | Call (f,_) -> elexp_location f
        | Cons ((l,_)) -> l
        | Case (l,_,_,_) -> l
        | Inductive(l, _) -> l
        | Type -> U.dummy_location


let elexp_name e =
  match e with
    | Imm  _ -> "Imm"
    | Var  _ -> "Var"
    | Let  _ -> "Let"
    | Call _ -> "Call"
    | Cons _ -> "Cons"
    | Case _ -> "Case"
    | Type   -> "Type"
    | Lambda    _ -> "Lambda"
    | Builtin   _ -> "Builtin"
    | Inductive _ -> "Inductive"

let rec elexp_print lxp = print_string (elexp_string lxp)
and elexp_string lxp =
    let maybe_str lxp =
        match lxp with
        | Some (v, lxp)
          -> " | " ^ (match v with None -> "_" | Some (_,name) -> name)
            ^ " => " ^ elexp_string lxp
        | None -> "" in

    let str_decls d =
        List.fold_left (fun str ((_, s), lxp) ->
            str ^ " " ^ s ^ " = " ^ (elexp_string lxp)) "" d in

    let str_pat lst =
        List.fold_left (fun str v ->
            str ^ " " ^ (match v with
                | None -> "_"
                | Some (_, s) -> s)) "" lst in

    let str_cases c =
        SMap.fold (fun key (_, lst, lxp) str ->
            str ^ " | " ^ key ^ " " ^ (str_pat lst) ^ " => " ^ (elexp_string lxp))
                c "" in

    let str_args lst =
        List.fold_left (fun str lxp ->
            str ^ " " ^ (elexp_string lxp)) "" lst in

    match lxp with
        | Imm(s)          -> sexp_string s
        | Builtin((_, s)) -> s
        | Var((_, s), i)  -> s ^ "[" ^ string_of_int i ^ "]"
        | Cons((_, s))    -> s

        | Lambda((_, s), b)  -> "lambda " ^ s ^ " -> " ^ (elexp_string b)

        | Let(_, d, b)    ->
            "let" ^ (str_decls d) ^ " in " ^ (elexp_string b)

        | Call(fct, args) ->
            "(" ^ (elexp_string fct) ^ (str_args args) ^ ")"

        | Case(_, t, cases, default) ->
            "case " ^ (elexp_string t) ^ (str_cases cases) ^ (maybe_str default)

        | Inductive(_, (_, s)) ->
            "typecons " ^ s

        | Type -> "Type "
