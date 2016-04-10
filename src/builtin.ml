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


(*                Builtin types               *)
let dloc = dummy_location
let slevel0 = SortLevel (SLn 0)
let slevel1 = SortLevel (SLn 1)
let type0 = Sort (dloc, Stype slevel0)
let type1 = Sort (dloc, Stype slevel1)
let type_omega = Sort (dloc, StypeOmega)
let type_level = Sort (dloc, StypeLevel)
let type_level = Builtin (LevelType, "TypeLevel", type_level)


let type_int = Builtin (IntType, "Int", type0)
let type_float = Builtin (FloatType, "Float", type0)

let op_binary t =  Arrow (Aexplicit, None, t, dloc,
                        Arrow (Aexplicit, None, t, dloc, t))

let iop_binary = op_binary type_int
let fop_binary = op_binary type_float
let type_eq = let lv = (dloc, "l") in
   let tv = (dloc, "t") in
   Arrow (Aerasable, Some lv, type_level, dloc,
          Arrow (Aerasable, Some tv,
                 Sort (dloc, Stype (Var (lv, 0))), dloc,
                 Arrow (Aexplicit, None, Var (tv, 0), dloc,
                        Arrow (Aexplicit, None, Var (tv, 1), dloc,
                               type0))))

let builtin_iadd = Builtin (IAdd, "_+_", iop_binary)
let builtin_imult = Builtin (IMult, "_*_", iop_binary)
let builtin_eq = Builtin (EqType, "_=_", type_eq) (*
let builtin_fadd = Builtin (FAdd, "_+_", fop_binary)
let builtin_fmult = Builtin (FMult, "_*_", fop_binary) *)

(*      Math Functions       *)
let get_int lxp =
    match lxp with
        | Imm(Integer(_, l)) -> Some l
        | _ -> None
;;

let get_float lxp =
    match lxp with
        | Imm(Float(_, l)) -> Some l
        | _ -> None
;;

let iadd_impl ctx =
    let llxp = (get_rte_variable (None) 0 ctx) in
    let rlxp = (get_rte_variable (None) 1 ctx) in
    let l = get_int llxp in
    let r = get_int rlxp in

    (* if l and r are not ints this is a partial eval *)
    if l = None || r = None then
        Call(builtin_iadd, [(Aexplicit, llxp); (Aexplicit, rlxp)])
    else (
        let v, w = match l, r with
            | Some v, Some w -> v, w
            | _, _ -> (-40), (-40) in
        Imm(Integer (dloc, v + w)))

let imult_impl ctx =

    let vint = (nfirst_rte_var 2 ctx) in
    let varg = List.map (fun g -> get_int g) vint in

    (* check for partial eval and compute product *)
    let (partial, prod) = List.fold_left (fun a g ->
        let (partial, prod) = a in
            match g with
                | Some v  -> (partial, v * prod)
                | None -> (true, 1))
        (false, 1) varg in

    (* we could partially eval partial call         *)
    (* i.e (a * 2 * 2 * b * 4) => (a * b * 16)      *)
    (* but we don't here                            *)

    if partial then
        let args = List.map (fun g -> (Aexplicit, g)) vint in
            Call(builtin_imult, args)
    else
        Imm(Integer(dloc, prod))

let none_fun = (fun ctx -> type_int)

(* Built-in list of types/functions *)
let typer_builtins = [
(*    NAME  | LXP  | Type       | impl      *)
    ("Int"  , None, type_int,    none_fun);
    ("Float", None, type_float,  none_fun);
    ("Type" , None, type0,       none_fun);   (* builtin_iadd *)
    ("_=_"  , Some builtin_eq, type_eq,     none_fun);   (*  t  ->  t  -> bool *)
    ("_+_"  , Some builtin_iadd, iop_binary,  iadd_impl);  (* int -> int -> int  *)
    ("_*_"  , Some builtin_imult, iop_binary,  imult_impl); (* int -> int -> int  *)

(*  Macro primitives *)

]

(* Make lxp context with built-in types *)
let default_lctx () =
    (* Empty context *)
    let lctx = make_lexp_context in

    (* populate ctx *)
    List.fold_left
      (fun ctx (name, lxp, ltp, _) ->
        env_extend ctx (dloc, name) lxp ltp)
      lctx
      typer_builtins
;;

(* Make runtime context with built-in types *)
let default_rctx () =
    (* Empty context *)
    let rctx = make_runtime_ctx in

    (* populate ctx *)
    List.fold_left
      (fun ctx (name, lxp, ltp, f) ->
        add_rte_variable (Some name) ltp ctx)
       rctx
       typer_builtins
;;

let is_lbuiltin idx ctx =
    let bsize = List.length typer_builtins in
    let csize = get_size ctx in

    if idx >= csize - bsize then
        true
    else
        false
