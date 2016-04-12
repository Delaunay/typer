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
;;


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
let get_int (lxp: value_type): (int option) =
    let lxp = get_value_lexp lxp in
    match lxp with
        | Imm(Integer(_, l)) -> Some l
        | _ -> None
;;


(* Builtin of builtin * string * ltype *)
let _generic_binary_iop name f loc args_val ctx =

    let n = List.length args_val in
    let nctx = List.fold_left (fun c v -> add_rte_variable None v c) ctx args_val in

    (if n != 2 then builtin_error loc (name ^ " expects 2 arguments"));

    let llxp = (get_rte_variable (None) 0 nctx) in
    let rlxp = (get_rte_variable (None) 1 nctx) in

    let l = get_int llxp in
    let r = get_int rlxp in

        match l, r with
            | Some v, Some w -> Value(Imm(Integer (dloc, (f v w))))
            | _ -> builtin_error loc (name ^ " expects Integers as arguments")
;;

let iadd_impl  = _generic_binary_iop "Integer::add"  (fun a b -> a + b)
let isub_impl  = _generic_binary_iop "Integer::sub"  (fun a b -> a - b)
let imult_impl = _generic_binary_iop "Integer::mult" (fun a b -> a * b)
let idiv_impl  = _generic_binary_iop "Integer::div"  (fun a b -> a / b)


let none_fun = (fun loc args_val ctx ->
    builtin_error dloc "Requested Built-in was not implemented")


let make_block loc args_val ctx   = Value(type0)
let make_symbol loc args_val ctx  = Value(type0)
let make_node sxp args_val ctx    = Value(type0)
let make_string loc args_val ctx  = Value(type0)
let make_integer loc args_val ctx = Value(type0)
let make_float loc args_val ctx   = Value(type0)

let builtin_sexp = Builtin (SexpType, "_sxp_", type0)

(* Built-in list of types/functions *)
let typer_builtins = [
(*    NAME  | LXP  | Type       | impl      *)
    ("Int"  , None, type_int,    none_fun);
    ("Float", None, type_float,  none_fun);
    ("Type" , None, type0,       none_fun);

(* Built-in Functions *)
    ("_=_"  , Some builtin_eq,    type_eq,    none_fun);   (*  t  ->  t  -> bool *)
    ("_+_"  , Some builtin_iadd,  iop_binary, iadd_impl);  (* int -> int -> int  *)
    ("_*_"  , Some builtin_imult, iop_binary, imult_impl); (* int -> int -> int  *)

(*  Macro primitives *)
    ("block_"  , Some builtin_sexp, type0, make_block);
    ("symbol_" , Some builtin_sexp, type0, make_symbol);
    ("string_" , Some builtin_sexp, type0, make_string);
    ("integer_", Some builtin_sexp, type0, make_integer);
    ("float_"  , Some builtin_sexp, type0, make_float);
    ("node_"   , Some builtin_sexp, type0, make_node);
]

(* Make built-in lookup table *)
let _builtin_lookup =
    List.fold_left (fun lkup (name, _, _, f) ->
        SMap.add name f lkup)
        SMap.empty typer_builtins


let get_builtin_impl btype str ltp =
    try SMap.find str _builtin_lookup
    with Not_found ->
        builtin_error dloc "Requested Built-in does not exist"


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
        add_rte_variable (Some name) (Value(ltp)) ctx)
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
