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

let builtin_iadd  = Builtin (IAdd, "_+_", iop_binary)
let builtin_imult = Builtin (IMult, "_*_", iop_binary)
let builtin_eq    = Builtin (EqType, "_=_", type_eq)
let builtin_sexp  = Builtin (SexpType, "sexp", type0)
(*
let builtin_fadd = Builtin (FAdd, "_+_", fop_binary)
let builtin_fmult = Builtin (FMult, "_*_", fop_binary) *)

(*      Math Functions       *)
let get_int (lxp: value_type): (int option) =
    let lxp = get_value_lexp lxp in
    match lxp with
        | Imm(Integer(_, l)) -> Some l
        | _ -> None
;;

let get_string (lxp: value_type): (string option) =
    let lxp = get_value_lexp lxp in
    match lxp with
        | Imm(String(_, l)) -> Some l
        | _ -> None
;;

let get_sexp (lxp: value_type): (sexp option) =
    match lxp with
        | Vsexp l -> Some l
        | _ -> None
;;

(* Builtin of builtin * string * ltype *)
let _generic_binary_iop name f loc (args_val: value_type list) (ctx: runtime_env) =
    (* We don't have to access context because:                   *)
    (*  x + y is parsed as Call(_+_ x y)                          *)
    (* Partial application handling aggregates arguments in a ctx *)
    (* once all arguments are present Call(_+_ x y) is called     *)
    (* First, its arguments are evaluated which is where x, y are replaced        *)
    (* by their value in the context then _generic_binary_iop handle the function *)
    (* i.e we don't need to push x and y in the context. *)
    (* We don't even need the context                    *)
    let l, r = match args_val with
        | [a; b] -> a, b
        | _ -> builtin_error loc (name ^ " expects 2 arguments") in

        match (get_int l), (get_int r) with
            | Some v, Some w -> Value(Imm(Integer (loc, (f v w))))
            | _ ->
                value_print l; print_string " "; value_print r;
                builtin_error loc (name ^ " expects Integers as arguments")
;;

let iadd_impl  = _generic_binary_iop "Integer::add"  (fun a b -> a + b)
let isub_impl  = _generic_binary_iop "Integer::sub"  (fun a b -> a - b)
let imult_impl = _generic_binary_iop "Integer::mult" (fun a b -> a * b)
let idiv_impl  = _generic_binary_iop "Integer::div"  (fun a b -> a / b)

(*
let eq_impl loc args_val ctx =
    let l, r = match args_val with
        | [a; b] -> a, b
        | _ -> builtin_error loc "_=_ expects 2 arguments") in

    conv_p l r *)

(* loc is given by the compiler *)
let none_fun = (fun loc args_val ctx ->
    builtin_error loc "Requested Built-in was not implemented")

let make_symbol loc args_val ctx  =
    (* symbol is a simple string *)
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("symbol_ expects 1 argument") in

    let s = get_string lxp in
        match s with
            | Some str -> Vsexp(Symbol(loc, str))
            | _ -> builtin_error loc ("symbol_ expects one string as argument")


let make_node loc args_val ctx    =

    let head, args = match args_val with
        | hd::tl -> (get_sexp hd), tl
        | _ -> builtin_error loc ("node_ expects at least 2 arguments") in

    let op = match head with
        | Some sxp -> sxp
        | None -> builtin_error loc ("node_ expects sexp as operator") in

    let s = List.map (fun g -> match get_sexp g with
        | Some sxp -> sxp
        | None -> builtin_error loc ("node_ expects sexp as arguments")) args in

        Vsexp(Node(op, s))


let make_block loc args_val ctx   = Value(type0)
let make_string loc args_val ctx  = Value(type0)
let make_integer loc args_val ctx = Value(type0)
let make_float loc args_val ctx   = Value(type0)

let type_string   = type0
let type_mblock   = type0

let type_msymbol  = Arrow (Aexplicit, None, type_string, dloc, builtin_sexp)
let type_mstring  = Arrow (Aexplicit, None, type_string, dloc, builtin_sexp)
let type_minteger = Arrow (Aexplicit, None, type_int,    dloc, builtin_sexp)
let type_mfloat   = Arrow (Aexplicit, None, type_float,  dloc, builtin_sexp)
let type_mnode    = Arrow (Aexplicit, None, builtin_sexp,dloc, builtin_sexp)
let type_mexpand  = Arrow (Aexplicit, None, builtin_sexp,dloc, type0)

let builtin_block   = Builtin (SexpType, "block_", type_mblock)
let builtin_symbol  = Builtin (SexpType, "symbol_", type_msymbol)
let builtin_string  = Builtin (SexpType, "string_", type_mstring)
let builtin_integer = Builtin (SexpType, "integer_", type_minteger)
let builtin_float   = Builtin (SexpType, "float_", type_mfloat)
let builtin_node    = Builtin (SexpType, "node_", type_mnode)
let builtin_expand  = Builtin (SexpType, "expand_", type_mexpand)

(*
 *  Should we have a function that
 *      -> returns a new context inside typer ? (So we need to add a ctx type too)
 *      -> returns current context ?
 *      -> pexp_eval expr
 *      -> lexp_eval expr
 *      -> ou seulement: 'eval expr ctx'
 *)

(* Built-in list of types/functions *)
(* Some of the information is redundant but it suppress a lot of warnings *)
let typer_builtins = [
(*    NAME   | LXP        | Type | impl      *)
    ("Type"  , type0      , type0, none_fun);
    ("Int"   , type_int   , type0, none_fun);
    ("Float" , type_float , type0, none_fun);
    ("String", type_string, type0, none_fun);

(* Built-in Functions *)
    ("_=_"  , builtin_eq,    type_eq,    none_fun);   (*  t  ->  t  -> bool *)
    ("_+_"  , builtin_iadd,  iop_binary, iadd_impl);  (* int -> int -> int  *)
    ("_*_"  , builtin_imult, iop_binary, imult_impl); (* int -> int -> int  *)

(*  Macro primitives *)
    ("block_"  , builtin_block  , type_mblock  , make_block);
    ("symbol_" , builtin_symbol , type_msymbol , make_symbol);
    ("string_" , builtin_string , type_mstring , make_string);
    ("integer_", builtin_integer, type_minteger, make_integer);
    ("float_"  , builtin_float  , type_mfloat  , make_float);
    ("node_"   , builtin_node   , type_mnode   , make_node);
    ("expand_" , builtin_expand , type_mexpand , none_fun);

(* Macros primitives type ? *)


]

(* Make built-in lookup table *)
let _builtin_lookup =
    List.fold_left (fun lkup (name, _, _, f) ->
        SMap.add name f lkup)
        SMap.empty typer_builtins


let get_builtin_impl btype str ltp loc =
    try SMap.find str _builtin_lookup
    with Not_found ->
        builtin_error loc "Requested Built-in does not exist"

(* Make lxp context with built-in types *)
let default_lctx () =
    (* Empty context *)
    let lctx = make_lexp_context in

    (* populate ctx *)
    List.fold_left
      (fun ctx (name, lxp, ltp, _) ->
        env_extend ctx (dloc, name) (Some lxp) ltp)
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
        add_rte_variable (Some name) (Value(lxp)) ctx)
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
