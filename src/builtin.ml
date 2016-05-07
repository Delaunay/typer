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

(*
let builtin_fadd = Builtin (FAdd, "_+_", fop_binary)
let builtin_fmult = Builtin (FMult, "_*_", fop_binary) *)


(* Builtin of builtin * string * ltype *)
let _generic_binary_iop name f loc (args_val: value_type list) (ctx: runtime_env) =

   let l, r = match args_val with
        | [l; r] -> l, r
        | _ -> builtin_error loc (name ^ " expects 2 Integers arguments") in

        match l, r with
            | Vint(v), Vint(w) -> Vint(f v w)
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

        match lxp with
            | Vstring(str) -> Vsexp(Symbol(loc, str))
            | _ -> builtin_error loc ("symbol_ expects one string as argument")


let make_node loc args_val ctx    =

    let op, args = match args_val with
        | Vsexp(s)::tl -> s, tl
        | _::tl -> builtin_error loc ("node_ expects sexp as operator")
        | _ -> builtin_error loc ("node_ expects at least 2 arguments") in

    let s = List.map (fun g -> match g with
        | Vsexp(sxp) -> sxp
        | _ -> builtin_error loc ("node_ expects sexp as arguments")) args in

        Vsexp(Node(op, s))

(* Takes one sexp and 6 function returning a sexp                       *)
(* Sexp -> (Sexp -> Sexp) -> (Sexp -> Sexp) -> (Sexp -> Sexp)
        -> (Sexp -> Sexp) -> (Sexp -> Sexp) -> (Sexp -> Sexp)
        -> (Sexp -> Sexp)                                               *)
let sexp_dispatch loc args ctx =

    let sxp, nd, sym, str, it, flt, blk = match args with
        | [Vsexp(sxp), nd, sym, str, it, flt, blk] ->
            sxp, nd, sym, str, it, flt, blk
        | _ -> builtin_error loc "sexp_dispatch expects 5 arguments" in

    match sxp with
        | Node _    -> nd
        | Symbol _  -> sym
        | String _  -> str
        | Integer _ -> it
        | Float _   -> flt
        | Block _   -> blk
        | _ -> builtin_error loc "sexp_dispatch error"


(* We need those ro build internal type *)
let type_int      = Builtin((dloc, "Int")   , type0)
let type_float    = Builtin((dloc, "Float") , type0)
let type_sexp     = Builtin((dloc, "Sexp")  , type0)
let type_string   = Builtin((dloc, "String"), type0)
let type_macro    = Builtin((dloc, "Macro") , type0)
let iop_binary    = op_binary type_int

let make_block loc args_val ctx   = Vdummy
let make_string loc args_val ctx  = Vdummy
let make_integer loc args_val ctx = Vdummy
let make_float loc args_val ctx   = Vdummy

let type_msymbol  = Arrow (Aexplicit, None, type_string, dloc, type_sexp)
let type_mstring  = Arrow (Aexplicit, None, type_string, dloc, type_sexp)
let type_minteger = Arrow (Aexplicit, None, type_int   , dloc, type_sexp)
let type_mnode    = Arrow (Aexplicit, None, type_sexp  , dloc, type_sexp)
let type_mblock   = Arrow (Aexplicit, None, type_sexp  , dloc, type_sexp)

let builtin_macro = Cons (((dloc, "Macro"), (-4)), (dloc, "Macro_"))

let macro_cons    = Arrow (Aexplicit, None, type_sexp, dloc, type_macro)
let quote_cons    = Arrow (Aexplicit, None, type0, dloc, type_sexp)

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
(*    Name     | Type         | impl          *)
    ("Type"    , type0        , none_fun);
    ("Int"     , type0        , none_fun);
    ("Float"   , type0        , none_fun);
    ("String"  , type0        , none_fun);
    ("Sexp"    , type0        , none_fun);
    ("Macro"   , type0        , none_fun);

(* Built-in Functions *)
    ("_=_"     , type_eq      , none_fun);   (*  t  ->  t  -> bool *)
    ("_+_"     , iop_binary   , iadd_impl);  (* int -> int -> int  *)
    ("_*_"     , iop_binary   , imult_impl); (* int -> int -> int  *)
    ("Macro_"  , macro_cons   , none_fun);

(*  Macro primitives *)
    ("block_"  , type_mblock  , make_block);
    ("symbol_" , type_msymbol , make_symbol);
    ("string_" , type_mstring , make_string);
    ("integer_", type_minteger, make_integer);
    ("node_"   , type_mnode   , make_node);
    (* ("expand_" , builtin_expand , type_mexpand , none_fun); *)

]

(* Make built-in lookup table *)
let _builtin_lookup =
    List.fold_left (fun lkup (name, _, f) ->
        SMap.add name f lkup)
        SMap.empty typer_builtins

let get_builtin_impl str loc =
    try SMap.find str _builtin_lookup
    with Not_found ->
        builtin_error loc "Requested Built-in does not exist"

(* Make lxp context with built-in types *)
let default_lctx () =
    (* Empty context *)
    let lctx = make_lexp_context in

    (* populate ctx *)
    List.fold_left
      (fun ctx (name, ltp, _) ->
        let lxp = Builtin((dloc, name), ltp) in
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
      (fun ctx (name, _, f) ->
        (* We don't have to call eval we know how to evaluate manually *)
        add_rte_variable (Some name) (Vbuiltin(name)) ctx)
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
