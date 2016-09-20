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
open Printf

let builtin_error loc msg =
    msg_error "BUILT-IN" loc msg;
    raise (internal_error msg)

let builtin_warning loc msg =
    msg_warning "BUILT-IN" loc msg

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
]

let builtin_size = ref 0

let default_predef_map : predef_table =
    (* add predef name, expr will be populated when parsing *)
    List.fold_left (fun m name ->
        SMap.add name (ref None) m) SMap.empty predef_name

let predef_map = ref default_predef_map

let get_predef_raw (name: string) : lexp =
    match !(SMap.find name (!predef_map)) with
        | Some exp -> exp
        | None -> builtin_error dloc ("\""^ name ^ "\" was not predefined")

let get_predef_option (name: string) ctx =
  let r = (get_size ctx) - !builtin_size - 0 in
    match !(SMap.find name (!predef_map)) with
        | Some exp -> Some (mkSusp exp (S.shift r))
        | None -> None

let get_predef (name: string) ctx =
  let r = (get_size ctx) - !builtin_size - 0 in
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
let dloc    = dummy_location
let type0   = Sort (dloc, Stype (SortLevel (SLn 0)))
let type1   = Sort (dloc, Stype (SortLevel (SLn 1)))
let type2   = Sort (dloc, Stype (SortLevel (SLn 2)))
let type_omega = Sort (dloc, StypeOmega)
let type_level = Sort (dloc, StypeLevel)

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
let _generic_binary_iop name f loc (depth: int) (args_val: value_type list)
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
let none_fun : (location -> int -> value_type list -> runtime_env -> value_type)
    = (fun loc args_val ctx ->
    builtin_error loc "Requested Built-in was not implemented")

let make_symbol loc depth args_val ctx  =
    (* symbol is a simple string *)
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("symbol_ expects 1 argument") in

        match lxp with
            | Vstring(str) -> Vsexp(Symbol(loc, str))
            | _ -> builtin_error loc ("symbol_ expects one string as argument")


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
            builtin_error dloc "List conversion failure'"

let make_node loc depth args_val ctx    =

    let op, tlist = match args_val with
        | [Vsexp(op); lst] -> op, lst
        | op::_  ->
          builtin_error loc
            ("node_ expects one 'Sexp' got " ^ (value_name op))
        | _ -> typer_unreachable "-" in

    (* value_print tlist; print_string "\n"; *)

    let args = tlist2olist [] tlist in

    let s = List.map (fun g -> match g with
        | Vsexp(sxp)  -> sxp
        (* eval transform sexp into those... *)
        | Vint (i)    -> Integer(dloc, i)
        | Vstring (s) -> String(dloc, s)
        | _ ->
          print_rte_ctx ctx;
          print_string (value_name g); print_string "\n";
          value_print g; print_string "\n";
            builtin_error loc ("node_ expects 'List Sexp' second as arguments")) args in

        Vsexp(Node(op, s))

let make_string loc depth args_val ctx  =
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("string_ expects 1 argument") in

        match lxp with
            | Vstring(str) -> Vsexp(String(loc, str))
            | _ -> builtin_error loc ("string_ expects one string as argument")

let make_integer loc depth args_val ctx =
    let lxp = match args_val with
        | [r] -> r
        | _ -> builtin_error loc ("integer_ expects 1 argument") in

        match lxp with
            | Vint(str) -> Vsexp(Integer(loc, str))
            | _ -> builtin_error loc ("integer_ expects one string as argument")

let make_float loc depth args_val ctx   = Vdummy
let make_block loc depth args_val ctx   = Vdummy

let ttrue = Vcons((dloc, "True"), [])
let tfalse = Vcons((dloc, "False"), [])
let btyper b = if b then ttrue else tfalse

let string_eq loc depth args_val ctx =
    match args_val with
        | [Vstring(s1); Vstring(s2)] -> btyper (s1 = s2)
        | _ -> builtin_error loc "string_eq expects 2 strings"

let int_eq loc depth args_val ctx =
    match args_val with
        | [Vint(s1); Vint(s2)] -> btyper (s1 = s2)
        | _ -> builtin_error loc "int_eq expects 2 integer"

let sexp_eq loc depth args_val ctx =
    match args_val with
    | [Vsexp (s1); Vsexp (s2)] -> btyper (sexp_equal s1 s2)
    | _ -> builtin_error loc "sexp_eq expects 2 sexp"

let open_impl loc depth args_val ctx =

  let file, mode = match args_val with
    | [Vstring(file_name); Vstring(mode)] -> file_name, mode
    | _ -> builtin_error loc "open expects 2 strings" in

   (* open file *) (* return a file handle *)
   Vcommand(fun () ->
      match mode with
        | "r" -> Vin(open_in file)
        | "w" -> Vout(open_out file)
        | _ -> builtin_error loc "wrong open mode")

let read_impl loc depth args_val ctx =

  let channel = match args_val with
    | [Vin(c); _] -> c
    | _ ->
      List.iter (fun v -> value_print v; print_string "\n") args_val;
      builtin_error loc "read expects an in_channel" in

  let line = input_line channel in
    Vstring(line)

let write_impl loc depth args_val ctx =

  let channel, msg = match args_val with
    | [Vout(c); Vstring(msg)] -> c, msg
    | _ ->
      List.iter (fun v -> value_print v) args_val;
      builtin_error loc "read expects an out_channel" in

    fprintf channel "%s" msg;
      Vdummy

let is_lbuiltin idx ctx =
    let bsize = 1 in
    let csize = get_size ctx in

    if idx >= csize - bsize then
        true
    else
        false

(* --------------------------------------------------------------------------
 *  Built-in Macro
 * -------------------------------------------------------------------------- *)

(* Those are function that are evaluated during lexp_parse *)

let get_attribute_impl loc largs ctx ftype =

  let (vi, vn), (ai, an) = match largs with
      | [Var((_, vn), vi); Var((_, an), ai)] -> (vi, vn), (ai, an)
      | _ -> builtin_error loc "get-attribute expects two arguments" in

  let lxp = get_property ctx (vi, vn) (ai, an) in
  let ltype = match env_lookup_expr ctx ((loc, an), ai) with
    | Some ltp -> ltp
    | None -> builtin_error loc "not expression available" in

    lxp, ltype

let new_attribute_impl loc largs ctx ftype =

  let eltp = match largs with
    | [eltp] -> eltp
    | _ -> builtin_warning loc "new-attribute expects one argument"; type0 in

    eltp, ftype

let has_attribute_impl loc largs ctx ftype =

  let (vi, vn), (ai, an) = match largs with
      | [Var((_, vn), vi); Var((_, an), ai)] -> (vi, vn), (ai, an)
      | _ -> builtin_error loc "has-attribute expects two arguments" in

  let b = has_property ctx (vi, vn) (ai, an) in



  let rvar = if b then get_predef "True" ctx else get_predef "False" ctx in
    rvar, (get_predef "Bool" ctx)

let declexpr_impl loc largs ctx ftype =

  let (vi, vn) = match largs with
    | [Var((_, vn), vi)] -> (vi, vn)
    | _ -> builtin_error loc "declexpr expects one argument" in

  let lxp = match env_lookup_expr ctx ((loc, vn), vi) with
    | Some lxp -> lxp
    | None -> builtin_error loc "no expr available" in
  let ltp = env_lookup_type ctx ((loc, vn), vi) in
    lxp, ftype


let decltype_impl loc largs ctx ftype =

  let (vi, vn) = match largs with
    | [Var((_, vn), vi)] -> (vi, vn)
    | _ -> builtin_error loc "decltype expects one argument" in

  let ltype = env_lookup_type ctx ((loc, vn), vi) in
    (* mkSusp prop (S.shift (var_i + 1)) *)
    ltype, type0

let builtin_macro = [
  (* FIXME: These should be functions!  *)
  ("decltype",      decltype_impl);
  ("declexpr",      declexpr_impl);
  (* FIXME: These are not macros but `special-forms`.
   * We should add here `let_in_`, `case_`, etc...  *)
  ("get-attribute", get_attribute_impl);
  ("new-attribute", new_attribute_impl);
  ("has-attribute", has_attribute_impl);
]

type macromap =
  (location -> lexp list -> elab_context -> lexp -> (lexp * lexp)) SMap.t

let macro_impl_map : macromap =
  List.fold_left (fun map (name, funct) ->
    SMap.add name funct map) SMap.empty builtin_macro

let get_macro_impl loc name =
  try SMap.find name macro_impl_map
    with Not_found -> builtin_error loc ("Builtin macro" ^ name ^ " not found")

let is_builtin_macro name =
  try let _ = SMap.find name macro_impl_map in true
    with Not_found -> false



