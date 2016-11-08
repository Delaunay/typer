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
 *          Implements runtime environment
 *
 * --------------------------------------------------------------------------- *)

open Util       (* msg_error    *)
open Fmt        (*  make_title, table util *)

open Sexp

open Elexp
module M = Myers
module L = Lexp

let dloc = dummy_location

let error loc msg = msg_error "ENV" loc msg; raise (internal_error msg)
let warning loc msg = msg_warning "ENV" loc msg

let str_idx idx = "[" ^ (string_of_int idx) ^ "]"

type value_type =
    | Vint of int
    | Vstring of string
    | Vcons of symbol * value_type list
    | Vbuiltin of string
    | Vfloat of float
    | Closure of string * elexp * runtime_env
    | Vsexp of sexp             (* Values passed to macros.  *)
    (* Unable to eval during macro expansion, only throw if the value is used *)
    | Vdummy
    | Vin of in_channel
    | Vout of out_channel
    | Vcommand of (unit -> value_type)

 (*  Runtime Environ *)
 and env_cell = (string option * (value_type ref))
 and runtime_env = env_cell M.myers

let rec value_equal a b =
  match a, b with
    | Vint(i1), Vint(i2)         -> i1 = i2
    | Vstring(s1), Vstring(s2)   -> s1 = s2
    | Vbuiltin(s1), Vbuiltin(s2) -> s1 = s2
    | Vfloat(f1), Vfloat(f2)     -> f1 = f2
    | Vsexp(a), Vsexp(b)         -> sexp_equal a b
    | Vin (c1), Vin(c2)          -> c1 = c2
    | Vout (c1), Vout(c2)        -> c2 = c2
    | Vcommand (f1), Vcommand(f2)-> f1 = f2
    | Vdummy, Vdummy             -> warning dloc "Vdummy"; true

    | Closure(s1, b1, ctx1), Closure(s2, b2, ctx2) ->
      warning dloc "Closure";
      if (s1 != s2) then false else true

    | Vcons((_, ct1), a1), Vcons((_, ct2), a2) ->
      if (ct1 != ct2) then false else
        not (List.exists2
          (fun a b -> not (value_equal a b)) a1 a2)

    | _ -> false

let rec value_eq_list a b =
  match a, b with
    | [], [] -> true
    | v1::vv1, v2::vv2 ->
      value_equal v1 v2 && value_eq_list vv1 vv2
    | _ -> false

let value_location (vtp: value_type) =
    match vtp with
        | Vcons ((loc, _), _) -> loc
        | Closure (_, lxp, _) -> elexp_location lxp
        (* location info was lost or never existed *)
        | _ -> dloc

let value_name v =
  match v with
    | Vin   _ -> "Vin"
    | Vout  _ -> "Vout"
    | Vint  _ -> "Vint"
    | Vsexp  _ -> "Vsexp"
    | Vcons  _ -> "Vcons"
    | Vfloat _ -> "Vfloat"
    | Vdummy     -> "Vdummy"
    | Vstring  _ -> "Vstring"
    | Closure  _ -> "Closure"
    | Vbuiltin _ -> "Vbuiltin"
    | Vcommand _ -> "Vcommand"

let rec value_string v =
  match v with
    | Vin   _ -> "in_channel"
    | Vout  _ -> "out_channe;"
    | Vdummy     -> "dummy"
    | Vcommand _ -> "command"
    | Vstring  s -> "\"" ^ s ^ "\""
    | Vbuiltin s -> s
    | Vint     i -> string_of_int i
    | Vfloat   f -> string_of_float f
    | Vsexp    s -> sexp_string s
    | Closure  (s, elexp, _) -> "(lambda " ^ s ^ " -> " ^ (elexp_string elexp) ^ ")"
    | Vcons    ((_, s), lst) ->
      let args = List.fold_left (fun str v ->
        (str ^ " " ^ (value_string v))) "" lst in
          "(" ^ s ^ args ^ ")"

let value_print (vtp: value_type) = print_string (value_string vtp)

let make_runtime_ctx = M.nil

let get_rte_size (ctx: runtime_env): int = M.length ctx

let get_rte_variable (name: string option) (idx: int)
                     (ctx: runtime_env): value_type =
    try (
        let (defname, ref_cell) = (M.nth idx ctx) in
        let x = !ref_cell in
    match (defname, name) with
        | (Some n1, Some n2) -> (
            if n1 = n2 then
                x
            else (
            error dloc
                ("Variable lookup failure. Expected: \"" ^
                n2 ^ "[" ^ (string_of_int idx) ^ "]" ^ "\" got \"" ^ n1 ^ "\"")))

        | _ -> x)
    with Not_found ->
        let n = match name with Some n -> n | None -> "" in
        error dloc ("Variable lookup failure. Var: \"" ^
            n ^ "\" idx: " ^ (str_idx idx))

let add_rte_variable name (x: value_type) (ctx: runtime_env)
    : runtime_env =
  let valcell = ref x in
  M.cons (name, valcell) ctx

let set_rte_variable idx name (v: value_type) (ctx : runtime_env) =
    let (n, ref_cell) = (M.nth idx ctx) in

    (match (n, name) with
     | Some n1, Some n2 ->
        if (n1 != n2) then
          error dloc ("Variable's Name must Match: " ^ n1 ^ " vs " ^ n2)
     | _ -> ());

    ref_cell := v

(* Select the n first variable present in the env *)
let nfirst_rte_var n ctx =
    let rec loop i acc =
        if i < n then
            loop (i + 1) ((get_rte_variable None i ctx)::acc)
        else
            List.rev acc in
    loop 0 []

let print_myers_list l print_fun start =
    let n = (M.length l) - 1 in
    print_string (make_title " ENVIRONMENT ");
    make_rheader [(None, "INDEX");
        (None, "VARIABLE NAME"); (Some ('l', 48), "VALUE")];
    print_string (make_sep '-');

    for i = start to n do
    print_string "    | ";
        ralign_print_int (n - i) 5;
        print_string " | ";
        print_fun (M.nth (n - i) l);
    done;
    print_string (make_sep '=')

let print_rte_ctx_n (ctx: runtime_env) start =
  print_myers_list
    ctx
    (fun (n, vref) ->
      let g = !vref in
      let _ =
        match n with
        | Some m -> lalign_print_string m 12; print_string "  |  "
        | None -> print_string (make_line ' ' 12); print_string "  |  " in

      value_print g; print_string "\n") start

(* Only print user defined variables *)
let print_rte_ctx ctx =
  (* FIXME: harcoded -3, runtime_env has 3 variables missing *)
  print_rte_ctx_n ctx (!L.builtin_size - 3)

(* Dump the whole context *)
let dump_rte_ctx ctx =
  print_rte_ctx_n ctx 0
