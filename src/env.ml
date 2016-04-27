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
open Lexp       (*  lexp_print *)

open Myers
open Debruijn


let dloc = dummy_location

let env_error loc msg =
    msg_error "ENV" loc msg;
    raise (internal_error msg)
;;

let str_idx idx = "[" ^ (string_of_int idx) ^ "]"

(*  currently, we don't do much *)
type value_type =
    | Value of lexp
    | Closure of lexp * (((string option * value_type) ref myers) * (int * int))
    (* Macro type *)
    | Vsexp of sexp
    (* Unable to eval during macro expansion, only throw if the value is used *)
    | Vdummy

let get_value_lexp (vtp: value_type) =
    match vtp with
        | Value s -> s
        | Closure (s, _) -> s
        | _ -> env_error dloc "Does not hold a lexp"

let value_print (vtp: value_type) =
    match vtp with
        | Closure (lxp, _) ->
            print_string ("Closure(" ^ (_lexp_to_str (!debug_ppctx) lxp) ^ ")")
        | Value s -> lexp_print s
        | Vsexp sxp -> sexp_print sxp
        | _ -> print_string "value_print_dummy"


let value_location (vtp: value_type) = lexp_location (get_value_lexp vtp)


(*  Runtime Environ *)
type env_cell = (string option * value_type) ref
type runtime_env = (env_cell myers) * (int * int)

let make_runtime_ctx = (nil, (0, 0));;

let get_rte_size (ctx: runtime_env): int = let (l, _) = ctx in length l;;

let is_free_var idx ctx =
    let (l, (osize, _)) = ctx in
    let tsize = (get_rte_size ctx) - osize in
        if idx > tsize then true else false
;;

let get_rte_variable (name: string option) (idx: int) (ctx: runtime_env): value_type =
    let (l, _) = ctx in
    try (
        let ref_cell = (nth idx l) in
        let (tn, x) = !ref_cell in
    match (tn, name) with
        | (Some n1, Some n2) -> (
            if n1 = n2 then
                x
            else (
            env_error dloc
                ("Variable lookup failure. Expected: \"" ^
                n2 ^ "[" ^ (string_of_int idx) ^ "]" ^ "\" got \"" ^ n1 ^ "\"")))

        | _ -> x)
    with Not_found ->
        let n = match name with Some n -> n | None -> "" in
        env_error dloc ("Variable lookup failure. Var: \"" ^
            n ^ "\" idx: " ^ (str_idx idx))
;;

let rte_shift vref ctx =
    let (_, (osize, _)) = ctx in    (* number of variable declared outside *)
    let csize = get_rte_size ctx in (* current size                        *)
    let offset = csize - osize in
    let ((loc, name), idx) = vref in
    (* check if variable is free *)
    let offset = if idx > offset then offset else 0 in
    (* shift idx *)
        idx + offset

let add_rte_variable name (x: value_type) (ctx: runtime_env): runtime_env =
    let (l, b) = ctx in
    let lst = (cons (ref (name, x)) l) in
        (lst, b);;

let set_rte_variable idx name (lxp: value_type) ctx =
    let (l, _) = ctx in
    let ref_cell = (nth idx l) in
    let (n, _) = !ref_cell in

    match (n, name) with
        | Some n1, Some n2 ->
            if (n1 != n2) then
                env_error dloc ("Variable's Name must Match: " ^ n1 ^ " vs " ^ n2)
            else(
                ref_cell := (name, lxp); ctx)

        | _ -> ref_cell := (name, lxp); ctx


(* This function is used when we enter a new scope                         *)
(* it saves the size of the environment before temp var are added          *)
(* it allow us to remove temporary variables when we enter a new scope     *)
let local_ctx ctx =
    let (l, (_, _)) = ctx in
    let osize = length l in
        (l, (osize, 0))
;;

let select_n (ctx: runtime_env) n: runtime_env =
    let (l, a) = ctx in
    let r = ref nil in
    let s = (length l) - 1 in

    for i = 0 to n - 1 do
        r := (cons (nth (s - i) l) (!r));
    done;

    ((!r), a)

let temp_ctx (ctx: runtime_env): runtime_env =
    let (l, (osize, _)) = ctx in
    let tsize = length l in
        (* Check if temporary variables are present *)
        if tsize != osize then
            (* remove them *)
            (select_n ctx osize)
        else
            ctx
;;

(* Select the n first variable present in the env *)
let nfirst_rte_var n ctx =
    let rec loop i acc =
        if i < n then
            loop (i + 1) ((get_rte_variable None i ctx)::acc)
        else
            List.rev acc in
    loop 0 []
;;

let print_myers_list l print_fun =
    let n = (length l) - 1 in

    print_string (make_title " ENVIRONMENT ");
    make_rheader [(None, "INDEX");
        (None, "VARIABLE NAME"); (Some ('l', 48), "VALUE")];
    print_string (make_sep '-');

    for i = 0 to n do
    print_string "    | ";
        ralign_print_int (n - i) 5;
        print_string " | ";
        print_fun (nth (n - i) l);
    done;
    print_string (make_sep '=');
;;

let print_rte_ctx (ctx: runtime_env) =
    let (l, b) = ctx in
    print_myers_list l
    (fun x ->
        let (n, g) = !x in
        let _ =
        match n with
            | Some m -> lalign_print_string m 12; print_string "  |  "
            | None -> print_string (make_line ' ' 12); print_string "  |  " in

        value_print g; print_string "\n")
;;

