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

open Fmt        (*  make_title, table util *)
open Lexp       (*  lexp_print *)
open Myers
open Util       (* msg_error    *)

let dloc = dummy_location

let env_error loc msg =
    msg_error "ENV" loc msg;
    raise (internal_error msg)
;;

let str_idx idx = "[" ^ (string_of_int idx) ^ "]"

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

let print_rte_ctx ctx =
    let (l, b) = ctx in
    print_myers_list l
    (fun (n, g) ->
        let _ =
        match n with
            | Some m -> lalign_print_string m 12; print_string "  |  "
            | None -> print_string (make_line ' ' 12); print_string "  |  " in
        lexp_print g; print_string "\n")
;;


(* Offset is used when we eval declaration one by one                    *)
(* i.e not everything is present so we need to account for missing decls *)
type decls_offset = int

(*  Runtime Environ *)
type runtime_env = ((string option * lexp) myers) * (int * int * decls_offset)

let make_runtime_ctx = (nil, (0, 0, 0));;

let get_rte_size (ctx: runtime_env): int = let (l, _) = ctx in length l;;

let add_rte_variable name x ctx =
    let (l, b) = ctx in
    let lst = (cons (name, x) l) in
        (lst, b);;

let is_free_var idx ctx =
    let (l, (osize, _, offset)) = ctx in
    let tsize = (get_rte_size ctx) - osize in
        if idx > tsize then true else false
;;

let get_rte_variable (name: string option) (idx: int) (ctx: runtime_env): lexp =
    let (l, (_, _, offset)) = ctx in
    let idx = if (is_free_var idx ctx) then idx - offset else idx in
    try (let (tn, x) = (nth idx l) in
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
            n ^ "\" idx: " ^ (str_idx idx) ^ " offset: " ^ (str_idx offset) ^
            " free_var? " ^ (string_of_bool (is_free_var idx ctx)))
;;


(* This function is used when we enter a new scope                         *)
(* it saves the size of the environment before temp var are added          *)
(* it allow us to remove temporary variables when we enter a new scope     *)
let local_ctx ctx =
    let (l, (_, _, off)) = ctx in
    let osize = length l in
        (l, (osize, 0, off))
;;

let select_n ctx n =
    let (l, a) = ctx in
    let r = ref nil in
    let s = (length l) - 1 in

    for i = 0 to n - 1 do
        r := (cons (nth (s - i) l) (!r));
    done;

    ((!r), a)

let temp_ctx ctx =
    let (l, (osize, _, _)) = ctx in
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
