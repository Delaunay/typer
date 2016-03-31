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
 *          print out each compilation' steps
 *
 * --------------------------------------------------------------------------- *)

open Debug
open Prelexer
open Lexer
open Sexp
open Grammar
open Pexp
open Util
open Fmt
open Debruijn
open Myers
open Lparse
open Eval
open Lexp

let dloc = dummy_location;;
let dummy_decl = Imm(String(dloc, "Dummy"));;

let discard v = ();;

(*          Argument parsing        *)
let arg_print_options = ref SMap.empty;;
let arg_files = ref []

let add_p_option name () =
    arg_print_options := SMap.add name true (!arg_print_options);;

let get_p_option name =
    try let _ = SMap.find name (!arg_print_options) in
        true
    with
        Not_found -> false
;;

let arg_defs = [
    ("-pretok",
        Arg.Unit (add_p_option "pretok"), " Print pretok debug info");
    ("-tok",
        Arg.Unit (add_p_option "tok"), " Print tok debug info");
    ("-sexp",
        Arg.Unit (add_p_option "sexp"), " Print sexp debug info");
    ("-pexp",
        Arg.Unit (add_p_option "pexp"), " Print pexp debug info");
    ("-lexp",
        Arg.Unit (add_p_option "lexp"), " Print lexp debug info");
    ("-lctx",
        Arg.Unit (add_p_option "lctx"), " Print lexp context");
    ("-rctx",
        Arg.Unit (add_p_option "rctx"), " Print runtime context");
    ("-all",
        Arg.Unit (fun () ->
            add_p_option "pretok" ();
            add_p_option "tok" ();
            add_p_option "sexp" ();
            add_p_option "pexp" ();
            add_p_option "lexp" ();
            add_p_option "lctx" ();
            add_p_option "rctx" ();),
        " Print all debug info");
];;

let parse_args () =
  Arg.parse arg_defs (fun s -> arg_files:= s::!arg_files) ""

let make_default () =
    arg_print_options := SMap.empty;
    add_p_option "sexp" ();
    add_p_option "pexp" ();
    add_p_option "lexp" ()
;;

let main () =
    parse_args ();

    let arg_n = Array.length Sys.argv in

    let usage =
        "\n  Usage:   " ^ Sys.argv.(0) ^ " <file_name> [options]\n" in

    (*  Print Usage *)
    if arg_n == 1 then
        (Arg.usage (Arg.align arg_defs) usage)
    else(
        (if arg_n = 2 then make_default ());

        let filename = List.hd (!arg_files) in

        print_string (make_title " ERRORS ");

        (* get pretokens*)
        let pretoks = prelex_file filename in

        (if (get_p_option "pretok") then(
            print_string (make_title " PreTokens");
            debug_pretokens_print_all pretoks; print_string "\n"));

        (* get sexp/tokens *)
        let toks = lex default_stt pretoks in

        (if (get_p_option "tok") then(
            print_string (make_title " Base Sexp");
            debug_sexp_print_all toks; print_string "\n"));

        (* get node sexp  *)
        let nodes = sexp_parse_all_to_list default_grammar toks (Some ";") in

        (if (get_p_option "sexp") then(
            print_string (make_title " Node Sexp ");
            debug_sexp_print_all nodes; print_string "\n"));

        (* Parse All Declaration *)
        let pexps = pexp_decls_all nodes in

        (if (get_p_option "pexp") then(
            print_string (make_title " Pexp ");
            debug_pexp_decls pexps; print_string "\n"));

        (* get lexp *)
        let ctx = default_lctx () in

        let lexps, nctx =
            try lexp_p_decls pexps ctx
            with e -> (
                print_lexp_ctx (!_global_lexp_ctx);
                print_lexp_trace ();
                raise e
            ) in

        (if (get_p_option "lexp") then(
            print_string (make_title " Lexp ");
            debug_lexp_decls lexps; print_string "\n"));

        print_string "\n\n";

        (if (get_p_option "lctx") then(
            print_lexp_ctx nctx; print_string "\n"));

        (* Eval declaration *)
        let rctx = make_runtime_ctx in
        let rctx = eval_decls lexps rctx in

        (if (get_p_option "rctx") then(
            print_rte_ctx rctx; print_string "\n"));

        (* Eval Each Expression *)
        print_string (make_title " Eval Print ");

        (try
            (* Check if main is present *)
            let main = (senv_lookup "main" nctx) in
            (* Push main args here if any *)

            (* get main body *)
            let body = (get_rte_variable (Some "main") main rctx) in
            (* eval main *)
            let r = (debug_eval body rctx) in
                print_eval_result 1 r

        with
            Not_found -> ()
        )
    )
;;

main ()
;;
