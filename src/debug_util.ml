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

(* Utilities *)
open Util
open Fmt
open Debug

(* ASTs *)
open Sexp
open Pexp
open Lexp

(* AST reader *)
open Prelexer
open Lexer
open Lparse
open Eval

(* definitions *)
open Grammar
open Builtin

(* environments *)
open Debruijn
open Env





let dloc = dummy_location;;
let dummy_decl = Imm(String(dloc, "Dummy"));;

let discard v = ();;

(*          Argument parsing        *)
let arg_print_options = ref SMap.empty;;
let arg_files = ref []
let debug_arg = ref 0

let add_p_option name () =
    debug_arg := (!debug_arg) + 1;
    arg_print_options := SMap.add name true (!arg_print_options);;

let get_p_option name =
    try let _ = SMap.find name (!arg_print_options) in
        true
    with
        Not_found -> false
;;

(*
    pretty ?        (print with new lines and indents)
    indent level
    print_type?     (print inferred Type)
    print_index     (print dbi index)
    separate decl   (print extra newline between declarations)
    indent size      4
    highlight       (use console color to display hints)
*)

let _format_mode = ref false
let _ppctx  = ref (true , 0, true, false, true,  2, true)
let _format_dest = ref ""
let _write_file = ref false


let _set_print_pretty ctx v =
    let (a, b, c, d, e, f, g) = !ctx in ctx := (v, b, c, d, e, f, g)

let _set_print_type ctx v =
    let (a, b, c, d, e, f, g) = !ctx in ctx := (a, b, v, d, e, f, g)

let _set_print_index ctx v =
    let (a, b, c, d, e, f, g) = !ctx in ctx := (a, b, c, v, e, f, g)

let _set_print_indent_size ctx v =
    let (a, b, c, d, e, f, g) = !ctx in ctx := (a, b, c, d, e, v, g)

let _set_highlight ctx v =
    let (a, b, c, d, e, f, g) = !ctx in ctx := (a, b, c, d, e, f, v)


let mod_ctx f v = f _ppctx v; f debug_ppctx v
let set_print_type v () = mod_ctx _set_print_type v
let set_print_index v () = mod_ctx _set_print_index v
let set_print_indent_size v =  mod_ctx _set_print_indent_size v
let set_highlight v () =  mod_ctx _set_highlight v
let set_print_pretty v () = mod_ctx _set_print_pretty v


let output_to_file str =
    _write_file := true;
    _format_dest := str;
    set_highlight false ()


let arg_defs = [
    (* format *)
    ("--format",
        Arg.Unit (fun () -> _format_mode := true), " format a typer source code");
    ("-fmt-type=on",
        Arg.Unit (set_print_type true), " Print type info");
    ("-fmt-pretty=on",
        Arg.Unit (set_print_pretty true), " Print with indentation");
    ("-fmt-pretty=off",
        Arg.Unit (set_print_pretty false), " Print expression in one line");
    ("-fmt-type=off",
        Arg.Unit (set_print_type false), " Don't print type info");
    ("-fmt-index=on",
        Arg.Unit (set_print_index true), " Print DBI index");
    ("-fmt-index=off",
        Arg.Unit (set_print_index false), " Don't print DBI index");
    ("-fmt-indent-size",
        Arg.Int set_print_indent_size, " Indent size");
    ("-fmt-highlight=on",
        Arg.Unit (set_highlight true), " Enable Highlighting for typer code");
    ("-fmt-highlight=off",
        Arg.Unit (set_highlight false), " Disable Highlighting for typer code");
    ("-fmt-file",
        Arg.String output_to_file, " Output formatted code to a file");

    (*  Debug *)
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


let format_source () =
    print_string (make_title " ERRORS ");

    let filename = List.hd (!arg_files) in
    let pretoks = prelex_file filename in
    let toks = lex default_stt pretoks in
    let nodes = sexp_parse_all_to_list default_grammar toks (Some ";") in
    let pexps = pexp_decls_all nodes in
    let ctx = default_lctx () in
    let lexps, _ = lexp_p_decls pexps ctx in

    print_string (make_sep '-'); print_string "\n";

    let result = _lexp_str_decls (!_ppctx) lexps in

    if (!_write_file) then (
        print_string ("    " ^ " Writing output file: " ^ (!_format_dest) ^ "\n");
        let file = open_out (!_format_dest) in

        List.iter (fun str -> output_string file str) result;

        flush_all ();
        close_out file;

    ) else (List.iter (fun str ->
        print_string str; print_string "\n") result;)
;;

let main () =
    parse_args ();

    let arg_n = Array.length Sys.argv in

    let usage =
        "\n  Usage:   " ^ Sys.argv.(0) ^ " <file_name> [options]\n" in

    (*  Print Usage *)
    if arg_n == 1 then
        (Arg.usage (Arg.align arg_defs) usage)

    else if (!_format_mode) then (
        format_source ()
    )
    else(
        (if (!debug_arg) = 0 then make_default ());

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

        (if (get_p_option "lctx") then(
            print_lexp_ctx nctx; print_string "\n"));

        (* Eval declaration *)
        let rctx = default_rctx () in
        let rctx = (try eval_decls lexps rctx
            with e ->
                print_rte_ctx (!_global_eval_ctx);
                print_eval_trace ();
                raise e) in

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
                print_eval_result 1 body

        with
            Not_found -> ()
        )
    )
;;

main ()
;;
