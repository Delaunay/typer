(* main.ml --- Toplevel file for Typer.

Copyright (C) 2011-2016  Free Software Foundation, Inc.

Author: Stefan Monnier <monnier@iro.umontreal.ca>
Keywords: languages, lisp, dependent types.

This file is part of Typer.

Typer is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any
later version.

Typer is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
more details.

You should have received a copy of the GNU General Public License along with
this program.  If not, see <http://www.gnu.org/licenses/>.  *)

(* open Printf *)
open Util
open Lexer
open Sexp
(* open Elaborate *)
(* open Javascript *)

(* I think they shouldn't be here, but for now I use them.  *)
(* open Lexp *)
open Prelexer
open Pexp

(* Overview.
 *
 * The front-end is split into parsing and elaboration.
 * Parsing (string -> pexp) is done in the following steps:
 * - Prelexer (string -> pretokens): Get rid of comments, recognize
 *   strings, match braces, and split the rest into chunks separated by
 *   whitespace.  This process is not influenced by the program
 *   being compiled.
 * - Lexer (pretokens -> tokens): Split the pretokens into tokens.
 *   This recognizes floats, integers, and splits the few tokens that are
 *   "self-delimited" rather than being delimited by spaces
 *   (e.g. semi-colons, since ";;" is one pretoken but two tokens).
 *   This phase depends on the lexing rules that define which tokens are
 *   self-delimiting.  Programs can change those rules.
 * - Sexp (tokens -> sexp): Extract the structure using operator precedence
 *   parsing.  The result is an S-expression.  This phase depends on the
 *   operator precedences, which can be changed by the programs.
 * - Pexp (sexp -> pexp): Assuming a Sexp represents a valid Typer
 *   expression, turn it into a specialized datatype for easier subsequent
 *   processing.  This process is not influenced by the program
 *   being compiled.
 *
 * Elaboration (pexp -> lexp) is basically done in a single step, which is
 * decomposed into a few different parts which are all run bit-by-bit in
 * interleaved ways during elaboration:
 * - Normalize: Perform β-reductions to normalize open terms.
 * - Unify: Higher-order unification of `lexp' terms.  May call the normalizer.
 * - Eval: Call-by-value interpreter of closed lexp terms, with potential
 *   side-effects and all.
 * - Elaborate: Expand macros and infer types.  Will call the evaluator to
 *   perform macro expansion and the unification to infer the types.
 * The result of the front-end is a term of type Lexp, a fairly normal
 * explicitly typed lambda-calculus amenable to the usual
 * compilation strategies.
 *
 * The middle-end is done in the following steps:
 * - Type-erasure (lexp -> ulexp) erases all the type annotation and erasable
 *   arguments.
 *
 * The Javascript backend is done in the following steps:
 * - Conversion (ulexp -> jsexp) turns a Ulexp into an abstract representation
 *   of a Javascript expression.
 * - The output step then takes this Jsexp and turns it into a Javascript
 *   program.
 *)

(*************** The Top Level *********************)

let default_stt =
  let stt = Array.make 256 false
  in stt.(Char.code ';') <- true;
     stt.(Char.code ',') <- true;
     stt.(Char.code '(') <- true;
     stt.(Char.code ')') <- true;
     stt

(* default_grammar is auto-generated from typer-smie-grammar via:

  (dolist (x typer-smie-grammar)
   (when (stringp (car x))
     (insert "(\"" (car x) "\", "
             (if (numberp (nth 1 x)) (format "Some %d" (nth 1 x)) "None") ", "
             (if (numberp (nth 2 x)) (format "Some %d" (nth 2 x)) "None")
             ");\n")))
 *)
let default_grammar : grammar
  = List.fold_left (fun g (n, ll, rl) -> SMap.add n (ll, rl) g)
                   SMap.empty
                   [("^", Some 171, Some 159);
                    ("/", Some 148, Some 160);
                    ("-", Some 92, Some 110);
                    ("+", Some 93, Some 111);
                    ("!=", Some 94, Some 75);
                    (">=", Some 95, Some 76);
                    ("<=", Some 96, Some 77);
                    (">", Some 97, Some 78);
                    ("<", Some 98, Some 79);
                    ("&&", Some 64, Some 81);
                    ("||", Some 39, Some 51);
                    (",", Some 26, Some 26);
                    ("then", Some 1, Some 0);
                    ("=", Some 99, Some 80);
                    ("type", None, Some 27);
                    (";", Some 15, Some 15);
                    ("*", Some 137, Some 137);
                    (":", Some 173, Some 115);
                    ("]", Some 3, None);
                    ("->", Some 126, Some 114);
                    ("=>", Some 126, Some 113);
                    ("≡>", Some 126, Some 112);
                    ("in", Some 2, Some 53);
                    ("else", Some 0, Some 52);
                    ("|", Some 40, Some 40);
                    (")", Some 4, None);
                    ("[", None, Some 3);
                    ("case", None, Some 28);
                    ("lambda", None, Some 126);
                    ("letrec", None, Some 2);
                    ("let", None, Some 2);
                    ("if", None, Some 1);
                    ("(", None, Some 4);
                   ]


let process_typer_file sourcename choppable_suffix venv =
  (* let targetbase = Filename.chop_suffix sourcename choppable_suffix in *)
  let pretokens = prelex_file sourcename in
  let tokens = lex default_stt pretokens in
  (* sexp_print (Node (Symbol (dummy_location, "tokens"), tokens));
   * print_newline(); *)

  (* let js_file  = open_out (sourcename ^ ".js") in
   * 
   * output_string js_file (Javascript.intro ^ "\n\n"); *)

  let rec process_decl (grm, tokens, decls, pnames, delayed, senv, venv) =
    let (sexp, rest) = sexp_parse_all grm tokens (Some ";") in
    (* sexp_print e; print_newline(); *)
    sexp_print sexp; print_newline();
    let pdecls = pexp_p_decls sexp in
    sexp_print (pexp_u_decls pdecls); print_newline();
    (* let (decls',pnames',delayed',senv',venv')
     *   = List.fold_left (elaborate_decl (ScopeLevel 0) (default_stt, grm))
     *                    ([], pnames, delayed, senv, venv)
     *                    pdecls in
     * let pdecls = lexp_unparse_decls decls' in
     * sexp_print (pexp_u_decls pdecls); print_newline(); *)
    (* print_string ": ";
     * sexp_print (pexp_unparse (lexp_unparse t)); print_newline(); *)
    (* print_newline(); *)



    (* let ule = Ulexp.optimisation_pass (Ulexp.from_lexp le) in
     *   Ulexp.pretty_print print_string ule;
     * 
     * 
     *   (let freevars = Ulexp.freevars ule in
     *     Ulexp.print_freevars freevars ;
     *     Ulexp.print_scc ule;
     *   );
     * 
     * 
     *   print_string "\nJAVASCRIPT:\n ";
     * 
     *   print_jsstatement (output_string js_file) (translate_to_js (ule));
     *   output_string js_file "\n\n";
     * 
     *   output_jsexp (translate_to_js (ule));
     * 
     * 
     *   (\*jsexp_parse_to_console le;*\)
     *   print_newline();
     *   print_newline(); *)

    match rest with
      | [] -> (decls, venv)
      | _ -> process_decl (grm, rest,
                          pdecls @ decls, pnames, delayed, senv, venv)
  in process_decl (default_grammar, tokens,
                   [], SMap.empty, None, [], venv)
   (* ; close_out js_file *)

let process_file filename venv =
  if Filename.check_suffix filename ".typer" then
    process_typer_file filename ".typer" venv
  else
    raise (Arg.Bad ("Unknown filetype: " ^ filename))

let (perv_decls, perv_venv) = process_file "pervasive.typer" None

let _ = Arg.parse
          [
          (* "-dpretty-term", Arg.Set print_pretty,
           *     "Pretty-print after preterm conversion"; *)
          (* "-dno-pretty-term", Arg.Clear print_pretty,
           *     "Don't pretty-print after preterm conversion"; *)
          (* "-dpretty-cons", Arg.Set print_constr,
           *     "Pretty-print after preterm conversion"; *)
          (* "-dno-pretty-cons", Arg.Clear print_constr,
           *     "Don't pretty-print after preterm conversion"; *)
          (* "-dverbose-pretty", Arg.Unit (fun () -> Print.set_pp_verbose true),
           *     "Use an extra-unambiguous pretty-printer syntax"; *)
          (* "-use-typeof", Arg.Set do_verif_types,
           *     "Check types with typeof rather than infer them"; *)
          ]
          (fun s -> ignore (process_file s perv_venv))
          "Usage: typer [options] [files]\nOptions are:"
