(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Stefan Monnier <monnier@iro.umontreal.ca>
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
 *          Define the default Typer Grammar
 *
 * --------------------------------------------------------------------------- *)

(* FIXME: it should be possible to make something like "." bind tighter than
   function application.  *)
(* FIXME: what about sections, as in "if_then e1 else_"?  *)

open Util

type grammar = (int option * int option) SMap.t

(* A token_end array indicates the few chars which are separate tokens,
 * even if not surrounded by spaces, such as '(', ')', and ';'.
 * It also indicates which chars are "inner" operators, i.e. those chars
 * that make up the inner structure of structured identifiers such as
 * foo.bar.baz.  *)
type char_kind = | CKnormal | CKseparate | CKinner of int
type token_env = char_kind array
let default_stt : token_env =
  let stt = Array.make 256 CKnormal
  in stt.(Char.code ';') <- CKseparate;
     stt.(Char.code ',') <- CKseparate;
     stt.(Char.code '(') <- CKseparate;
     stt.(Char.code ')') <- CKseparate;
     stt.(Char.code '.') <- CKinner 5;
     stt

(* default_grammar is auto-generated from typer-smie-grammar via:

  (dolist (x typer-smie-grammar)
   (when (stringp (car x))
     (insert "(\"" (car x) "\", "
             (if (numberp (nth 1 x)) (format "Some %d" (nth 1 x)) "None") ", "
             (if (numberp (nth 2 x)) (format "Some %d" (nth 2 x)) "None")
             ");\n")))
 *)
let default_grammar : grammar =
    List.fold_left (fun g (n, ll, rl) -> SMap.add n (ll, rl) g)
        SMap.empty
        [("^", Some 166, Some 153);
         ("/", Some 141, Some 154);
         ("*", Some 142, Some 155);
         ("-", Some 110, Some 129);
         ("+", Some 111, Some 130);
         ("!=", Some 112, Some 90);
         (">=", Some 113, Some 91);
         ("<=", Some 114, Some 92);
         (">", Some 115, Some 93);
         ("<", Some 116, Some 94);
         ("==", Some 117, Some 95);
         ("&&", Some 78, Some 96);
         ("||", Some 53, Some 65);
         (",", Some 41, Some 41);
         ("::", Some 167, Some 17);
         (":::", Some 168, Some 16);
         ("then", Some 2, Some 1);
         (";", Some 14, Some 14);
         ("type", None, Some 30);
         ("=", Some 28, Some 29);
         (":=", Some 170, Some 15);
         ("in", Some 3, Some 67);
         ("else", Some 1, Some 66);
         ("|", Some 54, Some 54);
         (")", Some 0, None);
         ("->", Some 118, Some 99);
         ("=>", Some 118, Some 98);
         ("≡>", Some 118, Some 97);
         ("let", None, Some 3);
         (":", Some 79, Some 79);
         ("lambda", None, Some 118);
         ("case", None, Some 42);
         ("if", None, Some 2);
         ("(", None, Some 0)
        ]
