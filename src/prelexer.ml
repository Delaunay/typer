(* prelexer.ml --- First half of lexical analysis of Typer.

Copyright (C) 2011-2012, 2016  Free Software Foundation, Inc.

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

open Util

let prelexer_error = msg_error "PRELEXER"

type pretoken =
  | Pretoken of location * string
  | Prestring of location * string
  (* | Preerror of location * string *)
  | Preblock of location * pretoken list * location

(*************** The Pre-Lexer phase *********************)

(* In order to allow things like "module Toto { open Titi; ... }" where
   lexical and syntatic declarations from Titi do impact the parsing of
   "...", the "module" macro has to receive an unparsed form of "...".

   So Sexps will keep the {...} blocks "unparsed" and macros that take such
   arguments will want to call the reader on them explicitly.  But in order
   to avoid traversing blocks as many times as they are nested, we perform
   the "block recognition" once and for all at the start via a "pre-lexer".
   This also handles strings and comments since they may contain braces
   (contrary to numbers, for example which are not handled here).  *)

(* FIXME: Add syntax for char constants (maybe 'c').  *)
(* FIXME: Handle multiline strings.  *)

let string_sub str b e = String.sub str b (e - b)

let inc_cp (cp:charpos) (c:char) =
  (* Count char positions in utf-8: don't count the non-leading bytes.  *)
  if (Char.code c < 128 || Char.code c >= 192) then cp+1 else cp

let rec prelex (file : string) (fin : in_channel) ln ctx acc
    : pretoken list =
  try
    (* let fin = open_in file in *)
    let line = input_line fin in
    let limit = String.length line in
    let nextline = prelex file fin (ln + 1) in
    let rec prelex' ctx (bpos:bytepos) (cpos:charpos) acc =
      let nexttok = prelex' ctx in
      if bpos >= limit then nextline ctx acc else
        match line.[bpos] with
          | c when c <= ' ' -> nexttok (bpos+1) (cpos+1) acc
          | '%' -> nextline ctx acc      (* A comment.  *)
          | '"' ->                       (* A string.  *)
            let rec prestring bp cp chars =
              if bp >= limit then
                (prelexer_error {file=file; line=ln; column=cpos}
                           "Unterminated string";
                 nextline ctx
                          (Prestring ({file=file; line=ln; column=cpos}, "")
                           :: acc))
              else
                match line.[bp] with
                  | '"' ->
                    nexttok (bp+1) (cp+1)
                            (Prestring ({file=file; line=ln; column=cpos},
                                        string_implode (List.rev chars))
                             :: acc)
                  | '\\' ->
                    (if bpos + 1 >= limit then
                       (prelexer_error {file=file; line=ln; column=cpos}
                                  "Unterminated string";
                        nextline ctx
                                 (Prestring ({file=file; line=ln; column=cpos},
                                             "")
                                  :: acc))
                     else
                       match line.[bp + 1] with
                         | 't' -> prestring (bp+2) (cp+2) ('\t' :: chars)
                         | 'n' -> prestring (bp+2) (cp+2) ('\n' :: chars)
                         | 'r' -> prestring (bp+2) (cp+2) ('\r' :: chars)
                         | ('u' | 'U') ->
                           prelexer_error {file=file; line=ln; column=cp}
                                     "Unimplemented unicode escape";
                           prestring (bp+2) (cp+2) chars
                         | char -> prestring (bp+2) (cp+2) (char :: chars))
                  | char -> prestring (bp+1) (inc_cp cp char) (char :: chars)
            in prestring (bpos+1) (cpos+1) []
          | '{' -> prelex' ((ln, cpos, bpos, acc) :: ctx) (bpos+1) (cpos+1) []
          | '}' ->
            (match ctx with
               | ((sln, scpos, sbpos, sacc) :: ctx) ->
                 prelex' ctx (bpos+1) (cpos+1)
                         (Preblock ({file=file; line=sln; column=scpos},
                                    List.rev acc,
                                    {file=file; line=ln; column=(cpos + 1)})
                          :: sacc)
               | _ -> (prelexer_error {file=file; line=ln; column=cpos}
                                 "Unmatched closing brace";
                       prelex' ctx (bpos+1) (cpos+1) acc))
          | char ->                     (* A pretoken.  *)
            let rec pretok bp cp =
              if bp >= limit then
                nextline ctx (Pretoken ({file=file; line=ln; column=cpos},
                                        string_sub line bpos bp)
                              :: acc)
              else
                match line.[bp] with
                  | (' '|'\t'|'\n'|'\r'|'%'|'"'|'{'|'}' )
                    -> nexttok bp cp
                               (Pretoken ({file=file; line=ln; column=cpos},
                                          string_sub line bpos bp)
                                :: acc)
                  | char -> pretok (bp+1) (inc_cp cp char)
            in pretok (bpos+1) (inc_cp cpos char)
    in prelex' ctx 0 1 acc (* Traditionally, column numbers start at 1 :-(  *)
  with End_of_file ->
       match ctx with
         | [] -> List.rev acc
         | ((ln, cpos, _, _) :: ctx) ->
           (prelexer_error {file=file; line=ln; column=cpos}
                      "Unmatched opening brace"; List.rev acc)


let prelex_file file =
  let fin = open_in file
  in prelex file fin 1 [] []  (* Traditionally, line numbers start at 1 :-(  *)

(*  Since current implementation is not compatible with stream          *
 *  we write a temporary file and use this file as input.               *
 *  This is a terrible solution but for the things we do it does not    *
 *  really matters.  Plus it will make testing easier.                  *)
let prelex_string str =
    (* FIXME: we should use a proper temp file (e.g. with mktemp).  *)
    let fin = open_out "_temp_hack" in
        output_string fin str;
        (flush_all);
        close_out fin;
    let fin = open_in "_temp_hack" in
    prelex "string" fin 1 [] []

let rec pretokens_print pretokens =
  List.iter (fun pt ->
             print_string " ";
             match pt with
               | Preblock(_,pts,_)
                 -> print_string "{"; pretokens_print pts; print_string " }"
               | Pretoken(_, str) -> print_string str
               | Prestring(_, str)
                 -> print_string "\""; print_string str; print_string "\"")
            pretokens
