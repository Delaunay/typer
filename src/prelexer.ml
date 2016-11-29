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

let inc_cp (cp:charpos) (c:char) =
  (* Count char positions in utf-8: don't count the non-leading bytes.  *)
  if utf8_head_p c then cp+1 else cp

let rec prelex (file : string) (getline : unit -> string) ln ctx acc
        : pretoken list =
  try
    (* let fin = open_in file in *)
    let line = getline () in
    let limit = String.length line in
    let nextline = prelex file getline (ln + 1) in
    let rec prelex' ctx (bpos:bytepos) (cpos:charpos) acc =
      let nexttok = prelex' ctx in
      if bpos >= limit then nextline ctx acc else
        match line.[bpos] with
        | c when c <= ' ' -> nexttok (bpos+1) (cpos+1) acc
        | '%' -> nextline ctx acc      (* A comment.  *)
        | '"'                         (* A string.  *)
          -> let rec prestring bp cp chars =
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
        | '}'
          -> (match ctx with
             | ((sln, scpos, sbpos, sacc) :: ctx) ->
                prelex' ctx (bpos+1) (cpos+1)
                        (Preblock ({file=file; line=sln; column=scpos},
                                   List.rev acc,
                                   {file=file; line=ln; column=(cpos + 1)})
                         :: sacc)
             | _ -> (prelexer_error {file=file; line=ln; column=cpos}
                                   "Unmatched closing brace";
                    prelex' ctx (bpos+1) (cpos+1) acc))
        | char                  (* A pretoken.  *)
          -> let rec pretok bp cp =
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
                | '\\' when bp+1 < limit
                  -> let char = line.[bp + 1] in
                    pretok (bp + 2) (1 + inc_cp cp char)
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
  in prelex file (fun _ -> input_line fin)
            (* Traditionally, line numbers start at 1 :-(  *)
            1 [] []

let prelex_string str =
  let pos = ref 0 in
  let getline () =
    let start = !pos in
    if start >= String.length str then raise End_of_file else
      let i = try String.index_from str start '\n'
              with Not_found -> String.length str - 1 in
      let npos = i + 1 in
      pos := npos;
      let line = String.sub str start (npos - start) in
      (* print_string ("Read line: " ^ line); *)
      line
  in prelex "<string>" getline 1 [] []

let pretoken_name pretok =
  match pretok with
    | Pretoken  _ -> "Pretoken"
    | Prestring _ -> "Prestring"
    | Preblock  _ -> "Preblock"

let rec pretoken_string pretok =
    match pretok with
        | Preblock(_,pts,_) ->  "{" ^ (
            List.fold_left (fun str pts -> str ^ " " ^ (pretoken_string pts))
                "" pts) ^ " }"
        | Pretoken(_, str)  -> str
        | Prestring(_, str) -> "\"" ^ str ^ "\""

let pretokens_string pretokens =
  List.fold_left (fun str pt -> str ^ (pretoken_string pt)) "" pretokens


let pretokens_print p = print_string (pretokens_string p)


(* Prelexer comparison, ignoring source-line-number info, used for tests.  *)
let rec pretokens_equal p1 p2 = match p1, p2 with
  | Pretoken (_, s1), Pretoken (_, s2) -> s1 = s2
  | Prestring (_, s1), Prestring (_, s2) -> s1 = s2
  | Preblock (_, ps1, _), Preblock (_, ps2, _) ->
     pretokens_eq_list ps1 ps2
  | _ -> false
and pretokens_eq_list ps1 ps2 = match ps1, ps2 with
  | [], [] -> true
  | (p1 :: ps1), (p2 :: ps2) ->
     pretokens_equal p1 p2 && pretokens_eq_list ps1 ps2
  | _ -> false
