(* lexer.ml --- Second half of lexical analysis of Typer.

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
open Prelexer
open Sexp
open Grammar

(*************** The Lexer phase *********************)

let digit_p char =
  let code = Char.code char
  in Char.code '0' <= code && code <= Char.code '9'

type num_part = | NPint | NPfrac | NPexp

let unescape str =
  let rec split b =
    if b >= String.length str then []
    else let e = try String.index_from str b '\\'
                 with Not_found -> String.length str in
         String.sub str b (e - b) :: split (e + 1)
  in String.concat "" (split 0)

let nexttoken (stt : token_env) (pts : pretoken list) bpos cpos
    (* The returned Sexp may not be a Node.  *)
    : sexp * pretoken list * bytepos * charpos =
  match pts with
  | [] -> (internal_error "No next token!")
  | (Preblock (sl, bpts, el) :: pts) -> (Block (sl, bpts, el), pts, 0, 0)
  | (Prestring (loc, str) :: pts) -> (String (loc, str), pts, 0, 0)
  | (Pretoken ({file;line;column}, name) :: pts')
    -> if digit_p name.[bpos] then
        let rec lexnum bp cp (np : num_part) =
          if bp >= String.length name then
            ((if np == NPint then
                Integer ({file;line;column=column+cpos},
                         int_of_string (string_sub name bpos bp))
              else
                Float ({file;line;column=column+cpos},
                       float_of_string (string_sub name bpos bp))),
             pts', 0, 0)
          else
            match name.[bp] with
            | ('0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9')
              -> lexnum (bp+1) (cp+1) np
            | '.' when np == NPint -> lexnum (bp+1) (cp+1) NPfrac
            | ('e'|'E') when not (np == NPexp) -> lexnum (bp+1) (cp+1) NPexp
            | ('+'|'-')
                 when np == NPexp && (name.[bp-1] == 'e' || name.[bp-1] == 'E')
              -> lexnum (bp+1) (cp+1) NPexp
            | _
              -> ((if np == NPint then
                    Integer ({file;line;column=column+cpos},
                             int_of_string (string_sub name bpos bp))
                  else
                    Float ({file;line;column=column+cpos},
                           float_of_string (string_sub name bpos bp))),
                 pts, bp, cp)
        in lexnum (bpos+1) (cpos+1) NPint
      else if bpos + 1 >= String.length name then
        (hSymbol ({file;line;column=column+cpos},
                  string_sub name bpos (String.length name)),
         pts', 0, 0)
      else if stt.(Char.code name.[bpos]) = CKseparate then
        (hSymbol ({file;line;column=column+cpos},
                  string_sub name bpos (bpos + 1)),
         pts, bpos+1, cpos+1)
      else
        let mksym epos escaped
          = let rawstr = string_sub name bpos epos in
            let str = if escaped then unescape rawstr else rawstr in
            hSymbol ({file;line;column=column+cpos}, str) in
        let rec lexsym bp cp escaped =
          if bp >= String.length name then
            (mksym (String.length name) escaped, pts', 0, 0)
          else
            let char = name.[bp] in
            if char == '\\' && bp + 1 < String.length name then
              (* Skip next char, in case it's a special token.  *)
              (* For utf-8, this cp+2 is risky but actually works: \ counts
               * as 1 and if the input is valid utf-8 the next byte has to
               * be a leading byte, so it has to count as 1 as well ;-)  *)
              lexsym (bp+2) (cp+2) true
            else if stt.(Char.code name.[bp]) = CKseparate then
              (mksym bp escaped, pts, bp, cp)
            else lexsym (bp+1) (inc_cp cp char) escaped
        in lexsym bpos cpos false

let lex tenv (pts : pretoken list) : sexp list =
  let rec gettokens pts bpos cpos acc =
    match pts with
    | [] -> List.rev acc
    | _ -> let (tok, pts, bpos, cpos) = nexttoken tenv pts bpos cpos
          in gettokens pts bpos cpos (tok :: acc) in
  gettokens pts 0 0 []

let _lex_str (str: string) tenv =
    let pretoks = prelex_string str in
        lex tenv pretoks

let lex_str str = _lex_str str default_stt

let _sexp_parse_str (str: string) tenv grm limit =
    let toks = _lex_str str tenv in
        sexp_parse_all_to_list grm toks limit

let sexp_parse_str str =
    _sexp_parse_str str default_stt default_grammar (Some ";")

