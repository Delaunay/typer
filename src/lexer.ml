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

(* FIXME: if we want to handle mixfix declarations such as "let _$_ x y =
   toto in a+1 $ b-2" we could make the "_$_" token (i.e. a simple lexical
   criteria) trigger the addition of corresponding syntax rules, but
   it seems hard to extend it so the precedence can also be specified
   because it is awkward to include the info in the lexical part, and as
   soon as we move into the syntactical part we get bitten by the fact that
   we don't know what the syntax means until we perform macroexpansion
   (i.e. much later).  *)

type token_env = bool array

let digit_p char =
  let code = Char.code char
  in Char.code '0' <= code && code <= Char.code '9'

type num_part = | NPint | NPfrac | NPexp

let nexttoken (stt : token_env) (pts : pretoken list) bpos cpos
    (* The returned Sexp may not be a Node.  *)
    : sexp * pretoken list * bytepos * charpos =
  match pts with
    | [] -> (internal_error "No next token!")
    | (Preblock (sl, bpts, el) :: pts) -> (Block (sl, bpts, el), pts, 0, 0)
    | (Prestring (loc, str) :: pts) -> (String (loc, str), pts, 0, 0)
    | (Pretoken ({file;line;column}, name) :: pts') ->
      if digit_p name.[bpos] then
        let rec lexnum bp cp (np : num_part) =
          if bp >= String.length name then
            ((if np == NPint then
                Integer ({file;line;column=column+bpos},
                         int_of_string (string_sub name bpos bp))
              else
                Float ({file;line;column=column+bpos},
                       float_of_string (string_sub name bpos bp))),
             pts', 0, 0)
          else
            match name.[bp] with
              | ('0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9')
                -> lexnum (bp+1) (cp+1) np
              | '.' when np == NPint -> lexnum (bp+1) (cp+1) NPfrac
              | ('e'|'E') when not (np == NPexp) -> lexnum (bp+1) (cp+1) NPexp
              | ('+'|'-')
                when np == NPexp && (name.[bp-1] == 'e' || name.[bp-1] == 'E') ->
                lexnum (bp+1) (cp+1) NPexp
              | _ ->
                ((if np == NPint then
                    Integer ({file;line;column=column+bpos},
                             int_of_string (string_sub name bpos bp))
                  else
                    Float ({file;line;column=column+bpos},
                           float_of_string (string_sub name bpos bp))),
                 pts, bp, cp)
        in lexnum (bpos+1) (cpos+1) NPint
      else if bpos + 1 >= String.length name then
        (hSymbol ({file;line;column=column+bpos},
                  string_sub name bpos (String.length name)),
         pts', 0, 0)
      else if stt.(Char.code name.[bpos])
              && not (name.[bpos+1] == '_') then
        (hSymbol ({file;line;column=column+bpos},
                  string_sub name bpos (bpos + 1)),
         pts, bpos+1, cpos+1)
      else
        let rec lexsym bp cp =
          if bp >= String.length name then
            (hSymbol ({file;line;column=column+bpos},
                      string_sub name bpos (String.length name)),
             pts', 0, 0)
          else
            let char = name.[bp] in
            if char == '_' then
              (* Skip next char, in case it's a special token.  *)
              (* For utf-8, this cp+2 is risky but actually works: _ counts
                    as 1 and if the input is valid utf-8 the next byte has to
                    be a leading byte, so it has to count as 1 as well ;-) *)
              lexsym (bp+2) (cp+2)
            else if stt.(Char.code name.[bp]) && (bp + 1 >= String.length name
                                                  || not (name.[bp+1] == '_')) then
              (hSymbol ({file;line;column=column+bpos},
                        string_sub name bpos bp),
               pts, bp, cp)
            else lexsym (bp+1) (inc_cp cp char)
        in lexsym bpos cpos

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

