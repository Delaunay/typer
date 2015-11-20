(* sexp.ml --- The Lisp-style Sexp abstract syntax tree.

Copyright (C) 2011-2015  Free Software Foundation, Inc.

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

(* FIXME/TODO:
 * - Give more control over the way we strip parentheses.
 *   E.g. allow some infix operators to keep track whether their args where
 *   parenthesized or not.  Some uses may also want to "not-strip" parentheses
 *   so as to distinguish "((a b))" from "(a b)".
 * - Add another level of tokenizing/parsing: on the first level "M.a"
 *   can be parsed as one token, and then on the second level, it would
 *   turn into a call to "." with two arguments.  *)

open Util
open Prelexer

type integer = (* Num.num  *) int
type symbol = location * string

type sexp =                  (* Syntactic expression, kind of like Lisp.  *)
  | Epsilon
  | Block of location * pretoken list * location
  | Symbol of symbol
  | String of location * string
  | Integer of location * integer
  | Float of location * float
  | Node of sexp * sexp list

(**************** Hash-consing symbols *********************)

module SHash = Hashtbl.Make (struct type t = string
                                    let equal = (=)
                                    let hash = Hashtbl.hash
                             end)
let shash = SHash.create 1000
let hString (name) = try SHash.find shash name
                     with Not_found
                          -> SHash.add shash name name; name
let hSymbol (l, name) = Symbol (l, hString name)
(* let toplevel = hString "TopLevel" *)
let emptyString = hString ""

(*************** The Sexp Printer *********************)

let rec sexp_print sexp =
  match sexp with
    | Epsilon -> print_string "()"  (* "ε" *)
    | Block(_,pts,_) -> print_string "{"; pretokens_print pts; print_string " }"
    | Symbol(_, name) -> print_string name
    | String(_, str) -> print_string "\""; print_string str; print_string "\""
    | Integer(_, n) -> print_int n
    | Float(_, x) -> print_float x
    | Node(f, args) -> print_string "(";
                       sexp_print f;
                       List.iter (fun sexp -> print_string " "; sexp_print sexp)
                                 args;
                       print_string ")"

let rec sexp_location s =
  match s with
    | Block (l, _, _) -> l
    | Symbol (l, _) -> l
    | String (l, _) -> l
    | Integer (l, _) -> l
    | Float (l, _) -> l
    | Node (s, _) -> sexp_location s
    | Epsilon -> (internal_error "Looking for the location of Epsilon")

(*************** The Sexp Parser *********************)

(* FIXME: it should be possible to make something like "." bind tighter than
   function application.  *)
(* FIXME: what about sections, as in "if_then e1 else_"?  *)

module SMap
  = Map.Make (struct type t = string let compare = String.compare end)
type grammar = (int option * int option) SMap.t

(* If true, infix symbols like "_;_" will be turned into ";_" or "_;"
 *    if they had no right or left argument.
 * If false, "_;_" will stay as it is, and receive Epsilon arguments
 *    as appropriate.  *)
let empty_args_are_not_args = false

(* `op' is the operator being parsed.  E.g. for let...in...
 *      it would be either ["let"] or ["in";"let"] depending on which
 *      part we've parsed already.
 * `largs' are the args to the left of the latest infix; they belong to `op'.
 * `rargs' are the sexps that compose the arg to the right of the latest
 *      infix symbol.  They may belong to `op' or to a later infix operator
 *      we haven't seen yet which binds more tightly.  *)
let rec sexp_parse (g : grammar) (rest : sexp list)
                   (level : int)
                   (op : symbol list)
                   (largs : sexp list)
                   (rargs : sexp list)
        : (sexp * sexp list) =
  let sexp_parse = sexp_parse g in

  let rec compose_symbol (ss : symbol list) = match ss with
      | [] -> (internal_error "empty operator!")
      | (l,_)::_ -> (l, String.concat "_" (List.map (fun (_,s) -> s)
                                                   (List.rev ss))) in

  let push_largs largs rargs closer = match List.rev rargs with
      | [] -> if closer then Epsilon :: largs else largs
      | e::es -> (match es with [] -> e | _ -> Node (e, es)) :: largs in

  let mk_node op largs rargs closer =
    let args = List.rev (push_largs largs rargs closer) in
    match op with
      | [] -> (match args with [] -> Epsilon
                            | [e] -> e
                            | e::es -> Node (e, es))
      | ss -> let headname = compose_symbol ss in
             match (headname, args) with
             (* FIXME: While it's uaulyl good to strip away parens,
              * this makes assumptions about the grammar (i.e. there's
              * a rule « exp ::= '(' exp ')' » ), and this is sometimes
              * not desired (e.g. to distinguish "a b ⊢ c d" from
              * "(a b) ⊢ (c d)").  *)
             | ((_,"(_)"), [arg]) -> arg (* Strip away parens.  *)
             | _ -> Node (hSymbol (headname), args) in

  match rest with
  | (((Symbol ((l,name) as s)) as e)::rest') ->
    (try match SMap.find name g with
         | (None, None) -> sexp_parse rest' level op largs (e::rargs)
         | (None, Some rl)          (* Open paren or prefix.  *)
           -> let (e, rest) = sexp_parse rest' rl [s] [] []
             in sexp_parse rest level op largs (e::rargs)
         | (Some ll, _) when ll < level
           (* A symbol that closes the currently parsed element.  *)
           -> ((if empty_args_are_not_args then
                 mk_node (match rargs with [] -> op | _ -> ((l,"")::op))
                         largs rargs false
               else
                 mk_node ((l,"")::op) largs rargs true),
              rest)
         | (Some ll, None) when ll > level
           (* A closer without matching opener.
            * It might simply be a postfix symbol that binds very tightly.
            * We currently signal an error because it's more common for
            * it to be a closer with missing opener.  *)
           -> msg_error l ("Lonely postfix/closer \""^name^"\"");
             sexp_parse rest' level op largs
                        [mk_node [(l,name);(l,"")] [] rargs true]
         | (Some ll, Some rl) when ll > level
           (* A new infix which binds more tightly, i.e. does not close
            * the current `op' but takes its `rargs' instead.  *)
           -> let (e, rest)
               = if empty_args_are_not_args then
                   sexp_parse rest' rl
                              (match rargs with [] -> [s] | _ -> [s;(l,"")])
                              (push_largs [] rargs false) []
                 else
                   sexp_parse rest' rl [s;(l,"")]
                              (push_largs [] rargs true) []
             in sexp_parse rest level op largs [e]
         | (Some ll, Some rl)
           -> sexp_parse rest' rl
                        (if ll == rl
                            && match op with (_,name')::_ -> name = name'
                                          | _ -> false
                         then op else (s::op))
                        (push_largs largs rargs true) []
         | (Some ll, None)
           -> (mk_node (s::op) largs rargs true, rest')
     with Not_found ->
       sexp_parse rest' level op largs (e::rargs))
  | e::rest -> sexp_parse rest level op largs (e::rargs)
  | [] -> (mk_node (match rargs with [] -> op
                                  | _ -> ((dummy_location,"")::op))
                  largs rargs false,
          [])

let sexp_parse_all grm tokens limit =
  let level = match limit with
    | None -> min_int
    | Some token ->
      match SMap.find token grm with
      | (Some ll, Some _) -> ll + 1
      | _ -> (internal_error ("Can't find level of \""^token^"\""))
  in let (e, rest) = sexp_parse grm tokens level [] [] [] in
     let se = match e with
       | Node (Symbol (_, ""), [e]) -> e
       | Node (Symbol (_, ""), e::es) -> Node (e, es)
       | _ -> (internal_error "Didn't find a toplevel") in
     match rest with
     | [] -> (se,rest)
     | Symbol (_,t) :: rest when Some t = limit -> (se,rest)
     | _ -> (internal_error "Stopped parsing before the end!")

(* "sexp_p" is for "parsing" and "sexp_u" is for "unparsing".  *)

let sexp_p_list (s : sexp) (exceptions : string list) : sexp list =
  match s with
  | Epsilon -> []
  | Node (Symbol (_, head), tail) when List.mem head exceptions -> [s]
  | Node (head, tail)  -> head :: tail
  | _ -> [s]

let sexp_u_list (ss : sexp list) : sexp =
  match ss with
  | [] -> Epsilon
  | [s] -> s
  | (s :: ss) -> Node (s, ss)

