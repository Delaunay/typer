(* pexp.ml --- Proto lambda-expressions, half-way between Sexp and Lexp.

Copyright (C) 2011-2017  Free Software Foundation, Inc.

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
open Sexp   (* Symbol *)
open Lexer
open Grammar

let pexp_error = msg_error "PEXP"

(*************** The Pexp Parser *********************)

type arg_kind = Aexplicit | Aimplicit | Aerasable (* eraseable ⇒ implicit.  *)

(*  This is Dangerously misleading since pvar is NOT pexp but Pvar is *)
type pvar = symbol
(* type sort = Type | Ext *)
(* type tag = string *)

type pexp =
  (* | Psort of location * sort *)
  | Pimm of sexp                       (* Used for strings, ...  *)
  | Pbuiltin of symbol
  | Pvar of pvar
  | Phastype of location * pexp * pexp
  | Pmetavar of pvar
  | Plet of location * pdecl list * pexp
  | Parrow of arg_kind * pvar option * pexp * location * pexp
  | Plambda of arg_kind * pvar * pexp option * pexp
  | Pcall of pexp * sexp list           (* Curried call.  *)
  (* The symbols are only used so that we can distinguish two
   * otherwise isomorphic types.  *)
  | Pcase of location * pexp * (ppat * pexp) list

and ppat =
  (* This data type allows nested patterns, but in reality we don't
   * support them.  I.e. we don't want Ppatcons within Ppatcons.  *)
  | Ppatany of location
  | Ppatsym of pvar (* A named default pattern, or a 0-ary constructor.  *)
  | Ppatcons of pexp * (symbol option * ppat) list

and pdecl =
  | Ptype of symbol * pexp        (* identifier : expr  *)
  | Pexpr of symbol * pexp        (* identifier = expr  *)
  | Pmcall of symbol * sexp list  (* identifier [sexp]  *)


let rec pexp_location e =
  match e with
  (* | Psort (l,_) -> l *)
  | Pimm s -> sexp_location s
  | Pbuiltin (l,_) -> l
  | Pvar (l,_) -> l
  | Phastype (l,_,_) -> l
  | Pmetavar (l, _) -> l
  | Plet (l, _, _) -> l
  | Parrow (_, _, _, l, _) -> l
  | Plambda (_,(l,_), _, _) -> l
  | Pcall (f, _) -> pexp_location f
  | Pcase (l, _, _) -> l

let pexp_name e =
  match e with
  | Pimm _           -> "Pimm"
  | Pbuiltin _       -> "Pbuiltin"
  | Pvar (_,_)       -> "Pvar"
  | Phastype (_,_,_) -> "Phastype"
  | Pmetavar (_, _)  -> "Pmetavar"
  | Plet (_, _, _)   -> "Plet"
  | Parrow (_, _, _, _, _)   -> "Parrow"
  | Plambda (_,(_,_), _, _)  -> "Plambda"
  | Pcall (_, _)             -> "Pcall"
  | Pcase (_, _, _) -> "Pcase"

let rec pexp_pat_location e = match e with
  | Ppatany l -> l
  | Ppatsym (l,_) -> l
  | Ppatcons (e, _) -> pexp_location e

(* In the following "pexp_p" the prefix for "parse a sexp, returning a pexp"
 * and "pexp_u" is the prefix for "unparse a pexp, returning a sexp".  *)
let rec pexp_parse (s : sexp) : pexp =
  match s with
  (* This is an internal error because Epsilon does not have any location
   * information so it needs to be caught elsewhere.  *)
  | (Block _ | Integer _ | Float _ | String _) -> Pimm s
  (* | Symbol (l, "Type") -> Psort (l, Type) *)
  | Symbol (l, name) when String.length name > 0 && String.get name 0 == '?'
    -> Pmetavar (l, String.sub name 1 (String.length name - 1))
  | Symbol (l, name) when String.length name > 2
                          && String.get name 0 == '#'
                          && String.get name 1 == '#'
    -> Pbuiltin (l, string_sub name 2 (String.length name))
  (* | Node (Symbol (start, "##"), [Symbol s])
   *   -> Pbuiltin s
   * | Node (Symbol (start, "##"), [e])
   *   -> pexp_error (sexp_location e) "Non-symbol argument to `##`";
   *     Pmetavar (start, "")
   * | Node (Symbol (start, "##"), _)
   *   -> pexp_error start "`##` takes exactly one argument";
   *     Pmetavar (start, "") *)
  | Symbol s -> Pvar s
  | Node (Symbol (start, "_:_"), [e; t])
    -> Phastype (start, pexp_parse e, pexp_parse t)
  (* let *)
  | Node (Symbol (start, "let_in_"), [decls; body])
    -> Plet (start, pexp_p_decls decls, pexp_parse body)
  | Node (Symbol (start, ("let_in_" | "let" | "let_")), _)
    -> pexp_error start "Unrecognized let expression"; Pmetavar (start, "_")
  (* arrow *)
  | Node (Symbol (start, (("_->_" | "_=>_" | "_≡>_") as arw)), [t1; t2])
    -> let kind = (match arw with
                  | "_->_" -> Aexplicit | "_=>_" -> Aimplicit | _ -> Aerasable) in
      (match t1 with
       | Node (Symbol (_, "_:_"), [Symbol v; t1])
         -> Parrow (kind, Some v, pexp_parse t1, start, pexp_parse t2)
       | _ -> Parrow (kind, None, pexp_parse t1, start, pexp_parse t2))
  | Node (Symbol (start, ("_->_" | "_=>_" | "_≡>_")), _)
    -> pexp_error start "Unrecognized arrow expression"; Pmetavar (start, "_")
  (* lambda *)
  | Node (Symbol (start,(("lambda_->_" | "lambda_=>_" | "lambda_≡>_") as arw)),
          [arg; body])
    -> let kind = match arw with
        | "lambda_->_" -> Aexplicit | "lambda_=>_" -> Aimplicit
        | _ -> Aerasable in
      List.fold_right
        (fun arg pbody
         -> let (v, t) = match arg with
             | Symbol v -> (v, None)
             | Node (Symbol (_, "_:_"), [Symbol v; t])
               -> (v, Some (pexp_parse t))
             | _ -> pexp_error start "Unrecognized lambda argument";
                   ((dummy_location, "unrecognized_arg"), None)
           in Plambda (kind, v, t, pbody))
        (sexp_p_list arg ["_:_"])
        (pexp_parse body)
  | Node (Symbol (start, "lambda_"), _)
    -> pexp_error start "Unrecognized lambda expression"; Pmetavar (start, "_")
  (* cases analysis *)
  | Node (Symbol (start, "case_"),
          [Node (Symbol (_, "_|_"), e :: cases)])
    -> let parse_case branch = match branch with
        | Node (Symbol (_, "_=>_"), [pat; code])
          -> (pexp_p_pat pat, pexp_parse code)
        | _ -> let l = (sexp_location branch) in
              pexp_error l "Unrecognized simple case branch";
              (Ppatany l, Pmetavar (l, "_"))
      in Pcase (start, pexp_parse e, List.map parse_case cases)
  | Node (Symbol (start, "case_"), [e]) -> Pcase (start, pexp_parse e, [])
  | Node (Symbol (start, "case_"), _)
    -> pexp_error start "Unrecognized case expression"; Pmetavar (start, "_")
  (* | Node (Symbol (_, "(_)"), [e]) -> pexp_parse e *)
  | Node (f, []) -> pexp_parse f
  | Node (f, args) -> Pcall (pexp_parse f, args)

and pexp_p_actual_arg arg : (arg_kind * pvar option * pexp) =
  match arg with
  | Node (Symbol (_, ":≡"), [Symbol s; e])
    -> (Aerasable, Some s, pexp_parse e)
  | Node (Symbol (_, ":="), [Symbol s; e])
    -> (Aimplicit, Some s, pexp_parse e)
  | Node (Symbol (_, ":-"), [Symbol s; e])
    -> (Aexplicit, Some s, pexp_parse e)
  | e -> (Aexplicit, None, pexp_parse e)

and pexp_p_formal_arg arg : (arg_kind * pvar * pexp option) =
  match arg with
  | Node (Symbol (_, "_:::_"), [Symbol s; e])
    -> (Aerasable, s, Some (pexp_parse e))
  | Node (Symbol (_, "_::_"), [Symbol s; e])
    -> (Aimplicit, s, Some (pexp_parse e))
  | Node (Symbol (_, "_:_"), [Symbol s; e])
    -> (Aexplicit, s, Some (pexp_parse e))
  | Symbol s -> (Aexplicit, s, None)
  | _ -> sexp_print arg;
        (pexp_error (sexp_location arg) "Unrecognized formal arg");
         (Aexplicit, (sexp_location arg, "{arg}"), None)

and pexp_u_formal_arg (arg : arg_kind * pvar * pexp option) =
  match arg with
  | (Aexplicit, s, None) -> Symbol s
  | (ak, ((l,_) as s), t)
    -> Node (Symbol (l, match ak with Aerasable -> ":::"
                                   | Aimplicit -> "::"
                                   | Aexplicit -> ":"),
            [Symbol s; match t with Some e -> pexp_unparse e
                                  | None -> Symbol (l, "_")])

and pexp_p_id (x : location * string) : (location * string) option =
  match x with
  | (_, "_") -> None
  | _ -> Some x

and pexp_u_id (x : (location * string) option) : (location * string) =
  match x with
  | None -> (dummy_location, "_")
  | Some x -> x

and pexp_p_ind_arg s = match s with
  | Node (Symbol (_,"_:_"), [Symbol s; t])
    -> (Aexplicit, pexp_p_id s, pexp_parse t)
  | Node (Symbol (_,"_::_"), [Symbol s; t])
    -> (Aimplicit, pexp_p_id s, pexp_parse t)
  | Node (Symbol (_,"_:::_"), [Symbol s; t])
    -> (Aerasable, pexp_p_id s, pexp_parse t)
  | _ -> (Aexplicit, None, pexp_parse s)

and pexp_u_ind_arg arg = match arg with
  | (Aexplicit, None, t) -> pexp_unparse t
  | (k, s, t)
    -> let (l,_) as id = pexp_u_id s in
      Node (Symbol (l, match k with Aexplicit -> "_:_"
                                  | Aimplicit -> "_::_"
                                  | Aerasable -> "_:::_"),
            [Symbol id; pexp_unparse t])

and pexp_p_pat_arg (s : sexp) = match s with
  | Symbol _ -> (None, pexp_p_pat s)
  | Node (Symbol (_, "_:=_"), [Symbol f; Symbol s])
    -> (Some f, Ppatsym s)
  | _ -> let loc = sexp_location s in
        pexp_error loc "Unknown pattern arg";
        (None, Ppatany loc)

and pexp_u_pat_arg (arg : symbol option * ppat) : sexp =
  match arg with
  | (None, p) -> pexp_u_pat p
  | (Some ((l,_) as n), p) ->
     Node (Symbol (l, "_:=_"),
           (* FIXME: the label is wrong!  *)
           [Symbol (pexp_u_id (Some n)); pexp_u_pat p])

and pexp_p_pat (s : sexp) : ppat = match s with
  | Symbol (l, "_") -> Ppatany l
  | Symbol s -> Ppatsym s
  | Node (c, args)
    -> Ppatcons (pexp_parse c, List.map pexp_p_pat_arg args)
  | _ -> let l = sexp_location s in
        pexp_error l "Unknown pattern"; Ppatany l

and pexp_u_pat (p : ppat) : sexp = match p with
  | Ppatany l -> Symbol (l, "_")
  | Ppatsym s -> Symbol s
  | Ppatcons (c, args) -> Node (pexp_unparse c, List.map pexp_u_pat_arg args)

and pexp_p_decls e: pdecl list =
  match e with
  | Symbol (_, "") -> []
  | Node (Symbol (_, ("_;_" | "_;" | ";_")), decls)
    -> List.concat (List.map pexp_p_decls decls)
  | Node (Symbol (_, "_:_"), [Symbol s; t]) -> [Ptype(s, pexp_parse t)]
  | Node (Symbol (_, "_=_"), [Symbol s; t]) -> [Pexpr(s, pexp_parse t)]
  | Node (Symbol (_, "_=_"), [Node (Symbol s, args); t]) ->
      let rec mkfun args =
        match args with
        | [] -> pexp_parse t  (* Plambda of arg_kind * pvar * pexp option * pexp *)
        | (Symbol s :: args) -> Plambda(Aexplicit, s, None, mkfun args)
        | (arg :: args) -> pexp_error (sexp_location arg)
                                    "Unknown argument format";
                          mkfun args
      in [Pexpr(s, mkfun args)]
  (* everything else is considered a macro
   * An error will be produced during lexp_parsing if the macro does not exist
   * once expanded the Pmcall macro will produce a list of pdecl        *)
  | Node (Symbol (l, op), args) -> [Pmcall((l, op), args)]
  | _ ->
    print_string ((sexp_name e) ^ ": \""); sexp_print e; print_string "\"\n";
    pexp_error (sexp_location e) ("Unknown declaration"); []

and pexp_unparse (e : pexp) : sexp =
  match e with
  (* | Psort (l,Ext) -> Symbol (l, "%Ext%") *)
  (* | Psort (l,Type) -> Symbol (l, "%Type%") *)
  | Pimm s -> s
  | Pbuiltin (l,name) -> Symbol (l, "##" ^ name)
  (* | Pbuiltin ((l,_) as s) -> Node (Symbol (l, "##"), [Symbol s]) *)
  | Pvar v -> Symbol v
  | Pmetavar (l,name) -> Symbol (l, "?" ^ name)
  | Phastype (l,e,t)
    -> Node (Symbol (l, "_:_"), [pexp_unparse e; pexp_unparse t])
  | Plet (start, decls, body) ->
    Node (Symbol (start, "let_in_"),
          [pexp_u_decls decls; pexp_unparse body])
  | Parrow (kind, arg, t1, l, t2) ->
    let ut1 = pexp_unparse t1 in
    Node (Symbol (l, match kind with Aexplicit -> "_->_"
                                   | Aimplicit -> "_=>_"
                                   | Aerasable -> "_≡>_"),
          [(match arg with None -> ut1
                         | Some v -> Node (Symbol (l, "_:_"), [Symbol v; ut1]));
           pexp_unparse t2])
  | Plambda (ak, v, t, body) ->
    Node (Symbol (dummy_location, match ak with
                                  | Aexplicit -> "lambda_->_"
                                  | Aimplicit -> "lambda_=>_"
                                  | Aerasable -> "lambda_≡>_"),
          [(match t with None -> Symbol v
                       | Some t -> Node (Symbol (dummy_location, "_:_"),
                                         [Symbol v; pexp_unparse t]));
           pexp_unparse body])
  | Pcall (f, args) -> Node (pexp_unparse f, args)
  | Pcase (start, e, branches) ->
    Node (Symbol (start, "case_"),
          pexp_unparse e
          :: List.map
               (fun (pat, branch) ->
                 Node (Symbol (pexp_pat_location pat, "_=>_"),
                       [pexp_u_pat pat;
                        pexp_unparse branch]))
               branches)

and pexp_u_decl decl =
  match decl with
    | Pexpr (s, v) ->
      Node (Symbol (dummy_location, "_=_"), [Symbol s; pexp_unparse v])

    | Ptype (s, v) ->
      Node (Symbol (dummy_location, "_:_"), [Symbol s; pexp_unparse v])

    | Pmcall(s, args) ->
      Node (Symbol s, args)

and pexp_u_decls (ds: pdecl list) =
  match ds with
  | [] -> dummy_epsilon
  | [d] -> pexp_u_decl d
  | _ -> Node (Symbol (dummy_location, "_;_"),
              List.map pexp_u_decl ds)

and pexp_string e = sexp_string (pexp_unparse e)
and pexp_print e = print_string (pexp_string e)

(* Parse All Pexp as a list *)
let pexp_parse_all (nodes: sexp list) =
    List.map pexp_parse nodes

let pexp_decls_all (nodes: sexp list): pdecl list =
    let rec loop nodes acc =
        match nodes with
            | [] -> acc
            | hd::tl ->
                let r = pexp_p_decls hd in
                let nacc = List.append acc r in
                    loop tl nacc in
    loop nodes []

(*      String Parsing
 * --------------------------------------------------------- *)

(* Lexp helper *)
let _pexp_expr_str (str: string) (tenv: token_env)
            (grm: grammar) (limit: string option) =
    let sxps = _sexp_parse_str str tenv grm limit in
        pexp_parse_all sxps

(* specialized version *)
let pexp_expr_str str =
    _pexp_expr_str str default_stt default_grammar (Some ";")

let _pexp_decl_str (str: string) tenv grm limit =
    let sxps = _sexp_parse_str str tenv grm limit in
        pexp_decls_all sxps

(* specialized version *)
let pexp_decl_str str =
    _pexp_decl_str str default_stt default_grammar (Some ";")

