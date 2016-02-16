(* pexp.ml --- Proto lambda-expressions, half-way between Sexp and Lexp.

Copyright (C) 2011-2012, 2015, 2016  Free Software Foundation, Inc.

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
open Sexp

(*************** The Pexp Parser *********************)

type arg_kind = Aexplicit | Aimplicit | Aerasable (* eraseable ⇒ implicit.  *)
type pvar = symbol
(* type sort = Type | Ext *)
(* type tag = string *)

type ppat =
  (* This data type allows nested patterns, but in reality we don't
   * support them.  I.e. we don't want Ppatcons within Ppatcons.  *)
  | Ppatany of location
  | Ppatvar of pvar
  (* FIXME: For modules and such, we'll want to generalize this
   * `pvar' to a pexp.  *)
  | Ppatcons of pvar * ((arg_kind * symbol) option * ppat) list

type pexp =
  (* | Psort of location * sort *)
  | Pimm of sexp                       (* Used for strings, ...  *)
  | Pvar of pvar
  | Phastype of location * pexp * pexp
  | Pmetavar of pvar
  | Plet of location * (pvar * pexp * bool) list * pexp
  | Parrow of arg_kind * pvar option * pexp * location * pexp
  | Plambda of arg_kind * pvar * pexp option * pexp
  | Pcall of pexp * sexp list           (* Curried call.  *)
  (* The symbols are only used so that we can distinguish two
   * otherwise isomorphic types.  *)
  | Pinductive of symbol * (arg_kind * pvar * pexp option) list
                  * (symbol * (arg_kind * pvar option * pexp) list) list
  | Pcons of pvar * symbol
  | Pcase of location * pexp * (ppat * pexp) list

let rec pexp_location e =
  match e with
  (* | Psort (l,_) -> l *)
  | Pimm s -> sexp_location s
  | Pvar (l,_) -> l
  | Phastype (l,_,_) -> l
  | Pmetavar (l, _) -> l
  | Plet (l, _, _) -> l
  | Parrow (_, _, _, l, _) -> l
  | Plambda (_,(l,_), _, _) -> l
  | Pcall (f, _) -> pexp_location f
  | Pinductive ((l,_), _, _) -> l
  | Pcons ((l,_),_) -> l
  | Pcase (l, _, _) -> l

let rec pexp_pat_location e = match e with
  | Ppatany l -> l
  | Ppatvar (l,_) -> l
  | Ppatcons ((l, _), _) -> l
  
(* In the following "pexp_p" the prefix for "parse a sexp, returning a pexp"
 * and "pexp_u" is the prefix for "unparse a pexp, returning a sexp".  *)
                       
let rec pexp_parse (s : sexp) : pexp =
  match s with
  (* This is an internal error because Epsilon does not have any location
   * information so it needs to be caught elsewhere.  *)
  | Epsilon -> (internal_error "Epsilon in pexp_parse")
  | (Block _ | Integer _ | Float _ | String _) -> Pimm s
  (* | Symbol (l, "Type") -> Psort (l, Type) *)
  | Symbol ((_, "_") as s) -> Pmetavar s
  | Symbol s -> Pvar s
  | Node (Symbol (start, "_:_"), [e; t])
    -> Phastype (start, pexp_parse e, pexp_parse t)
  (* let *)
  | Node (Symbol (start, "let_in_"), [decls; body])
    -> Plet (start, pexp_decls decls, pexp_parse body)
  | Node (Symbol (start, ("let_in_" | "let" | "let_")), _)
    -> msg_error start "Unrecognized let expression"; Pmetavar (start, "_")
  (* arrow *)
  | Node (Symbol (start, (("_->_" | "_=>_" | "_≡>_") as arw)), [t1; t2])
    -> let kind = (match arw with
                  | "_->_" -> Aexplicit | "_=>_" -> Aimplicit | _ -> Aerasable) in
      (match t1 with
       | Node (Symbol (_, "_:_"), [Symbol v; t1])
         -> Parrow (kind, Some v, pexp_parse t1, start, pexp_parse t2)
       | _ -> Parrow (kind, None, pexp_parse t1, start, pexp_parse t2))
  | Node (Symbol (start, ("_->_" | "_=>_" | "_≡>_")), _)
    -> msg_error start "Unrecognized arrow expression"; Pmetavar (start, "_")
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
             | _ -> msg_error start "Unrecognized lambda argument";
                   ((dummy_location, "unrecognized_arg"), None)
           in Plambda (kind, v, t, pbody))
        (sexp_p_list arg ["_:_"])
        (pexp_parse body)
  | Node (Symbol (start, "lambda_"), _)
    -> msg_error start "Unrecognized lambda expression"; Pmetavar (start, "_")
  (* inductive type *)
  | Node (Symbol (start, "inductive_"), t :: cases)
    -> let (name, args) = match t with
        | Node (Symbol s, args) -> (s, args)
        | Symbol s -> (s, [])
        | _ -> msg_error start "Unrecognized inductive type name";
              ((dummy_location, ""), []) in
      let pcases =
        List.fold_right
          (fun case pcases
           -> match case with
             | Node (Symbol s, cases)
               -> (s, List.map pexp_p_ind_arg cases)::pcases
             | _ -> msg_error (sexp_location case)
                             "Unrecognized constructor declaration"; pcases)
          cases [] in
      Pinductive (name, List.map pexp_parse args, pcases)
  | Node (Symbol (start, "inductive_"), _)
    -> msg_error start "Unrecognized inductive type"; Pmetavar (start, "_")
  (* constructor *)
  | Node (Symbol (start, "inductive-cons"), [Symbol tname; Symbol tag])
    -> Pcons (tname, tag)
  | Node (Symbol (start, "cons_"), _)
    -> msg_error start "Unrecognized constructor call"; Pmetavar (start, "_")
  (* cases analysis *)
  | Node (Symbol (start, "case_"),
          [Node (Symbol (_, "_|_"), e :: cases)])
    -> let parse_case branch = match branch with
        | Node (Symbol (_, "_=>_"), [pat; code])
          -> (pexp_p_pat pat, pexp_parse code)
        | _ -> let l = (sexp_location branch) in
              msg_error l "Unrecognized simple case branch";
              (Ppatany l, Pmetavar (l, "_"))
      in Pcase (start, pexp_parse e, List.map parse_case cases)
  | Node (Symbol (start, "case_"), [e]) -> Pcase (start, pexp_parse e, [])
  | Node (Symbol (start, "case_"), _)
    -> msg_error start "Unrecognized case expression"; Pmetavar (start, "_")
  (* | Node (Symbol (_, "(_)"), [e]) -> pexp_parse e *)
  | Node (f, []) -> pexp_parse f
  | Node (f, args) -> Pcall (pexp_parse f, args)

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
  | Node (Symbol (_, "_:-_"), [Symbol f; Symbol s])
    -> (Some (Aexplicit, f), Ppatvar s)
  | Node (Symbol (_, "_:=_"), [Symbol f; Symbol s])
    -> (Some (Aimplicit, f), Ppatvar s)
  | Node (Symbol (_, "_:≡_"), [Symbol f; Symbol s])
    -> (Some (Aerasable, f), Ppatvar s)
  | _ -> let loc = sexp_location s in
        msg_error loc "Unknown pattern arg";
        (None, Ppatany loc)

and pexp_u_pat_arg (arg : (arg_kind * symbol) option * ppat) : sexp =
  match arg with
  | (None, p) -> pexp_u_pat p
  | (Some (k, ((l,_) as n)), p) ->
     Node (Symbol (l, match k with Aexplicit -> "_:-_"
                                 | Aimplicit -> "_:=_"
                                 | Aerasable -> "_:≡_"),
           (* FIXME: the label is wrong!  *)
           [Symbol (pexp_u_id (Some n)); pexp_u_pat p])

and pexp_p_pat (s : sexp) : ppat = match s with
  | Symbol (l, "_") -> Ppatany l
  | Symbol s -> Ppatvar s
  | Node (Symbol c, args)
    -> Ppatcons (c, List.map pexp_p_pat_arg args)
  | _ -> let l = sexp_location s in
        msg_error l "Unknown pattern"; Ppatany l

and pexp_u_pat (p : ppat) : sexp = match p with
  | Ppatany l -> Symbol (l, "_")
  | Ppatvar s -> Symbol s
  | Ppatcons (c, args) -> Node (Symbol c, List.map pexp_u_pat_arg args)

and pexp_decls e =
  match e with
  | Epsilon -> []
  | Node (Symbol (_, ("_;_" | "_;" | ";_")), decls)
    -> List.concat (List.map pexp_decls decls)
  | Node (Symbol (_, "_:_"), [Symbol s; t]) -> [(s, pexp_parse t, true)]
  | Node (Symbol (_, "_=_"), [Symbol s; t]) -> [(s, pexp_parse t, false)]
  (* | Node (Symbol (_, "_=_"), [Node (Symbol s, args); t]) ->
   *   let rec mkfun args =
   *     match args with
   *     | [] -> pexp_parse t
   *     | (Symbol s :: args) -> Plambda (s, None, mkfun args)
   *     | (arg :: args) -> msg_error (sexp_location arg)
   *                                 "Unknown argument format";
   *                       mkfun args
   *   in [(s, mkfun args, false)] *)
  | _ -> msg_error (sexp_location e) ("Unknown declaration"); []

and pexp_unparse (e : pexp) : sexp =
  match e with
  (* | Psort (l,Ext) -> Symbol (l, "%Ext%") *)
  (* | Psort (l,Type) -> Symbol (l, "%Type%") *)
  | Pimm s -> s
  | Pvar v -> Symbol v
  | Pmetavar (l,name) -> Symbol (l,"?"^name)
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
  | Pinductive (_, t, branches) ->
    Node (Symbol (dummy_location, "inductive_"),
          sexp_u_list (List.map pexp_unparse t)
          :: List.map (fun ((l,name) as s, types)
                       -> Node (Symbol s,
                               List.map pexp_u_ind_arg types))
                      branches)
  | Pcons (tname, ((l,_) as tag)) ->
    Node (Symbol (l, "cons_"),
          [Symbol tname; Symbol tag])
  | Pcase (start, e, branches) ->
    Node (Symbol (start, "case_"),
          pexp_unparse e
          :: List.map
               (fun (pat, branch) ->
                 Node (Symbol (pexp_pat_location pat, "_=>_"),
                       [pexp_u_pat pat;
                        pexp_unparse branch]))
               branches)
and pexp_u_decl (s, v, declp) =
  Node (Symbol (dummy_location, if declp then "_:_" else "_=_"),
        [Symbol s; pexp_unparse v])
and pexp_u_decls ds =
  match ds with
  | [] -> Epsilon
  | [d] -> pexp_u_decl d
  | _ -> Node (Symbol (dummy_location, "_;_"),
              List.map pexp_u_decl ds)

let pexp_print e = sexp_print (pexp_unparse e)


