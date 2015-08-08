(* pexp.ml --- Proto lambda-expressions, half-way between Sexp and Lexp.

Copyright (C) 2011-2012  Free Software Foundation, Inc.

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
  | Pinductive of pexp * (symbol * pexp) list
  | Pcons of pvar * symbol
  | Pcase of location * pexp
             (* FIXME: For modules and such, we'll want to generalize this
              * `symbol' to a pexp.  *)
             * (symbol * (arg_kind * pvar) list * pexp) list
             * pexp option              (* Default.  *)

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
  | Pinductive (t, _) -> pexp_location t
  | Pcons ((l,_),_) -> l
  | Pcase (l, _, _, _) -> l
                           
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
    -> let (v,t) = match arg with
        | Symbol v -> (v, None)
        | Node (Symbol (_, "_:_"), [Symbol v; t])
          -> (v, Some (pexp_parse t))
        | _ -> msg_error start "Unrecognized lambda argument";
              ((dummy_location, "unrecognized_arg"), None)
      in Plambda ((match arw with
                   | "lambda_->_" -> Aexplicit | "lambda_=>_" -> Aimplicit
                   | _ -> Aerasable),
                  v, t, pexp_parse body)
  | Node (Symbol (start, "lambda_"), _)
    -> msg_error start "Unrecognized lambda expression"; Pmetavar (start, "_")
  (* inductive type *)
  | Node (Symbol (start, "inductive_"), t :: cases)
    -> let pcases
        = List.fold_right
            (fun case pcases
             -> match case with
               | Node (Symbol (_, "_:_"), [Symbol s; case])
                 -> (s, pexp_parse case)::pcases
               | _ -> msg_error (sexp_location case)
                               "Unrecognized constructor declaration"; pcases)
            cases [] in
      Pinductive (pexp_parse t, pcases)
  | Node (Symbol (start, "inductive_"), _)
    -> msg_error start "Unrecognized inductive type"; Pmetavar (start, "_")
  (* constructor *)
  | Node (Symbol (start, "cons_"), [Symbol tname; Symbol tag])
    -> Pcons (tname, tag)
  | Node (Symbol (start, "cons_"), _)
    -> msg_error start "Unrecognized constructor call"; Pmetavar (start, "_")
  (* cases analysis *)
  | Node (Symbol (start, "case_"), e :: cases)
    -> let parse_case c branches =
        match c with
        | Node (Symbol (_, "_=>_"), [Symbol tag; branch])
          -> (tag, [], pexp_parse branch) :: branches
        | Node (Symbol (_, "_=>_"), [Node (Symbol tag, args); branch])
          -> (tag,
             List.map (fun arg -> match arg with
                               | Symbol arg -> (Aexplicit, arg)
                               | _ -> let loc = sexp_location arg in
                                     msg_error loc "Non-trivial pattern arg";
                                     (Aexplicit, (loc, "_")))
                      args,
             pexp_parse branch) :: branches
        | _ -> msg_error (sexp_location c) "Unrecognized simple case branch";
              branches
      in (match List.rev cases with
          | (Node (Symbol (_, "_=>_"), [Symbol (_, "_"); default])) :: revcases
            -> Pcase (start, pexp_parse e,
                     List.fold_right parse_case (List.rev revcases) [],
                     Some (pexp_parse default))
          | _ -> Pcase (start, pexp_parse e,
                       List.fold_right parse_case cases [], None))
  | Node (Symbol (start, "case_"), _)
    -> msg_error start "Unrecognized case expression"; Pmetavar (start, "_")
  (* | Node (Symbol (_, "(_)"), [e]) -> pexp_parse e *)
  | Node (f, []) -> pexp_parse f
  | Node (f, args) -> Pcall (pexp_parse f, args)

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

let rec pexp_unparse (e : pexp) : sexp =
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
          [pexp_undecls decls; pexp_unparse body])
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
  | Pinductive (t, branches) ->
    Node (Symbol (dummy_location, "inductive_"),
          pexp_unparse t :: List.map (fun ((l,name) as s,case)
                                      -> Node (Symbol (l,"_:_"),
                                              [Symbol s; (pexp_unparse case)]))
                                     branches)
  | Pcons (tname, ((l,_) as tag)) ->
    Node (Symbol (l, "cons_"),
          [Symbol tname; Symbol tag])
  | Pcase (start, e, branches, default) ->
    Node (Symbol (start, "case_"),
          pexp_unparse e
          :: List.append
               (List.map (fun (((l,_) as tag), args, branch) ->
                          Node (Symbol (l, "_=>_"),
                                [(match args with
                                  | [] -> Symbol tag
                                  | _ -> Node (Symbol tag,
                                              List.map (fun (Aexplicit, a)
                                                        -> Symbol a)
                                                       args));
                                 pexp_unparse branch]))
                         branches)
               (match default with
                | None -> []
                | Some e ->
                  [Node (Symbol (dummy_location, "_=>_"),
                         [Symbol (dummy_location, "_");
                          pexp_unparse e])]))
and pexp_undecl (s, v, declp) =
  Node (Symbol (dummy_location, if declp then "_:_" else "_=_"),
        [Symbol s; pexp_unparse v])
and pexp_undecls ds =
  match ds with
  | [] -> Epsilon
  | [d] -> pexp_undecl d
  | _ -> Node (Symbol (dummy_location, "_;_"),
              List.map pexp_undecl ds)

let pexp_print e = sexp_print (pexp_unparse e)


