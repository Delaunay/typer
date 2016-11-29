(* unification.ml --- Unification of Lexp terms

Copyright (C) 2016  Free Software Foundation, Inc.

Author: Vincent Bonnevalle <tiv.crb@gmail.com>

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

(* FIXME: Needs occurs-check.
 * Also needs to add a notion of scope-level, as described in
 * http://okmij.org/ftp/ML/generalization.html (aka ranks in
 * ftp://ftp.inria.fr/INRIA/Projects/cristal/Didier.Remy/eq-theory-on-types.ps.gz)
 *)

open Lexp
(* open Sexp *)
(* open Inverse_subst *)
module OL = Opslexp
module DB = Debruijn

(** Provide unify function for unifying two Lambda-Expression *)

(* :-( *)
let global_last_metavar = ref (-1) (*The first metavar is 0*)

let create_metavar () = global_last_metavar := !global_last_metavar + 1;
                        !global_last_metavar

(* For convenience *)
type return_type = (meta_subst * constraints) option

(** Alias for VMap.add*)
let associate (meta: int) (lxp: lexp) (subst: meta_subst)
  : meta_subst =
  (VMap.add meta lxp subst)

(** If key is in map returns the value associated
 else returns <code>None</code>
*)
let find_or_none (value: lexp) (map: meta_subst) : lexp option =
  match value with
  | Metavar (idx, _, _, _)
    -> if VMap.mem idx map
      then Some (VMap.find idx map)
      else None
  | _ -> None

(**
 lexp is equivalent to _ in ocaml
 (Let , lexp) == (lexp , Let)
 UNIFY      -> recursive call or dispatching
 OK         -> add a substituion to the list of substitution
 CONSTRAINT -> returns a constraint
*)

let unify_and res op = match res with
  | None -> None
  | Some (subst, constraints1)
    -> match op subst with
      | None -> None
      | Some (subst, constraints2) -> Some (subst, constraints2@constraints1)

(****************************** Top level unify *************************************)

(** Dispatch to the right unifyer.

 If (<code>_unify_X X Y</code>) don't handle the case <b>(X, Y)</b>, it call (<code>unify Y X</code>)

 The metavar unifyer is the end rule, it can't call unify with it's parameter (changing their order)
*)
let rec unify (e1: lexp) (e2: lexp)
              (ctx : DB.lexp_context) (subst: meta_subst)
        : return_type =
  unify' e1 e2 ctx OL.set_empty subst

and unify' (e1: lexp) (e2: lexp)
           (ctx : DB.lexp_context) (vs : OL.set_plexp) (subst: meta_subst)
    : return_type =
  let e1' = OL.lexp_whnf e1 ctx subst in
  let e2' = OL.lexp_whnf e2 ctx subst in
  let changed = not (e1 == e1' && e2 == e2') in
  if changed && OL.set_member_p subst vs e1' e2' then Some (subst, []) else
  let vs' = if changed then OL.set_add vs e1' e2' else vs in
  match (e1', e2') with
    | ((Imm _, Imm _) | (Cons _, Cons _) | (Builtin _, Builtin _)
       | (Var _, Var _) |  (Inductive _, Inductive _))
      -> if OL.conv_p subst ctx e1' e2' then Some (subst, []) else None
    | (l, (Metavar _ as r)) -> _unify_metavar  r l subst
    | (l, (Call _ as r))    -> _unify_call     r l ctx vs' subst
    (* | (l, (Case _ as r))    -> _unify_case     r l subst *)
    | (Arrow _ as l, r)     -> _unify_arrow    l r ctx vs' subst
    | (Lambda _ as l, r)    -> _unify_lambda   l r ctx vs' subst
    | (Metavar _ as l, r)   -> _unify_metavar  l r subst
    | (Call _ as l, r)      -> _unify_call     l r ctx vs' subst
    (* | (Case _ as l, r)      -> _unify_case     l r subst *)
    (* | (Inductive _ as l, r) -> _unify_induct   l r subst *)
    | (Sort _ as l, r)      -> _unify_sort     l r ctx vs' subst
    | (SortLevel _ as l, r) -> _unify_sortlvl  l r ctx vs' subst
    | _ -> Some (subst,
                if OL.conv_p subst ctx e1' e2' then [] else [(e1, e2)])

(********************************* Type specific unify *******************************)

(** Unify a Arrow and a lexp if possible
 - (Arrow, Arrow) -> if var_kind = var_kind
                     then unify ltype & lexp (Arrow (var_kind, _, ltype, lexp))
                     else None
 - (Arrow, Var) -> Constraint
 - (_, _) -> None
*)
and _unify_arrow (arrow: lexp) (lxp: lexp) ctx vs (subst: meta_subst)
  : return_type =
  match (arrow, lxp) with
  | (Arrow (var_kind1, v1, ltype1, _, lexp1),
     Arrow (var_kind2, _, ltype2, _, lexp2))
    -> if var_kind1 = var_kind2
      then unify_and (unify' ltype1 ltype2  ctx vs subst)
                     (unify' lexp1 lexp2
                             (DB.lexp_ctx_cons ctx 0 v1 Variable ltype1)
                             (OL.set_shift vs))
      else None
  | (Arrow _, Imm _) -> None
  | (Arrow _, Var _) -> Some (subst, [(arrow, lxp)])
  | (Arrow _, _) -> unify' lxp arrow ctx vs subst
  | (_, _) -> None

(** Unify a Lambda and a lexp if possible
 - Lamda     , Lambda             -> if var_kind = var_kind
                                     then UNIFY ltype & lxp else ERROR
 - Lambda    , Var                -> CONSTRAINT
 - Lambda    , Call               -> Constraint
 - Lambda    , Let                -> Constraint
 - Lambda    , lexp               -> unify lexp lambda subst
*)
and _unify_lambda (lambda: lexp) (lxp: lexp) ctx vs (subst: meta_subst) : return_type =
  match (lambda, lxp) with
  | (Lambda (var_kind1, v1, ltype1, lexp1),
     Lambda (var_kind2, _, ltype2, lexp2))
    -> if var_kind1 = var_kind2
      then unify_and (unify' ltype1 ltype2  ctx vs subst)
                     (unify' lexp1 lexp2
                             (DB.lexp_ctx_cons ctx 0 (Some v1) Variable ltype1)
                             (OL.set_shift vs))
      else None
  | (Lambda _, Var _)   -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Let _)   -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Arrow _) -> None
  | (Lambda _, Call _)  -> Some ((subst, [(lambda, lxp)]))
  | (Lambda _, Imm _)   -> None
  | (Lambda _, _)       -> unify' lxp lambda ctx vs subst
  | (_, _)              -> None

(** Unify a Metavar and a lexp if possible
 - lexp      , {metavar <-> none} -> UNIFY
 - lexp      , {metavar <-> lexp} -> UNFIFY lexp subst[metavar]
 - metavar   , metavar            -> if Metavar = Metavar then OK else ERROR
 - metavar   , lexp               -> OK
*)
and _unify_metavar (meta: lexp) (lxp: lexp) (subst: meta_subst) : return_type =
  let find_or_unify metavar value lxp s =
    match find_or_none metavar s with
    | Some (lxp_)   -> assert false
    | None          -> (match metavar with
        | Metavar (_, subst_, _, _) -> (match Inverse_subst.inverse subst_ with
            | Some s' -> Some (associate value (mkSusp lxp s') s, [])
            | None -> None)
        | _ -> None)
  in
  match (meta, lxp) with
  | (Metavar (val1, s1, _, _), Metavar (val2, s2, _, _)) when val1 = val2
    (* FIXME: handle the case where s1 != s2 !!  *)
    -> Some ((subst, []))
  | (Metavar (v, s1, _, _), _) -> find_or_unify meta v lxp subst
  | (_, _) -> None

(** Unify a Call (call) and a lexp (lxp)
 - Call      , Call               -> UNIFY
 - Call      , lexp               -> CONSTRAINT
*)
and _unify_call (call: lexp) (lxp: lexp) ctx vs (subst: meta_subst)
    : return_type =
  match (call, lxp) with
  | (Call (lxp_left, lxp_list1), Call (lxp_right, lxp_list2))
       when OL.conv_p subst ctx lxp_left lxp_right
    -> List.fold_left (fun op ((ak1, e1), (ak2, e2)) subst
                      -> if ak1 == ak2 then
                          unify_and (unify' e1 e2 ctx vs subst) op
                        else None)
                     (fun subst -> Some (subst, []))
                     (List.combine lxp_list1 lxp_list2)
                     subst
  | (Call _, _) -> Some ((subst, [(call, lxp)]))
  | (_, _)      -> None

(** Unify a Case with a lexp
 - Case, Case -> try to unify
 - Case, _ -> Constraint
*)
(* and _unify_case (case: lexp) (lxp: lexp) (subst: meta_subst) : return_type =
 *   let merge (_, const) subst_res = match subst_res with
 *     | None -> None
 *     | Some (s', c') -> Some (s', const@c')
 *   in
 *   let match_unify_inner lst smap1 smap2 subst =
 *     match _unify_inner lst subst with
 *     | None -> None
 *     | Some (s, c) -> merge (s, c) (_unify_inner_case (zip (SMap.bindings smap1) (SMap.bindings smap2)) s)
 *   in
 *   let match_lxp_opt lxp_opt1 lxp_opt2 tail smap1 smap2 subst =
 *     match lxp_opt1, lxp_opt2 with
 *     | Some (_, lxp1), Some (_, lxp2)
 *       -> match_unify_inner ((lxp1, lxp2)::tail) smap1 smap2 subst
 *     | _, _ -> None
 *   in
 *   match (case, lxp) with
 *     | (Case (_, lxp, lt12, smap, lxpopt), Case (_, lxp2, lt22, smap2, lxopt2))
 *       -> match_lxp_opt lxpopt lxopt2 ((lt12, lt22)::[]) smap smap2 subst
 *     | (Case _, _)     -> Some (subst, [(case, lxp)])
 *     | (_, _) -> None *)

(** Unify a Inductive and a lexp
 - Inductive, Inductive -> try unify
 - Inductive, Var -> constraint
 - Inductive, Call/Metavar/Case/Let -> constraint
 - Inductive, _ -> None
*)
(* and _unify_induct (induct: lexp) (lxp: lexp) (subst: meta_subst) : return_type =
 *   let transform (a, b, c) (d, e, f) = ((a, Some b, c), (d, Some e, f))
 *   and merge map1 map2 (subst, const) : return_type =
 *     match (_unify_induct_sub_list (SMap.bindings map1) (SMap.bindings map2) subst) with
 *     | Some (s', c') -> Some (s', const@c')
 *     | None -> None
 *   in
 *   let zip_unify lst subst map1 map2 : return_type =
 *     match _unify_inner_induct lst subst with
 *     | None        -> None
 *     | Some (s, c) -> merge map1 map2 (s, c)
 *   in
 *   match (induct, lxp) with
 *   | (Inductive (_, lbl1, farg1, m1), Inductive (_, lbl2, farg2, m2)) when lbl1 = lbl2 ->
 *     (match zip_map farg1 farg2 transform with
 *      | Some [] -> Some (subst, [])
 *      | Some lst -> zip_unify lst subst m1 m2
 *      | None -> None)
 *   | (Inductive _, Var _) -> Some (subst, [(induct, lxp)])
 *   | (_, _) -> None *)

(** Unify a SortLevel with a lexp
 - SortLevel, SortLevel -> if SortLevel ~= SortLevel then OK else ERROR
 - SortLevel, _         -> ERROR
*)
and _unify_sortlvl (sortlvl: lexp) (lxp: lexp) ctx vs (subst: meta_subst) : return_type =
  match sortlvl, lxp with
  | (SortLevel s, SortLevel s2) -> (match s, s2 with
      | SLz, SLz -> Some (subst, [])
      | SLsucc l1, SLsucc l2 -> unify' l1 l2 ctx vs subst
      | _, _ -> None)
  | _, _ -> None

(** Unify a Sort and a lexp
 - Sort, Sort -> if Sort ~= Sort then OK else ERROR
 - Sort, Var  -> Constraint
 - Sort, lexp -> ERROR
*)
and _unify_sort (sort_: lexp) (lxp: lexp) ctx vs (subst: meta_subst) : return_type =
  match sort_, lxp with
  | (Sort (_, srt), Sort (_, srt2)) -> (match srt, srt2 with
      | Stype lxp1, Stype lxp2 -> unify' lxp1 lxp2 ctx vs subst
      | StypeOmega, StypeOmega -> Some (subst, [])
      | StypeLevel, StypeLevel -> Some (subst, [])
      | _, _ -> None)
  | Sort _, Var _ -> Some (subst, [(sort_, lxp)])
  | _, _          -> None

(************************ Helper function **************************************)

(***** for Case *****)
(** Check arg_king in <code>(arg_kind * vdef option) list </code> in Case *)
and is_same arglist arglist2 =
  match arglist, arglist2 with
  | (akind, _)::t1, (akind2, _)::t2 when akind = akind2 -> is_same t1 t2
  | [], []                                              -> true
  | _, _                                                -> false

(** try to unify the SMap part of the case *)
(* and _unify_inner_case lst subst =
 *   let merge (_, c) res =
 *     match res with
 *     | Some (s', c') -> Some (s', c@c')
 *     | None          -> None
 *   in
 *   let rec _unify_inner_case list_ subst =
 *     match list_ with
 *     | ((key, (_, arglist, lxp)), (key2, (_, arglist2, lxp2)))::tail when key = key2 ->
 *       (if is_same arglist arglist2
 *        then ( match unify lxp lxp2 subst with
 *            | Some (s', c) -> merge (s', c) (_unify_inner_case tail s')
 *            | None         -> None)
 *        else None)
 *     | [] -> Some (subst, [])
 *     | _ -> None
 *   in (match lst with
 *       | Some [] -> Some (subst, [])
 *       | None -> None
 *       | Some l -> _unify_inner_case l subst) *)

(***** for Inductive *****)
(** for _unify_induct : unify the formal arg*)
(* and _unify_inner_induct lst subst : return_type =
 *   let test ((a1, _, l1), (a2, _, l2)) subst : return_type =
 *     if a1 = a2 then unify l1 l2 subst
 *     else None
 *   in
 *   List.fold_left (fun a e ->
 *       (match a with
 *        | Some (s, c) ->
 *          (match test e s with
 *           | Some (s1, c1) -> Some (s1, c1@c)
 *           | None -> Some (s, c))
 *        | None -> test e subst)
 *     ) None lst *)

(** unify the SMap of list in Inductive *)
(* and _unify_induct_sub_list l1 l2 subst =
 *   let test l1 l2 subst =
 *     let merge l1 l2 subst (s, c) =
 *       match (_unify_induct_sub_list l1 l2 subst) with
 *       | Some (s1, c1) -> Some (s1, c1@c)
 *       | None -> Some (s, c)
 *     in
 *     let unify_zip lst t1 t2 = match _unify_inner_induct lst subst with
 *       | Some (s, c) -> merge l1 l2 subst (s, c)
 *       | None -> (_unify_induct_sub_list t1 t2 subst)
 *     in
 *     match l1, l2 with
 *     | (k1, v1)::t1, (k2, v2)::t2 when k1 = k2 ->
 *       (match zip v1 v2 with
 *        | Some [] -> Some (subst, [])
 *        | Some lst -> unify_zip lst t1 t2
 *        | None -> None)
 *     | _, _ -> None
 *   in test l1 l2 subst *)

