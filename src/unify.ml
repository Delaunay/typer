(* unify.ml --- Unification of Lexp terms.

Copyright (C) 2011-2013  Free Software Foundation, Inc.

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
open Pexp
open Lexp

exception Unify_fail of lexp * lexp

let lexp_unify_fail e1 e2 = raise (Unify_fail (e1, e2))
                                 
(* Whether we only unify the non-erasable part of the code.  *)
let unify_erase = true

(* Check that `r' does not occur within `e', and if env is "Some s",
 * then also check that all its free vars are in `s'.
 * Furthermore, update the scope_level of all the metavars in `e' to be
 * at most `sl'.  *)
let rec lexp_unify_check sl r env e =
  let lexp_unify_check = lexp_unify_check sl r in
  match e with
  | (Sort _ | Imm _ | Builtin _) -> true
  | Var (_,v) -> (match env with None -> true | Some s -> VMap.mem v s)
  | Metavar (_,mk,r') ->
    (r != r' && match (!r,mk,sl) with
              | (MetaSet e, MetaFoF, _) -> lexp_unify_check env e
              | (MetaSet e, MetaGraft env', _)
                -> lexp_unify_check env (lexp_whnf env' e)
              (* FIXME: What if `r' appears in MetaUnset's type?  *)
              | (MetaUnset (venv, t, ScopeLevel sl'), _, ScopeLevel sl) ->
                 if sl < sl' then
                   r := MetaUnset (venv ,t, ScopeLevel sl);
                 true)
  | Arrow (_,v,t1,_,t2)
    -> lexp_unify_check env t1
      && lexp_unify_check
          (match v with
           | None -> env
           | Some (_,v) -> opt_map (VMap.add v (None, Imm Epsilon)) env)
          t2
  | Lambda (_,(_,v),t,e)
    -> lexp_unify_check env t
      && lexp_unify_check (opt_map (VMap.add v (None, Imm Epsilon)) env) e
  | Call (f, args)
    -> lexp_unify_check env f
      && List.for_all (fun (_,arg) -> lexp_unify_check env arg) args
  | Inductive (_, t, cases)
    -> lexp_unify_check env t
      && SMap.for_all (fun name t -> lexp_unify_check env t) cases
  | Cons (t, _) -> lexp_unify_check env t
  | Case (_, e, t, branches, default)
    -> lexp_unify_check env e
      && lexp_unify_check env t
      && (match default with None -> true | Some e -> lexp_unify_check env e)
      && SMap.for_all
          (fun name (_, args, e)
           -> let env' = opt_map (fun env ->
                                 List.fold_left
                                   (fun s (_,(_,arg))
                                    -> VMap.add arg (None, Imm Epsilon) s)
                                   env args)
                                env
             in lexp_unify_check env' e)
          branches
  | Susp (s,e) -> lexp_unify_check env (lexp_whnf s e)
  | Let (_,decls,e)
    -> let env' = opt_map (fun env
                          -> List.fold_left (fun s ((_,v),_,_)
                                            -> VMap.add v (None, Imm Epsilon) s)
                                           env decls)
                         env
      in lexp_unify_check env' e
         && List.for_all (fun (_,e,t) -> lexp_unify_check env' e
                                     && lexp_unify_check env' t)
                        decls

let lexp_unify_check sl r env e =
  print_string "Checking unifiability...";
  let res = lexp_unify_check sl r env e in
  print_string (if res then "success\n" else "failure\n");
  res

let lexp_pattern_p env args =
  let rec check seen args =
    match args with
    | [] -> true
    | (Aerasable, _) :: args when unify_erase -> check seen args
    | (_,arg) :: args ->
      match lexp_whnf VMap.empty arg with
      | Var (_,v) -> not (List.mem v seen)
                    && not (VMap.mem v env)
                    && check (v::seen) args
      | _ -> false
  in check [] args

let lexp_instatiation_counter = ref 0
           
let lexp_instantiate_meta r e =
  print_string "Instantiating _"; print_int (Hashtbl.hash r);
  print_string " to "; lexp_print e; print_string "\n";
  lexp_instatiation_counter := !lexp_instatiation_counter + 1;
  (* FIXME: Should we try and unify `e's type with MetaUnset's?  *)
  r := MetaSet e

(* Unify e1 and e2: `env' is the context in which logical metavars
 * are defined (i.e. we presume a quantification prefix of the form
 * ∀<env>∃<metavars>∀<localvars>).  The local vars are not mentioned
 * explicitly.
 * There can be 4 different outcomes at each step:
 * - We may be able to unify, in which case we just return `acc' unchanged
 *   after instantiating the metavars that needed it.
 * - We may find that the two terms can never be equal, in which case
 *   we raise a `Unify_fail' exception.
 * - We may find that we don't know how to unify the two terms because it falls
 *   outside of the scope of our algorithm.  In that case we add (e1, e2, true)
 *   to `acc' in the hope that some later instantiation of a metavar will
 *   simplify the problem back to something we can handle.
 * - We may find that the two terms can not be unified: they may reduce to the
 *   same value in some contexts, but probably not in all contexts.
 *   In that case we add (e1, e2, false) to `acc'.
 *)
let rec lexp_unify env e1 e2 (acc: unify_csts) : unify_csts =
  let lexp_unify = lexp_unify env in
  match (lexp_whnf VMap.empty e1, lexp_whnf VMap.empty e2) with
  | (Metavar ((l,_),env1,r1), Metavar (_,env2,r2)) when r1 == r2
    -> (match env1, env2, !r1 with
       | (MetaFoF, MetaFoF, _) -> acc
       | (MetaGraft s1, MetaGraft s2, _)
           when VMap.is_empty s1 && VMap.is_empty s2
         -> acc
       | (MetaGraft s1, MetaGraft s2, MetaUnset (venv, _, _)) ->
         (* We need to find a way to unify s1(e)=s2(e) without knowing `e',
          * FIXME: In general it can't be done, but:
          * - we can first filter s1 and s2 w.r.t e's `venv'
          * - any v that's substituted in only one of s1 or s2 cannot appear
          *   free in e, so we can strengthen venv by removing that var.
          * - actually any v that is substituted by s1 and s2 with expressions
          *   that can never be unified could also be removed.
          * - then we can check equality of s1 and s2.  *)
         let diffs
           = VMap.merge (fun v e1 e2
                         -> try let _ = VMap.find v venv in
                               match e1,e2 with
                               | Some e1, Some e2
                                 -> if lexp_conv_p VMap.empty e1 e2
                                   (* Actually if lexp_conv_p fails, we
                                    * could try to see if e1 and e2 are
                                    * incompatible, in which case `v' can be
                                    * removed!  *)
                                   then None else Some ()
                               | _,_ (* Strengthen! *)
                                 -> (match !r1 with
                                    | MetaUnset (venv, t, sl)
                                      -> r1 := MetaUnset (VMap.remove v venv,
                                                        t, sl)
                                    | _ -> ());
                                   None
                           (* `v' can't appear in e, so subst is a nop.  *)
                           with Not_found -> None)
                        s1 s2
         in if VMap.is_empty diffs then acc
            else
              (msg_error l "Unifying grafting metavar against itself";
               (e1, e2, UnifyWhenInst r1) :: acc)
       | _ -> (internal_error "Mixed fof/grafting"))
  | (Metavar (_, mk, r1), _)
    -> (match !r1, mk with
       (* | Some e1, Some s -> lexp_unify (mk_susp s e1) e2 acc
        * | Some e1, None -> lexp_unify e1 e2 acc *)
       | MetaSet _, _ -> (internal_error "WHND returned metavar")
       | MetaUnset (venv,_,sl), MetaGraft s
         -> (try let s' = lexp_subst_inv venv s in
                if lexp_unify_check sl r1 None e2
                then (lexp_instantiate_meta r1 (mk_susp s' e2);
                      acc)
                else (e1, e2, UnifyMaybe) :: acc
            with Lexp_subst_inv -> (e1, e2, UnifyMaybe) :: acc)
       | _, MetaFoF -> (e1, e2, UnifyWhenInst r1) :: acc)
  | (_, Metavar (_,_,r2)) -> lexp_unify e2 e1 acc
  | (Var (_, v1), Var (_, v2)) when v1 = v2 -> acc
  | (Var (_, v1), _) ->
    (match (try fst (VMap.find v1 env) with _ -> None) with
     | Some e1 -> lexp_unify e1 e2 acc
     | None -> match e2 with
              | Var (_, v2)
                -> (match (try fst (VMap.find v2 env) with _ -> None) with
                   | Some e2 -> lexp_unify e1 e2 acc
                   | None -> (e1, e2, UnifyNever) :: acc)
              | _ -> (e1, e2, UnifyMaybe) :: acc)
  | (_, Var (_, v2)) ->
    (match (try fst (VMap.find v2 env) with _ -> None) with
     | Some e2 -> lexp_unify e1 e2 acc
     (* FIXME: Shouldn't we try conversion first?  *)
     | None -> (e1, e2, UnifyMaybe) :: acc)
  | (Sort (_,s1), Sort (_, s2)) when s1 = s2 -> acc
  | (Builtin _, Builtin _) when e1 = e2 -> acc
  | (Imm (String (_, s1)), Imm (String (_, s2))) when s1 = s2 -> acc
  | (Imm (Integer (_, n1)), Imm (Integer (_, n2))) when n1 = n2 -> acc
  | (Imm (Float (_, x1)), Imm (Float (_, x2))) when x1 = x2 -> acc
  | (Imm i1, Imm i2) -> lexp_unify_fail e1 e2
  (*| (Susp (s1',e1), _) -> lexp_unify e1 (lexp_subst_subst s1 s1') e2 s2 acc
   *| (_, Susp (s2',e2)) -> lexp_unify e1 s1 e2 (lexp_subst_subst s2 s2') acc*)
  | (Arrow (ak1,v1,t11,_,t21), Arrow (ak2,v2,t12,_,t22)) when ak1 = ak2
    -> lexp_unify (match v1 with
                  (* | Some v1 -> mk_susp (VMap.add v1 (Var v1) VMap.empty) t21 *)
                  | _ -> t21)
                 (match (v1, v2) with
                  | (Some v1, Some (l,v2))
                    -> mk_susp (VMap.add v2 (Var v1) VMap.empty) t22
                  (* | (Some v1, _)
                   *   -> mk_susp (VMap.add v2 (Var v2) VMap.empty) t22 *)
                  | _ -> t22)
                 (lexp_unify t11 t12 acc)
  | (Arrow _, Arrow _) -> lexp_unify_fail e1 e2
  | (Lambda (Aerasable, v1, _, e1), Lambda (Aerasable, (_,v2), _, e2))
    when unify_erase -> lexp_unify e1 e2 acc
  | (Lambda (ak1, v1, t1, e1), Lambda (ak2, (_,v2), t2, e2)) when ak1 = ak2
    -> let acc' = if unify_erase then acc else lexp_unify t1 t2 acc in
      lexp_unify ((* mk_susp (VMap.add v1 (Var v1) VMap.empty) *) e1)
                 (mk_susp (VMap.add v2 (Var v1) VMap.empty) e2)
                 acc'
  | (Lambda _, Lambda _) -> lexp_unify_fail e1 e2
  | (Lambda (ak1, v1, t1, e1), _) -> (* Eta-expansion!  *)
    lexp_unify ((*mk_susp (VMap.add v1 (Var v1) VMap.empty)*) e1)
               ((*mk_susp (VMap.add v1 (Var v1) VMap.empty)*)
                 Call (e2, [(ak1, Var v1)]))
               acc
  | (_, Lambda _) -> lexp_unify e2 e1 acc
  | (Inductive ((_, id1) as v1, _, _), Inductive ((_, id2) as v2, _, _))
    when id1 != id2 -> lexp_unify_fail (Var v1) (Var v2)
  | (Inductive (_, t1, cs1), Inductive (_, t2, cs2))
    -> let acc' = lexp_unify t1 t2 acc in
      smap_fold2 (fun x y -> x @ y)
                 (fun name t1 t2
                  -> match t1,t2 with
                    | Some t1, Some t2 -> Some (lexp_unify t1 t2 [])
                    | _ -> lexp_unify_fail e1 e2)
                 cs1 cs2 acc'
  | (Cons (t1,(_,name1)), Cons (t2,(_,name2))) when name1 = name2
    -> lexp_unify t1 t2 acc
  | (Call (Var (_, f1), args1), Call (Var (_, f2), args2))
    -> (match try fst (VMap.find f1 env) with _ -> None with
       | Some e1 -> lexp_unify (Call (e1, args1)) e2 acc
       | _ -> match try fst (VMap.find f2 env) with _ -> None with
             | Some e2 -> lexp_unify e1 (Call (e2, args2)) acc
             | _ when f1 = f2 ->
               (* Even if e1 and e2 have the same type and f1=f2, they may not
                * have the same number of arguments (e.g. id id 1 = id 1). *)
               (try List.fold_left2 (fun acc (ak1,a1) (ak2,a2)
                                     -> if unify_erase && ak1 = Aerasable
                                       then acc else lexp_unify a1 a2 acc)
                                    acc args1 args2
                with Invalid_argument _ -> (e1, e2, UnifyNever) :: acc)
             | _ -> (e1, e2, UnifyNever) :: acc)
  | (Call (Cons (_,(_,name1)) as ef1, _), Call (Cons (_,(_,name2)) as ef2, _))
    when name1 != name2 -> lexp_unify_fail ef1 ef2
  | (Call (Cons (t1,_), args1), Call (Cons (t2,_), args2))
    -> let acc' = lexp_unify t1 t2 acc in
      if List.length args1 != List.length args2
      then lexp_unify_fail e1 e2
      else List.fold_left2 (fun acc (ak1,a1) (ak2,a2)
                            -> if unify_erase && ak1 = Aerasable
                              then acc else lexp_unify a1 a2 acc)
                           acc' args1 args2
  | (Call (Metavar (l,MetaFoF,r), _), _) -> (e1, e2, UnifyWhenInst r) :: acc
  | (Call (Metavar ((l,_),mk,r), args), _) when lexp_pattern_p env args
    -> (match (match mk, !r with
              | MetaFoF, _ -> None
              | MetaGraft s, MetaUnset (venv, _, _)
                -> (try Some (lexp_subst_inv venv s)
                   with Lexp_subst_inv -> None)
              | MetaGraft _, MetaSet _
                -> msg_error l "whnf returned a instantiated metavar-call";
                  None) with
       | None -> (e1, e2, UnifyMaybe) :: acc (* Can't invert the subst.  *)
       | Some s
         -> let (args',vs,s')
             = List.fold_left (fun (args,vs,s) (ak,arg)
                               (* FIXME: unify_erase?  *)
                               -> match lexp_whnf VMap.empty arg with
                                 | Var (l,v) -> let v' = copy_var v
                                               in ((ak,(l,v'))::args,
                                                   v::vs,
                                                   VMap.add v (Var (l,v')) s)
                                 | _ -> (internal_error "Oops"))
                              ([], [], s) args
           in match !r with
              | MetaSet _ -> acc (* Impossible!  *)
              | MetaUnset (venv, _, sl)
                -> if lexp_unify_check
                       sl r (Some (List.fold_left
                                     (fun env v
                                      -> VMap.add v (None, Imm Epsilon) env)
                                     venv vs))
                       e2
                  then (lexp_instantiate_meta
                          r (List.fold_left
                               (fun e (ak, ((l,_) as v)) ->
                                Lambda (ak, v, mk_meta sl venv l, e))
                               (mk_susp s' e2) args');
                        acc)
                  else (e1, e2, UnifyMaybe) :: acc)
  | (Call _, Call _) when lexp_conv_p env e1 e2 -> acc
  | (Case _, Case _) when lexp_conv_p env e1 e2 -> acc
  | ((Sort _ | Imm _ | Arrow _ | Inductive _ | Cons _ | Builtin _),
     (Sort _ | Imm _ | Arrow _ | Inductive _ | Cons _ | Builtin _))
    -> lexp_unify_fail e1 e2
  | ((Case _, _) | (_, Case _)) -> (e1, e2, UnifyMaybe) :: acc
  | ((Call _, _) | (_, Call _)) -> (e1, e2, UnifyMaybe) :: acc
  | ((Susp _, _) | (_, Susp _)) -> (internal_error "WHNF returned a Susp")
  | ((Let _, _) | (_, Let _)) -> (internal_error "WHNF returned a Let")

let lexp_unify env x1 x2 csts =
  print_string "Unifying: ";
  lexp_print x1; print_string " =with= ";
  lexp_print x2; print_endline "...";
  let csts' = lexp_unify env x1 x2 csts in
  print_endline ("...done with "^string_of_int (List.length csts' - List.length csts)^" csts");
  csts'

(* Make sure `k' is a Sort.  *)
let lexp_unify_sort venv k csts =
  (match lexp_whnf VMap.empty k with
   (* If the type `k' is already known, just keep it, otherwise default
    * it to `Type'.  *)
   | Metavar ((l,_), _, r) -> lexp_instantiate_meta r (type0)
   | _ -> ());
  csts


let rec lexp_resolve_pending venv p =
  let start_count = !lexp_instatiation_counter in
  let p' = List.fold_left
             (fun p cst ->
              match cst with
              | (e1, e2, UnifyNever)
                -> if lexp_conv_p venv e1 e2 then p
                  else ((e1, e2, UnifyNever) :: p)
              | (e1, e2, UnifyWhenInst v)
                when (match !v with MetaUnset _ -> true
                                  | _ -> false)
                (* FIXME: Are we really sure that lexp_conv_p can't succeed
                 * before `v' is instantiated?  *)
                -> ((e1, e2, UnifyWhenInst v) :: p)
              | (e1, e2, (UnifyMaybe | UnifyWhenInst _))
                -> lexp_unify venv e1 e2 p)
             [] p in
  if start_count = !lexp_instatiation_counter then p'
  else lexp_resolve_pending venv p'
