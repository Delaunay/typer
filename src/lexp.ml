(* lexp.ml --- Lambda-expressions: the core language.

Copyright (C) 2011-2016  Free Software Foundation, Inc.

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
open Myers
open Grammar
(* open Unify *)

(*************** DeBruijn indices for variables *********************)

(* Occurrence of a variable's symbol: we use DeBruijn index, and for
 * debugging purposes, we remember the name that was used in the source
 * code.  *)
type vdef = location * string
type db_index = int             (* DeBruijn index.  *)
type db_offset = int            (* DeBruijn index offset.  *)
type db_revindex = int          (* DeBruijn index counting from the root.  *)
type vref = vdef * db_index


type label = symbol

(*************** Elaboration to Lexp *********************)

type builtin =
  | IntType
  | FloatType
  | SexpType
  | LexpType
  | IAdd
  | EqType
  | LevelType


type ltype = lexp
 and lexp =
   | Imm of sexp                        (* Used for strings, ...  *)
   | SortLevel of sort_level
   | Sort of location * sort
   | Builtin of builtin * string * ltype
   | Var of vref
   (* This just means that all non-local Var bindings in the lexp should
    * have their debuijn index incremented by i.  IOW it guarantees that
    * the lexp does not refer to the topmost i elements of the context.  *)
   | Shift of db_offset * lexp
   (* This "Let" allows recursion.  *)
   | Let of location * (vdef * lexp * ltype) list * lexp
   | Arrow of arg_kind * vdef option * ltype * location * lexp
   | Lambda of arg_kind * vdef * ltype * lexp
   | Call of lexp * (arg_kind * lexp) list (* Curried call.  *)
   | Inductive of location * label * ((arg_kind * vdef * ltype) list)
                  * ((arg_kind * vdef option * ltype) list) SMap.t
   | Cons of vref * symbol (* = Type info * ctor_name*)
   | Case of location * lexp
             * ltype (* The base inductive type over which we switch.  *)
             * (location * (arg_kind * vdef) option list * lexp) SMap.t
             * lexp option               (* Default.  *)
    | UnknownType of location (* This is easy to handle *)
 (*   | Susp of subst * lexp
  *   (\* For logical metavars, there's no substitution.  *\)
  *   | Metavar of (location * string) * metakind * metavar ref
  * and metavar =
  *   (\* An uninstantiated var, along with a venv (stipulating over which vars
  *    * it should be closed), and its type.
  *    * If its type is not given, it implies its type should be a sort.  *\)
  *   | MetaUnset of (lexp option * lexp) VMap.t * ltype option * scope_level
  *   | MetaSet of lexp
  * and metakind =
  *   | MetaGraft of subst
  *   (\* Forward reference or Free var: Not known yet, but not instantiable by
  *    * unification.  *\)
  *   | MetaFoF
  * and subst = lexp VMap.t *)
 and sort =
   | Stype of lexp
   | StypeOmega
   | StypeLevel
 and sort_level =
  | SLn of int
  | SLsucc of lexp


(* let mk_susp s e = if VMap.is_empty s then e else Susp (s, e)
 * let mk_subst x v e = Susp (VMap.add x v VMap.empty, e) *)

let opt_map f x = match x with None -> None | Some x -> Some (f x)

(**** The builtin elements ****)

let dloc = dummy_location
let slevel0 = SortLevel (SLn 0)
let slevel1 = SortLevel (SLn 1)
let type0 = Sort (dloc, Stype slevel0)
let type1 = Sort (dloc, Stype slevel1)
let type_level = Sort (dloc, StypeLevel)
let type_omega = Sort (dloc, StypeOmega)
let type_int = Builtin (IntType, "Int", type0)
let type_float = Builtin (FloatType, "Float", type0)
let type_level = Builtin (LevelType, "TypeLevel", type_level)
let type_eq
  = Builtin
      (EqType, "_₌_",
       let lv = (dloc, "ℓ") in
       let tv = (dloc, "t") in
       Arrow (Aerasable, Some lv, type_level, dloc,
              Arrow (Aerasable, Some tv,
                     Sort (dloc, Stype (Var (lv, 0))), dloc,
                     Arrow (Aexplicit, None, Var (tv, 0), dloc,
                            Arrow (Aexplicit, None, Var (tv, 1), dloc,
                                   type0)))))
let iop_binary = Arrow (Aexplicit, None, type_int, dummy_location,
                        Arrow (Aexplicit, None, type_int, dummy_location,
                               type_int))
let builtin_iadd = Builtin (IAdd, "_+_", iop_binary)
let builtins =
  (* let l = dloc in *)
  [ (* (0,"%type1%", Some (type1),	Lsort (l, 2)) *)
    ("Type",  Some (type0),	type1)
  ; ("Type@", Some (let lv = (dloc, "ℓ") in
                    Lambda (Aexplicit, lv, type_level,
                            Sort (dloc, Stype (Var (lv, 0))))),
     let lv = (dloc, "ℓ") in
     Arrow (Aexplicit, Some lv, type_level, dloc,
            Sort (dloc, Stype (SortLevel (SLsucc (Var (lv,0)))))))
    (* ;(var_macro,  "%Macro%", None,		type0) *)
  ] @
    List.map (fun bi -> match bi with
                     | Builtin (_, name, t) -> (name, Some bi, t)
                     | _ -> internal_error "Registering a non-builtin")
             [type_level; type_int; type_float; type_eq]
(* let var_bottom = Var (dloc, -1) *)

(* let (senv_builtin,venv_builtin)
 *   = List.fold_left (fun (senv,venv) (name,e,t) ->
 *                     let v = name in
 *                     (SMap.add name v senv,
 *                      VMap.add v (e, t) venv))
 *                    (SMap.empty, VMap.empty)
 *                    builtins *)

(* Handling scoping/bindings is always tricky.  So it's always important
 * to keep in mind for *every* expression which is its context.
 *
 * In particular, this holds true as well for those expressions that appear
 * in the context.  Traditionally for dependently typed languages we expect
 * the context's rules to say something like:
 *
 *      ⊢ Γ    Γ ⊢ τ:Type
 *      —————————————————
 *          ⊢ Γ,x:τ
 *
 * Which means that we expect (τ) expressions in the context to be typed
 * within the *rest* of that context.
 *
 * This also means that when we look up a binding in the context, we need to
 * adjust the result, since we need to use it in the context where we looked
 * it up, which is different from the context where it was defined.
 *
 * More concretely, this means that lookup(Γ, i) should return an expression
 * where debruijn indices have been shifted by "i".
 *
 * This is nice for "normal bindings", but there's a complication in the
 * case of recursive definitions.  Typically, this is handled by using
 * something like a μx.e construct, which works OK for the theory but tends
 * to become rather inconvenient in practice for mutually recursive
 * definitions.  So instead, we annotate the recursive binding with
 * a "recursion_offset" to say that rather than being defined in "the rest
 * of the context", they're defined in a slightly larger context that
 * includes "younger" bindings.
 *)


(*****  SMap fold2 helper *****)

let smap_fold2 c f m1 m2 init
  = let chunks = SMap.merge f m1 m2 in
    SMap.fold (fun _ x y -> c x y) chunks init

(** Elaboration.  **)

(* let mk_meta2 sl venv l
 *   = let mk = MetaGraft VMap.empty in
 *     let t = Metavar ((l, "_"), mk, ref (MetaUnset (venv, None, sl)))
 *     in (Metavar ((l, "_"), mk, ref (MetaUnset (venv, Some t, sl))), t)
 * let mk_meta sl venv l
 *   = let mk = MetaGraft VMap.empty in
 *     let t = Metavar ((l, "_"), mk, ref (MetaUnset (venv, None, sl)))
 *     in Metavar ((l, "_"), mk, ref (MetaUnset (venv, Some t, sl)))
 * let mk_meta_dummy = mk_meta (ScopeLevel(-1))
 * let mk_metat sl venv l t
 *   = let mk = MetaGraft VMap.empty in
 *     Metavar ((l, "_"), mk, ref (MetaUnset (venv, Some t, sl))) *)
type value = lexp

(* Free vars (with type) we need to generalize.  *)
(* type fvars = lexp SMap.t *)
(* Each element of a unification constraint is a pair of expresions that
 * need to be unified together with a boolean indicating whether this might be
 * algorithmically unifiable.  I.e. if the boolean is false, then there's no
 * point calling lexp_unify on it because we know it will just re-add the same
 * constraint.  *)
(* type unify_cond =
 *   | UnifyNever                      (\* Can't be resolved by unification.  *\)
 *   | UnifyWhenInst of metavar ref    (\* Needs ref to be instantiated.  *\)
 *   | UnifyMaybe                      (\* Not clear when.  *\)
 * type unify_csts = (lexp * lexp * unify_cond) list
 * type constraints = unify_csts
 *
 * type pending = constraints *)
let id x = x

(* Combine two substitutions.  I.e. e = s(s'(e))).  *)
(* let lexp_subst_subst s s' =
 *   let s' = VMap.map (fun e -> mk_susp s e) s' in
 *   VMap.fold (fun v e s -> if VMap.mem v s
 *                        then (internal_error "Overlapping substs")
 *                        else VMap.add v e s)
 *             s s' *)

let lexp_max_sort (k1, k2) =
  match k1,k2 with
  | Sort (_,l1), Sort (_, l2) -> max l1 l2
  | _ -> internal_error "finding the max of non-sorts!"

(* Invert a substitution.  I.e. return s' such that s'(s(e))=e.
 * It is allowed to presume that e is closed in `venv'.  *)
(* exception Lexp_subst_inv
 * let lexp_subst_inv venv s =
 *   VMap.fold (fun v e s ->
 *              try let _ = VMap.find v venv in
 *                  match e with
 *                  (\* | Var _ when e = var_bottom -> s *\)
 *                  | Var (l,v') -> if VMap.mem v' s then raise Lexp_subst_inv
 *                                 else VMap.add v' (Var (l,v)) s
 *                  | _ -> raise Lexp_subst_inv
 *              (\* `v' is not in `venv' so it won't appear in `e'.  *\)
 *              with Not_found -> s)
 *             s VMap.empty *)

let rec lexp_location e =
  match e with
  | Sort (l,_) -> l
  | SortLevel (SLsucc e) -> lexp_location e
  | SortLevel (SLn _) -> dummy_location
  | Imm s -> sexp_location s
  | Var ((l,_),_) -> l
  | Builtin _ -> dummy_location
  | Let (l,_,_) -> l
  | Arrow (_,_,_,l,_) -> l
  | Lambda (_,(l,_),_,_) -> l
  | Call (f,_) -> lexp_location f
  | Inductive (l,_,_,_) -> l
  | Cons (_,(l,_)) -> l
  | Case (l,_,_,_,_) -> l
  | UnknownType l -> l
  | Shift (_, l) -> lexp_location l
  (* | Susp (_, e) -> lexp_location e
   * | Metavar ((l,_),_,_) -> l *)


let lexp_to_string e =
  match e with
    | Imm _ -> "Imm"
    | Var _ -> "Var"
    | Let _ -> "let"
    | Arrow _ -> "Arrow"
    | Lambda _ -> "lambda"
    | Call _ -> "Call"
    | Inductive _ -> "inductive_"
    | Cons _ -> "inductive-cons"
    | Case _ -> "case"
    | _ -> "unkwn"
;;

let builtin_reduce b args arg =
  match b,args,arg with
  | IAdd, [(_,Imm (Integer (_, i1)))], (Imm (Integer (_, i2)))
    -> Some (Imm (Integer (dummy_location, i1 + i2)))
  | _ -> None

(* Apply substitution `s' and then reduce to weak head normal form.
 * WHNF implies:
 * - Not a Let.
 * - Not a let-bound variable.
 * - Not a Susp.
 * - Not an instantiated Metavar.
 * - Not a Call (Lambda _).
 * - Not a Call (Call _).
 * - Not a Call (_, []).
 * - Not a Case (Cons _).
 * - Not a Call (MetaSet, ..).
 *)
(* let rec lexp_whnf (s : lexp VMap.t) e =
 *   match e with
 *   | (Imm _ | Builtin _) -> e
 *   | Sort (_, (StypeLevel | StypeOmega | Stype (SortLevel (SLn _)))) -> e
 *   | Sort (l, Stype e) -> Sort (l, Stype (mk_susp s e))
 *   | SortLevel (SLn _) -> e
 *   | SortLevel (SLsucc e) ->
 *      (match lexp_whnf s e with
 *       | SortLevel (SLn n) -> SortLevel (SLn (n + 1))
 *       | e' -> SortLevel (SLsucc e'))
 *   | Arrow (ak, v, t1, l, t2) -> Arrow (ak, v, mk_susp s t1, l, mk_susp s t2)
 *   | Lambda (ak, v, t, e) -> Lambda (ak, v, mk_susp s t, mk_susp s e)
 *   | Call (f, args) ->
 *     List.fold_left (fun e (ak,arg) ->
 *                     match e with
 *                     | Builtin (b,_,_) ->
 *                        (match builtin_reduce b [] arg with
 *                         | Some e -> e
 *                         | _ -> Call (e, [(ak, mk_susp s arg)]))
 *                     | Call (Builtin (b,_,_), args) ->
 *                        (match builtin_reduce b args arg with
 *                         | Some e -> e
 *                         | _ -> Call (e, [(ak, mk_susp s arg)]))
 *                     | Lambda (_, (_,v), _, body)
 *                       -> lexp_whnf (VMap.add v (mk_susp s arg) VMap.empty) body
 *                     | Call (f, args) -> Call (f, (ak, mk_susp s arg) :: args)
 *                     | _ -> Call (e, [(ak, mk_susp s arg)]))
 *                    (lexp_whnf s f) args
 *   | Inductive (id, t, branches)
 *     -> Inductive (id, mk_susp s t, SMap.map (mk_susp s) branches)
 *   | Cons (t, tag) -> Cons (mk_susp s t, tag)
 *   | Case (l, e, t, branches, default)
 *     -> let select name actuals
 *         = try let (l,formals,body) = SMap.find name branches in
 *               lexp_whnf (List.fold_left2 (fun s (_,a) (_,(_,f)) ->
 *                                       VMap.add f a s)
 *                                      s actuals formals)
 *                         body
 *           with Not_found ->
 *                match default with
 *                | None -> msg_error l "Unmatched constructor";
 *                         mk_meta_dummy VMap.empty l
 *                | Some body -> lexp_whnf s body
 *       in
 *       (match lexp_whnf s e with
 *        | Cons (_, (_,name)) -> select name []
 *        | Call (Cons (_, (_, name)), actuals) -> select name actuals
 *        | e -> Case (l, e, t,
 *                    SMap.map (fun (l,args,body)
 *                              -> (l, args, mk_susp s body))
 *                             branches,
 *                    match default with Some e -> Some (mk_susp s e)
 *                                     | None -> None))
 *   | Susp (s', e) -> lexp_whnf (lexp_subst_subst s s') e
 *   | Metavar (_,MetaFoF,r) ->
 *     (match !r with | MetaSet e -> lexp_whnf s e | _ -> e)
 *   | Metavar (l, MetaGraft s', r) ->
 *     let s' = (lexp_subst_subst s s') in
 *     (match !r with MetaSet e -> lexp_whnf s' e
 *                  (\* FIXME: filter s' w.r.t `venv'.  *\)
 *                  | MetaUnset (venv,_,_) -> Metavar (l, MetaGraft s', r))
 *   (\* BEWARE: we need a recursive environment, which is kinda painful
 *    * to create (tho we could use ref'cells), so we use a hack instead.  *\)
 *   | Let (l,decls,body)
 *     -> let decls' = List.map (fun (v, e, t) -> (v, mk_susp s e, mk_susp s t))
 *                             decls in
 *       let s' = List.fold_left (fun s ((l',v),e,t) ->
 *                                VMap.add v (Let (l, decls', Var (l', v))) s)
 *                               s decls
 *       in lexp_whnf s' body
 *   | Var (l,v)
 *     -> (try match VMap.find v s with
 *            (\* Hack attack!  A recursive binding, let's unroll it here. *\)
 *            | Let (_,decls,Var (_, v')) when v = v'
 *              -> let e = List.fold_left (fun e ((_,v'), e', _) ->
 *                                        if v = v' then e' else e)
 *                                       (\* This metavar is just a placeholder
 *                                        * which should be dropped.  *\)
 *                                       (mk_meta_dummy VMap.empty l) decls
 *                (\* Here we stay in `s' to keep the recursive bindings.  *\)
 *                in lexp_whnf s (lexp_copy e)
 *            | e -> lexp_whnf VMap.empty (lexp_copy e)
 *        with Not_found -> e) *)


let conv_erase = true              (* If true, conv ignores erased terms. *)

(* Return true iff e₁ and e₂ are convertible in `env'.
 * `s' maps vars bound in e₁ to their α-equivalent in e₂.  *)
(* let rec lexp_conv_p env s e1 e2 =
 *   let lexp_conv_p = lexp_conv_p env in
 *   (\* We compare e1 and e2 directly because vars in `s' should never appear
 *    * in e2 anyway, so if e1 and e2 are equal, then e1 doesn't refer to vars
 *    * in `s' either.  *\)
 *   e1 == e2
 *   || match (e1, e2) with
 *     | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
 *     | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
 *     | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
 *     | (Var (_, v1), Var (_, v2)) ->
 *       v1 = v2
 *       || (match try fst (VMap.find v1 env) with _ -> None with
 *          | Some e1 -> lexp_conv_p s e1 e2
 *          | None -> match try fst (VMap.find v2 env) with _ -> None with
 *                   | Some e2 -> lexp_conv_p s e1 e2
 *                   | None -> v2 = VMap.find v1 s)
 *     | (Var (_, v1), _)
 *       -> (match try fst (VMap.find v1 env) with _ -> None with
 *          | Some e1 -> lexp_conv_p s e1 e2
 *          | None -> false)
 *     | (_, Var (_, v2))
 *       -> (match try fst (VMap.find v2 env) with _ -> None with
 *          | Some e2 -> lexp_conv_p s e1 e2
 *          | None -> false)
 *     | (Metavar (_, mk, r1), _)
 *         when (match !r1 with MetaSet _ -> true | _ -> false)
 *       -> (match !r1,mk with
 *          | MetaSet e1, MetaGraft s1 -> lexp_conv_p s (mk_susp s1 e1) e2
 *          | MetaSet e1, MetaFoF      -> lexp_conv_p s e1 e2
 *          | _ -> false) (\* Impossible.  *\)
 *     | (_, Metavar (_, mk, r2))
 *         when (match !r2 with MetaSet _ -> true | _ -> false)
 *       -> (match !r2,mk with
 *          | MetaSet e2, MetaGraft s2 -> lexp_conv_p s e1 (mk_susp s2 e2)
 *          | MetaSet e2, MetaFoF      -> lexp_conv_p s e1 e2
 *          | _ -> false) (\* Impossible.  *\)
 *     | (Metavar ((l,_), MetaGraft s1, r1), Metavar (_, MetaGraft s2, r2))
 *         when r1 = r2
 *       -> (match !r1 with
 *          | MetaSet _ -> false    (\* Impossible!  *\)
 *          | MetaUnset (venv,_,_)
 *            -> let diffs
 *                (\* FIXME: If we filter s1&s2 when constructing MetaGraft, we can
 *                 * use VMap.equal.  *\)
 *                = VMap.merge
 *                    (fun v e1 e2
 *                     -> try let _ = VMap.find v venv in
 *                           match e1,e2 with
 *                           | Some e1, Some e2 when lexp_conv_p s e1 e2
 *                             -> None
 *                           | _ -> Some ()
 *                       (\* If `v' is not in `venv' that means `v' cannot
 *                        * appear in the var's instantiation, so we only need
 *                        * to decide if s(e)=e which we presume to be true for
 *                        * the same reason that we started this function by
 *                        * comparing e1≡e2 rather than s(e1)=e2.  *\)
 *                       with _ -> None)
 *                    s1 s2
 *              in VMap.is_empty diffs)
 *     | (Metavar (_, MetaFoF, r1), Metavar (_, MetaFoF, r2)) -> r1 = r2
 *     | (Susp (s1, e1), _) -> lexp_conv_p s (lexp_whnf s1 e1) e2
 *     | (_, Susp (s2, e2)) -> lexp_conv_p s e1 (lexp_whnf s2 e2)
 *     | (Cons (t1, (_, tag1)), Cons (t2, (_, tag2)))
 *       -> tag1 = tag2 && lexp_conv_p s t1 t2
 *     | (Case (_,e1,t1,branches1,default1), Case (_,e2,t2,branches2,default2))
 *       -> lexp_conv_p s e1 e2
 *         && (match (default1, default2) with
 *            | (None, None) -> true
 *            | (Some e1, Some e2) -> lexp_conv_p s e1 e2
 *            | _ -> false)
 *         && (conv_erase || lexp_conv_p s t1 t2)
 *         && SMap.equal
 *             (fun (_, args1, e1) (_, args2, e2)
 *              -> lexp_conv_p (List.fold_left2
 *                               (fun s (ak1,(_,arg1)) (ak2,(_,arg2))
 *                                -> if conv_erase && ak1 = Aerasable then s
 *                                  else VMap.add arg1 arg2 s)
 *                               s args1 args2)
 *                            e1 e2)
 *             branches1 branches2
 *     | (Inductive ((_,id1), t1, cases1), Inductive ((_,id2), t2, cases2))
 *       -> id1 = id2
 *         && lexp_conv_p s t1 t2
 *         && SMap.equal (lexp_conv_p s) cases1 cases2
 *     | (Lambda (Aerasable,_,_,e1), Lambda (Aerasable,_,_,e2)) when conv_erase
 *       -> lexp_conv_p s e1 e2
 *     | (Lambda (ak1,(_,v1),t1,e1), Lambda (ak2,(_,v2),t2,e2))
 *       -> ak1 = ak2
 *         && (conv_erase || lexp_conv_p s t1 t2)
 *         && lexp_conv_p (VMap.add v1 v2 s) e1 e2
 *     | (Call (f1, args1), Call (f2, args2))
 *       -> lexp_conv_p s f1 f2
 *         && List.length args1 = List.length args2
 *         && List.fold_left2 (fun eqp (ak1,a1) (ak2,a2) ->
 *                            eqp && ak1 = ak2
 *                            && ((conv_erase && ak1 = Aerasable)
 *                               || lexp_conv_p s a1 a2))
 *                           true args1 args2
 *     | (Arrow (ak1,v1,t11,_,t21), Arrow (ak2,v2,t12,_,t22))
 *       -> ak1 = ak2
 *         && lexp_conv_p s t11 t12
 *         && lexp_conv_p (match (v1,v2) with
 *                         | (Some (_,v1), Some (_,v2)) -> VMap.add v1 v2 s
 *                         | _ -> s)
 *                        t21 t22
 *     | (Let (_,decls1,body1), Let (_,decls2,body2))
 *       -> List.length decls1 = List.length decls2
 *         && let s' = List.fold_left2 (fun s ((_,v1),_,_) ((_,v2),_,_)
 *                                     -> VMap.add v1 v2 s)
 *                                    s decls1 decls2
 *           in List.fold_left2 (fun eqp (_,e1,t1) (_,e2,t2) ->
 *                               eqp
 *                               && lexp_conv_p s' e1 e2
 *                               && lexp_conv_p s t1 t2)
 *                              (lexp_conv_p s' body1 body2)
 *                              decls1 decls2
 *     | (_, _) -> false *)

(*
(* In non-recursion calls, `s' is always empty.  *)
let lexp_conv_p env = lexp_conv_p env VMap.empty

let lexp_unparse_v (l,v)
  (* FIXME: This only works for bound vars, free vars will need
   * a different treatment!  *)
  = let name = varname v in (l,name ^ (string_of_int v))
let rec lexp_unparse_decls decls =
  List.map (fun (v,_,t)
            -> (lexp_unparse_v v, lexp_unparse t, true))
           decls
  @ List.map (fun (v,e,_)
              -> (lexp_unparse_v v, lexp_unparse e, false))
             decls
and lexp_unparse e : pexp =
  match e with
  | Sort (l, StypeLevel) -> Pvar (l, "TypeLevel")
  | Sort (l, StypeOmega) -> Pvar (l, "TypeΩ")
  | Sort (l, Stype e)
    -> Pcall (Pvar (l, "Type"), [pexp_unparse (lexp_unparse e)])
  | SortLevel (SLn n) -> Pimm (Integer (dummy_location, n))
  | SortLevel (SLsucc e) -> Pcall (Pvar (lexp_location e, "S"),
                                  [pexp_unparse (lexp_unparse e)])
  | Imm s -> Pimm s
  | Builtin (b,name,t) -> Pvar (dummy_location, name)
  | Var v -> Pvar (lexp_unparse_v v)
  | Let (l,decls,e)
    -> Plet (l, lexp_unparse_decls decls,
            lexp_unparse e)
  | Arrow (ak,v,t1,l,t2)
    -> Parrow (ak,
              (match v with Some v -> Some (lexp_unparse_v v) | None -> None),
              lexp_unparse t1,
              l, lexp_unparse t2)
  | Lambda (ak, v, t, e)                 (* FIXME: losing `ak'.  *)
    -> Plambda (ak, lexp_unparse_v v, Some (lexp_unparse t), lexp_unparse e)
  | Call (f, args)                      (* FIXME: losing `ak'.  *)
    -> Pcall (lexp_unparse f, List.map (fun (_,arg)
                                       -> pexp_unparse (lexp_unparse arg))
                                      args)
  | Inductive (_,t,cases)               (* FIXME: losing `id'.  *)
    -> Pinductive (lexp_unparse t,
                  SMap.fold (fun name t ps
                             -> ((lexp_location t, name), lexp_unparse t)::ps)
                            cases [])
  | Cons (Var v, tag)
    -> Pcons (lexp_unparse_v v, tag)
  | Cons (_,_)
    -> (internal_error "Can't print a non-Var-typed Constructor")
  | Case (l, e, t, branches, default)
    -> Pcase (l, lexp_unparse e,
             (* FIXME!!  *)
             SMap.fold (fun name (l, args, e) cases
                        -> ((l,name),
                           List.map (fun (ak,v) -> (ak, lexp_unparse_v v)) args,
                          lexp_unparse e) :: cases)
                       branches [],
             opt_map lexp_unparse default)
  (* | Metavar (v,_,r) ->
   *   (match !r with
   *    | MetaSet e -> lexp_unparse e
   *    | _ -> Pmetavar v) (\* FIXME: losing the ref.  *\)
   * | Susp (s,e) -> lexp_unparse (lexp_whnf s e) *)
    (* (internal_error "Can't print a Susp") *)

let lexp_print e = sexp_print (pexp_unparse (lexp_unparse e))

(* let rec lexp_type (env: (lexp option * lexp) VMap.t) e : lexp =
 *   let rec follow e =
 *     match e with
 *     | Var (_,v) -> vmap_getval v
 *     | Metavar (_,_,r) -> (match !r with MetaSet e -> follow e | _ -> e)
 *     | _ -> e
 *   and vmap_getval (v : var) =
 *     match VMap.find v env with (Some e, _) -> follow e
 *                              | _ -> Var (dummy_location, v) in
 *   match e with
 *   | Sort (l, Stype e) -> Sort (l, Stype (SortLevel (SLsucc e)))
 *   | Sort (l, StypeOmega)
 *     -> msg_error l "TypeΩ doesn't have a type"; mk_meta_dummy env l
 *   | Sort (l, StypeLevel)
 *     -> msg_error l "TypeLevel doesn't have a type"; mk_meta_dummy env l
 *   | SortLevel _ -> Sort (lexp_location e, StypeLevel)
 *   | Imm (Integer _) -> type_int
 *   | Imm (Float _) -> type_float
 *   | Builtin (_,_,t) -> t
 *   (\* | Imm (String _) -> Var (dummy_location, var_string) *\)
 *   | Imm s -> let l = sexp_location s in
 *             msg_error l "Unrecognized sexp in lexp"; mk_meta_dummy env l
 *   | Var (_,name) -> snd (VMap.find name env)
 *   | Let (l, decls, body) ->
 *     lexp_type (List.fold_left (fun env ((_,v),e,t) ->
 *                                VMap.add v (Some (Let (l, decls, e)), t) env)
 *                               env decls)
 *               body
 *   | Arrow _ -> type0             (\* FIXME! *\)
 *   | Lambda (ak, ((l,v) as var),t,e) ->
 *     Arrow (ak, Some var, t, dummy_location,
 *            lexp_type (VMap.add v (None, t) env) e)
 *   | Call (f, args) ->
 *     let ft = lexp_type env f in
 *     let rec one_arg t (_,arg) =
 *       match lexp_whnf VMap.empty t with
 *       | Arrow (_, None, t1, _, t2) -> t2
 *       | Arrow (_, Some (_,v), t1, _, t2) ->
 *         Susp (VMap.add v arg VMap.empty, t2)
 *       | _ -> msg_error (lexp_location arg) "Too many arguments"; t
 *     in List.fold_left one_arg ft args
 *   | Inductive (_,t,_) -> t
 *   | Cons (e,(l,name)) ->
 *     (match lexp_whnf VMap.empty e with
 *      | Inductive (_,_,branches) ->
 *        (try SMap.find name branches
 *         with Not_found -> msg_error l ("No such constructor name `"^name^"'");
 *                          mk_meta_dummy env l)
 *      | _ -> msg_error l "The constructor refers to a non-inductive type";
 *            mk_meta_dummy env l)
 *   | Case (_,_,_,_,Some default) -> lexp_type env default
 *   (\* | Case (_,_,(_,i, args, branch) :: _,_) ->
 *    *   let ct = lexp_type env (vmap_getval cv) in
 *    *   let rec one_arg (t,env) argo =
 *    *     match t with
 *    *     | Arrow (_, None, t1, _, t2) ->
 *    *       (t2, VMap.add (snd argo) (None, t1) env)
 *    *     | Arrow (_, Some (l,v), t1, _, t2) ->
 *    *       (Susp (VMap.add v (mk_meta_dummy l) VMap.empty, t2),
 *    *        VMap.add (snd argo) (None, t1) env)
 *    *     | Susp (s, Arrow (ak,v,t1,l,t2)) ->
 *    *       one_arg (Arrow (ak, v, Susp (s, t1), l, Susp (s, t2)), env) argo
 *    *     | _ -> msg_error (fst argo) "Too many arguments";
 *    *           (t, VMap.add (snd argo)
 *    *                        (None, mk_meta_dummy (fst argo))
 *    *                        env)
 *    *   in let (_,env') = List.fold_left one_arg (ct,env) args
 *    *      in lexp_type env' branch *\)
 *   | Case (l,_,_,_,None) -> mk_meta_dummy env l (\* Dead code?  *\)
 *   | Susp (s, e) -> lexp_type env (lexp_whnf s e)
 *   | Metavar ((l,_),_,r)
 *     -> match !r with MetaSet e -> lexp_type env e
 *                   | MetaUnset (_, Some t, _) -> t
 *                   | _ -> msg_error l "Uninstantiated metavar of unknown type";
 *                         mk_meta_dummy env l *)

*)
