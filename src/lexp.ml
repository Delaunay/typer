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
open Fmt
(* open Unify *)
module S = Subst

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
  | IMult
  | EqType
  | LevelType

(* Pour la propagation des types bidirectionnelle, tout va dans `infer`,
 * sauf Lambda et Case qui vont dans `check`.  Je crois.  *)
type ltype = lexp
 and lexp =
   | Imm of sexp                        (* Used for strings, ...  *)
   | SortLevel of sort_level
   | Sort of location * sort
   | Builtin of builtin * string * ltype
   | Var of vref
   | Susp of lexp * lexp S.subst  (* Lazy explicit substitution: e[σ].  *)
   (* This "Let" allows recursion.  *)
   | Let of location * (vdef * lexp * ltype) list * lexp
   | Arrow of arg_kind * vdef option * ltype * location * lexp
   | Lambda of arg_kind * vdef * ltype * lexp
   | Call of lexp * (arg_kind * lexp) list (* Curried call.  *)
   | Inductive of location * label * ((arg_kind * vdef * ltype) list)
                  * ((arg_kind * vdef option * ltype) list) SMap.t
   | Cons of vref * symbol (* = Type info * ctor_name  *)
   | Case of location * lexp
             * ltype (* The base inductive type over which we switch.  *)
             * (location * (arg_kind * vdef) option list * lexp) SMap.t
             * lexp option               (* Default.  *)
 (*   (\* For logical metavars, there's no substitution.  *\)
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
(*
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

 * let (senv_builtin,venv_builtin)
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
  | Susp (e, _) -> lexp_location e
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
    | _ -> "not implemented"
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


(*
 *      Printing
 * --------------------- *)
(*
    pretty ?        (print with new lines and indents)
    indent level
    print_type?     (print inferred Type)
    print_index     (print dbi index)
    separate decl   (print extra newline between declarations)
    indent size     2/4
    highlight       (use console color to display hints)
*)

type print_context = (bool * int * bool * bool * bool * bool* int)

let pretty_ppctx  = ref (true , 0, true, false, true,  2, true)
let compact_ppctx = ref (false, 0, true, false, true,  2, false)
let debug_ppctx   = ref (false, 0, true, true , false, 2, true)

let rec lexp_print e = _lexp_print (!debug_ppctx) e
and _lexp_print ctx e = print_string (_lexp_to_str ctx e)

(*  Print a lexp into its typer equivalent                              *)
(*  Depending on the print_context the output can be correct typer code *)
(*  This function will be very useful when debugging generated code     *)

(* If I remember correctly ocaml doc, concat string is actually terrible *)
(* It might be better to use a Buffer. *)
and lexp_to_str exp = _lexp_to_str (!debug_ppctx) exp
and _lexp_to_str ctx exp =
    (* create a string instead of printing *)

    let (pretty, indent, ptype, pindex, _, isize, color) = ctx in
    let lexp_to_str = _lexp_to_str ctx in

    (* internal context, when parsing let *)
    let inter_ctx = (false, indent + 1, ptype, pindex, false, isize, color) in

    let lexp_to_stri idt e =
        _lexp_to_str (pretty, indent + idt, ptype, pindex, false, isize, color) e in

    (* colors *)
    let red     = if color then red else "" in
    let green   = if color then green else "" in
    let yellow  = if color then yellow else "" in
    let magenta = if color then magenta else "" in
    let cyan    = if color then cyan else "" in
    let reset   = if color then reset  else "" in

    let _index idx = if pindex then ("[" ^ (string_of_int idx) ^ "]") else "" in

    let make_indent idt = if pretty then (make_line ' ' ((idt + indent) * isize)) else "" in
    let newline = (if pretty then "\n" else " ") in
    let nl = newline in

    let keyword str = magenta ^ str ^ reset in
    let error str   = red ^ str ^ reset in
    let tval str = yellow ^ str ^ reset in
    let fun_call str= cyan ^ str ^ reset in

    let index idx = let str = _index idx in if idx < 0 then (error str) else
        (green ^ str ^ reset) in

    let kind_str k =
        match k with
            | Aexplicit -> "->" | Aimplicit -> "=>" | Aerasable -> "≡>" in

    match exp with
        | Imm(value) -> (match value with
            | String (_, s) -> tval ("\"" ^ s ^ "\"")
            | Integer(_, s) -> tval (string_of_int s)
            | Float  (_, s) -> tval (string_of_float s)
            | _ -> internal_error "Wrong Imm value.")

        | Var ((loc, name), idx) -> name ^ (index idx) ;

        | Let (_, decls, body)   ->
            let decls = List.fold_left (fun str elem ->
                str ^ elem ^ " ") "" (_lexp_str_decls inter_ctx decls) in

            (keyword "let ") ^ decls ^ (keyword "in ") ^ newline ^
                (make_indent 1) ^ (lexp_to_stri 1 body)

        | Arrow(k, Some (_, name), tp, loc, expr) ->
            "(" ^ name ^ " : " ^ (lexp_to_str tp) ^ ") " ^
                (kind_str k) ^ " " ^ (lexp_to_str expr)

        | Arrow(k, None, tp, loc, expr) ->
            (lexp_to_str tp) ^ " " ^ (kind_str k) ^ " " ^ (lexp_to_str expr)

        | Lambda(k, (loc, name), ltype, lbody) ->
            let arg = "(" ^ name ^ " : " ^ (lexp_to_str ltype) ^ ")" in

            (keyword "lambda ") ^ arg ^ " " ^ (kind_str k) ^ newline ^
                (make_indent 1) ^ (lexp_to_stri 1 lbody)

        | Cons(((_, idt_name), idx), (_, ctor_name)) ->
            (keyword "inductive-cons ") ^ idt_name ^ (index idx) ^ " " ^ ctor_name

        | Call(fname, args) -> (
            (*  get function name *)
            let str, idx = match fname with
                | Var((_, name), idx) -> name, idx
                | Builtin (_, name, _) -> name, 0
                | _ -> (error "unkwn"), -1 in

            let binop_str op (_, lhs) (_, rhs) =
                (lexp_to_str lhs) ^ op ^ (lexp_to_str rhs) in

            match (str, args) with
                (* Special Operators *)
                | ("_=_", [lhs; rhs]) -> binop_str " = " lhs rhs
                | ("_+_", [lhs; rhs]) -> binop_str " + " lhs rhs
                | ("_-_", [lhs; rhs]) -> binop_str " - " lhs rhs
                | ("_/_", [lhs; rhs]) -> binop_str " / " lhs rhs
                | ("_*_", [lhs; rhs]) -> binop_str " * " lhs rhs
                (* not an operator *)
                | _ ->
                    let args = List.fold_left
                        (fun str (_, lxp) -> str ^ " " ^ (lexp_to_str lxp))
                        "" args in

                    "(" ^ (fun_call (lexp_to_str fname)) ^ args ^ ")")

        | Inductive (_, (_, name), _, ctors) ->
            (keyword "inductive_") ^ " (" ^ name ^ ") " ^ (lexp_str_ctor ctx ctors)

        | Case (_, target, tpe, map, dflt) ->(
            let str = (keyword "case ") ^ (lexp_to_str target) ^
                                          " : " ^ (lexp_to_str tpe) in
            let arg_str arg =
                List.fold_left (fun str v ->
                    match v with
                        | None -> str ^ " _"
                        | Some (_, (_, n)) -> str ^ " " ^ n) "" arg in


            let str = SMap.fold (fun k (_, arg, exp) str ->
                str ^ nl ^ (make_indent 1) ^
                    "| " ^ (fun_call k) ^ (arg_str arg) ^ " => " ^ (lexp_to_stri 1 exp))
                map str in

            match dflt with
                | None -> str
                | Some df ->
                    str ^ nl ^ (make_indent 1) ^ "| _ => " ^ (lexp_to_stri 1 df))

        | Builtin (_, name, _) -> name

        | Sort (_, Stype lvl) -> (match lvl with
            | SortLevel (SLn 0) -> "Type"
            | SortLevel (SLn v) -> "Type" ^ (string_of_int v))

        | _ -> print_string "Printing Not Implemented"; ""

and lexp_str_ctor ctx ctors =
    SMap.fold (fun key value str ->
        let str = str ^ " (" ^ key in

        let str = List.fold_left (fun str (k, _, arg) ->
            str ^ " " ^ (_lexp_to_str ctx arg)) str value in

            str ^ ")")
        ctors ""

and _lexp_str_decls ctx decls =

    let (pretty, indent, ptype, pindex, sepdecl, isize, _) = ctx in
    let lexp_to_str = _lexp_to_str ctx in

    let make_indent idt = if pretty then (make_line ' ' ((idt + indent) * isize)) else "" in
    let sepdecl = (if sepdecl then "\n" else "") in

    let type_str name lxp = (if ptype then (
        (make_indent 0) ^ name ^ " : " ^ (lexp_to_str lxp) ^ ";") else "") in

    let ret = List.fold_left (fun str ((_, name), lxp, ltp) ->
        let str = if ptype then (type_str name ltp)::str else str in
        ((make_indent 0) ^ name ^ " = " ^ (lexp_to_str lxp) ^ ";" ^
            sepdecl)::str)

        [] decls in
        List.rev ret
