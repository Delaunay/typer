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

module U = Util
module L = List
module SMap = U.SMap
open Fmt

open Sexp
open Pexp

open Myers
open Grammar

(* open Unify *)
module S = Subst

type vdef = U.vdef
type vref = U.vref

type label = symbol

(*************** Elaboration to Lexp *********************)

(* Pour la propagation des types bidirectionnelle, tout va dans `infer`,
 * sauf Lambda et Case qui vont dans `check`.  Je crois.  *)
type ltype = lexp
 and subst = lexp S.subst
 and lexp =
   | Imm of sexp                        (* Used for strings, ...  *)
   | SortLevel of sort_level
   | Sort of U.location * sort
   | Builtin of vdef * ltype
   | Var of vref
   | Susp of lexp * subst  (* Lazy explicit substitution: e[σ].  *)
   (* This "Let" allows recursion.  *)
   | Let of U.location * (vdef * lexp * ltype) list * lexp
   | Arrow of arg_kind * vdef option * ltype * U.location * lexp
   | Lambda of arg_kind * vdef * ltype * lexp
   | Call of lexp * (arg_kind * lexp) list (* Curried call.  *)
   | Inductive of U.location * label
                  * ((arg_kind * vdef * ltype) list) (* formal Args *)
                  * ((arg_kind * vdef option * ltype) list) SMap.t
   | Cons of vref * symbol (* = Type info * ctor_name  *)
   | Case of U.location * lexp
             * ltype (* The base inductive type over which we switch.  *)
             * ltype (* The type of the return value of all branches *)
             * (U.location * (arg_kind * vdef option) list * lexp) SMap.t
             * lexp option               (* Default.  *)
   | Metavar of int * subst * vdef
 (*   (\* For logical metavars, there's no substitution.  *\)
  *   | Metavar of (U.location * string) * metakind * metavar ref
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


type varbind =
  | Variable
  | ForwardRef
  | LetDef of lexp

module VMap = Map.Make (struct type t = int let compare = compare end)
type substitution = lexp VMap.t
type constraints  = (lexp * lexp) list
let empty_subst = (VMap.empty)

(********* Helper functions to use the Subst operations  *********)
(* This basically "ties the knot" between Subst and Lexp.
 * Maybe it would be cleaner to just move subst.ml into lexp.ml
 * and be done with it.  *)

let rec mkSusp e s =
  if S.identity_p s then e else
    (* We apply the substitution eagerly to some terms.
     * There's no deep technical rason for that:
     * it just seemed like a good idea to do it eagerly when it's easy.  *)
    match e with
    | Susp (e, s') -> mkSusp e (scompose s' s)
    | Var (l,v) -> slookup s l v
    | Metavar (vn, s', vd) -> Metavar (vn, scompose s' s, vd)
    | _ -> Susp (e, s)
and scompose s1 s2 = S.compose mkSusp s1 s2
and slookup s l v = S.lookup (fun l i -> Var (l, i))
                             (fun e o -> mkSusp e (S.shift o))
                             s l v
let ssink = S.sink (fun l i -> Var (l, i))

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
                     | _ -> U.internal_error "Registering a non-builtin")
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
 *                        then (U.internal_error "Overlapping substs")
 *                        else VMap.add v e s)
 *             s s' *)

let lexp_max_sort (k1, k2) =
  match k1,k2 with
  | Sort (_,l1), Sort (_, l2) -> max l1 l2
  | _ -> U.internal_error "finding the max of non-sorts!"

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
  | SortLevel (SLn _) -> U.dummy_location
  | Imm s -> sexp_location s
  | Var ((l,_),_) -> l
  | Builtin ((l, _), _) -> l
  | Let (l,_,_) -> l
  | Arrow (_,_,_,l,_) -> l
  | Lambda (_,(l,_),_,_) -> l
  | Call (f,_) -> lexp_location f
  | Inductive (l,_,_,_) -> l
  | Cons (_,(l,_)) -> l
  | Case (l,_,_,_,_,_) -> l
  | Susp (e, _) -> lexp_location e
  (* | Susp (_, e) -> lexp_location e *)
  | Metavar (_,_,(l,_)) -> l


(********* Normalizing a term *********)

let vdummy = (U.dummy_location, "dummy")
let maybev mv = match mv with None -> vdummy | Some v -> v

let rec push_susp e s =            (* Push a suspension one level down.  *)
  match e with
  | Imm _ -> e
  | SortLevel _ -> e
  | Sort (l, Stype e) -> Sort (l, Stype (mkSusp e s))
  | Sort (l, _) -> e
  | Builtin _ -> e
  | Let (l, defs, e)
    -> let s' = L.fold_left (fun s (v, _, _) -> ssink v s) s defs in
      let (_,ndefs) = L.fold_left (fun (s,ndefs) (v, def, ty)
                                   -> (ssink v s,
                                      (v, mkSusp e s', mkSusp ty s) :: ndefs))
                                  (s, []) defs in
      Let (l, ndefs, mkSusp e s')
  | Arrow (ak, v, t1, l, t2)
    -> Arrow (ak, v, mkSusp t1 s, l, mkSusp t2 (ssink (maybev v) s))
  | Lambda (ak, v, t, e) -> Lambda (ak, v, mkSusp t s, mkSusp e (ssink v s))
  | Call (f, args) -> Call (mkSusp f s,
                           L.map (fun (ak, arg) -> (ak, mkSusp arg s)) args)
  | Inductive (l, label, args, cases)
    -> let (_, nargs) = L.fold_left (fun (s, nargs) (ak, v, t)
                                    -> (ssink v s, (ak, v, mkSusp t s) :: nargs))
                                   (s, []) args in
      let ncases = SMap.map (fun args
                             -> let (_, ncase)
                                 = L.fold_left (fun (s, nargs) (ak, v, t)
                                                -> (ssink (maybev v) s,
                                                   (ak, v, mkSusp t s)
                                                   :: nargs))
                                               (s, []) args in
                               ncase)
                            cases in
      Inductive (l, label, nargs, ncases)
  | Cons _ -> e
  | Case (l, e, it, ret, cases, default)
    -> Case (l, mkSusp e s, mkSusp it s, mkSusp ret s,
            SMap.map (fun (l, cargs, e)
                      -> let s' = L.fold_left (fun s carg
                                              -> match carg with
                                                | (_,None) -> s
                                                | (_,Some v) -> ssink v s)
                                             s cargs in
                        (l, cargs, mkSusp e s'))
                     cases,
            match default with
            | None -> default
            | Some e -> Some (mkSusp e s))
  (* Susp should never appear around Var/Susp/Metavar because mkSusp
   * pushes the subst into them eagerly.  IOW if there's a Susp(Var..)
   * or Susp(Metavar..) it's because some chunk of code should use mkSusp
   * rather than Susp.
   * But we still have to handle them here, since push_susp is called
   * in many other cases than just when we bump into a Susp.  *)
  | Susp (e,s') -> push_susp e (scompose s' s)
  | (Var _ | Metavar _) -> nosusp (mkSusp e s)

let nosusp e =                  (* Return `e` without `Susp`.  *)
  match e with
    | Susp(e, s) -> push_susp e s
    | _ -> e

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
    | Builtin _ -> "Builtin"
    | _ -> "lexp_to_string: not implemented"

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
  | SortLevel (SLn n) -> Pimm (Integer (U.dummy_location, n))
  | SortLevel (SLsucc e) -> Pcall (Pvar (lexp_location e, "S"),
                                  [pexp_unparse (lexp_unparse e)])
  | Imm s -> Pimm s
  | Builtin (b,name,t) -> Pvar (U.dummy_location, name)
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
    -> (U.internal_error "Can't print a non-Var-typed Constructor")
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
    (* (U.internal_error "Can't print a Susp") *)

let lexp_print e = sexp_print (pexp_unparse (lexp_unparse e))

(* let rec lexp_type (env: (lexp option * lexp) VMap.t) e : lexp =
 *   let rec follow e =
 *     match e with
 *     | Var (_,v) -> vmap_getval v
 *     | Metavar (_,_,r) -> (match !r with MetaSet e -> follow e | _ -> e)
 *     | _ -> e
 *   and vmap_getval (v : var) =
 *     match VMap.find v env with (Some e, _) -> follow e
 *                              | _ -> Var (U.dummy_location, v) in
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
 *   (\* | Imm (String _) -> Var (U.dummy_location, var_string) *\)
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
 *     Arrow (ak, Some var, t, U.dummy_location,
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

let pretty_ppctx  = ref (true , 0, true, false, true,  4, true)
let compact_ppctx = ref (false, 0, true, false, true,  4, false)
let debug_ppctx   = ref (false, 0, true, true , false, 4, true)

let rec lexp_print e = _lexp_print (!debug_ppctx) e
and _lexp_print ctx e = print_string (_lexp_to_str ctx e)

(*  Print a lexp into its typer equivalent                              *)
(*  Depending on the print_context the output can be correct typer code *)
(*  This function will be very useful when debugging generated code     *)

(* If I remember correctly ocaml doc, concat string is actually terrible *)
(* It might be better to use a Buffer. *)
and lexp_to_str exp = _lexp_to_str (!debug_ppctx) exp

(* FIXME: We don't want lexp_to_str, instead we want lexp_to_pexp (aka
 * "unparse"), which we can then combine with pexp_to_sexp, etc...  *)
and _lexp_to_str ctx exp =
    (* create a string instead of printing *)

    let (pretty, indent, ptype, pindex, _, isize, color) = ctx in
    let lexp_to_str = _lexp_to_str ctx in

    (* internal context, when parsing let *)
    let inter_ctx = (pretty, indent + 1, ptype, pindex, false, isize, color) in

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

    let keyword str  = magenta ^ str ^ reset in
    let error str    = red     ^ str ^ reset in
    let tval str     = yellow  ^ str ^ reset in
    let fun_call str = cyan    ^ str ^ reset in

    let index idx = let str = _index idx in if idx < 0 then (error str) else
        (green ^ str ^ reset) in

    let kind_str k =
        match k with
            | Aexplicit -> "->" | Aimplicit -> "=>" | Aerasable -> "≡>" in

    let kindp_str k =
        match k with
            | Aexplicit -> ":" | Aimplicit -> "::" | Aerasable -> ":::" in

    match exp with
        | Imm(value) -> (match value with
            | String (_, s) -> tval ("\"" ^ s ^ "\"")
            | Integer(_, s) -> tval (string_of_int s)
            | Float  (_, s) -> tval (string_of_float s)
            | e -> sexp_to_str e)

        | Susp (e, s) -> _lexp_to_str ctx (push_susp e s)

        | Var ((loc, name), idx) -> name ^ (index idx) ;

        | Metavar (idx, subst, (loc, name)) -> "?" ^ name ^ (index idx) (*TODO : print subst*)

        | Let (_, decls, body)   ->
            (* Print first decls without indent *)
            let h1, decls, idt_lvl =
                match _lexp_str_decls inter_ctx decls with
                    | h1::decls -> h1, decls, 2
                    | _ -> "", [], 1 in

            let decls = List.fold_left (fun str elem ->
                str ^ (make_indent 1) ^ elem ^ nl)
                    (h1 ^ nl) decls  in

            let n = String.length decls - 2 in
            (* remove last newline *)
            let decls = (String.sub decls 0 n) in

            (keyword "let ") ^ decls ^ (keyword " in ") ^ newline ^
                (make_indent idt_lvl) ^ (lexp_to_stri 1 body)

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
            let str, idx, inner_parens, outer_parens = match fname with
                | Var((_, name), idx)    -> name, idx, false, true
                | Builtin ((_, name), _) -> name,  0,  false, true
                | Lambda _               -> "__",  0,  true,  false
                | Cons _                 -> "__",  0,  false, false
                | _                      -> "__", -1,  true,  true  in

            let binop_str op (_, lhs) (_, rhs) =
                (lexp_to_str lhs) ^ op ^ (index idx) ^ " " ^ (lexp_to_str rhs) in

            let add_parens bl str =
                if bl then "(" ^ str ^ ")" else str in

            match (str, args) with
                (* Special Operators *)
                (* FIXME: Get rid of these special cases:
                 * Either use the boring (_+_ e1 e2) notation, or check the
                 * grammar to decide when we can use the infix notation and
                 * when to add parenthese.  *)
                | ("_=_", [lhs; rhs]) -> binop_str " =" lhs rhs
                | ("_+_", [lhs; rhs]) -> binop_str " +" lhs rhs
                | ("_-_", [lhs; rhs]) -> binop_str " -" lhs rhs
                | ("_/_", [lhs; rhs]) -> binop_str " /" lhs rhs
                | ("_*_", [lhs; rhs]) -> binop_str " *" lhs rhs
                (* not an operator *)
                | _ ->
                    let args = List.fold_left
                        (fun str (_, lxp) -> str ^ " " ^ (lexp_to_str lxp))
                        "" args in

                    let str = fun_call (lexp_to_str fname) in
                    let str = add_parens inner_parens str in
                    let str = str ^ args in
                        add_parens outer_parens str)

        | Inductive (_, (_, name), [], ctors) ->
            (keyword "inductive_") ^ " (" ^ name ^") " ^
                                            (lexp_str_ctor ctx ctors)

        | Inductive (_, (_, name), args, ctors) ->
            let args_str = List.fold_left (fun str (arg_kind, (_, name), ltype) ->
                str ^ " (" ^ name ^ " " ^ (kindp_str arg_kind) ^ " "
                ^ (lexp_to_str ltype) ^ ")")
                "" args in

            (keyword "inductive_") ^ " (" ^ name ^ args_str ^") " ^
                                            (lexp_str_ctor ctx ctors)

        | Case (_, target, tpe, _ret, map, dflt) ->(
            let str = (keyword "case ") ^ (lexp_to_str target)
            (* FIXME: `tpe' is the *base* type of `target`.  E.g. if `target`
             * is a `List Int`, then `tpe` will be `List`.
               ^ * " : " ^ (lexp_to_str tpe) *) in
            let arg_str arg =
                List.fold_left (fun str v ->
                    match v with
                        | (_,None) -> str ^ " _"
                        | (_, Some (_, n)) -> str ^ " " ^ n) "" arg in


            let str = SMap.fold (fun k (_, arg, exp) str ->
                str ^ nl ^ (make_indent 1) ^
                    "| " ^ (fun_call k) ^ (arg_str arg) ^ " => " ^ (lexp_to_stri 1 exp))
                map str in

            match dflt with
                | None -> str
                | Some df ->
                    str ^ nl ^ (make_indent 1) ^ "| _ => " ^ (lexp_to_stri 1 df))

        | Builtin ((_, name), _) -> name

        | Sort (_, Stype lvl) -> (match lvl with
            | SortLevel (SLn 0) -> "Type"
            | SortLevel (SLn v) -> "Type" ^ (string_of_int v)
            | _ -> "Type")

        | _ -> print_string "Printing Not Implemented\n"; "-- --"

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

    (* let make_indent idt =
        if pretty then (make_line ' ' ((idt + indent) * isize)) else "" in *)

    let sepdecl = (if sepdecl then "\n" else "") in

    let type_str name lxp = (if ptype then (
         name ^ " : " ^ (lexp_to_str lxp) ^ ";") else "") in

    let ret = List.fold_left (fun str ((_, name), lxp, ltp) ->
        let str = if ptype then (type_str name ltp)::str else str in
            (name ^ " = " ^ (lexp_to_str lxp) ^ ";" ^ sepdecl)::str)

        [] decls in
        List.rev ret
