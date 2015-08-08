(* elaborate.ml --- Macro expansion and type inference: Pexp -> Lexp terms.

Copyright (C) 2011-2014  Free Software Foundation, Inc.

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
open Lexer
open Sexp
open Pexp
open Lexp
open Unify

(* Elaboration can not always proceed sequentially through the code.
 * So it uses residues, which come in different flavors:
 * - unification constraints: these come from unsolved higher-order
 *   unifications.
 * - macro-expansions: these are delayed as much as possible so their type
 *   environment is as complete as possible.
 * - implicit argument instantiations: when an expression's type is
 *   a function that accepts an implicit argument, we need to know the
 *   context in order to know whether to pass this function as is or to try
 *   and infer an argument.
 * When we're done traversing a term, we have to resolve those residues.
 * This is done as follows:
 * - first re-try to unify all constraints first.
 * - then try to guess the implicit arguments.
 * - then expand all the macro-calls.
 * - if we made progress, but there are still residues, go try again,
 *   else if there are left-over implicit argument residues, make an arbitrary
 *   choice and try again.
 *)
       
type delayed =
  (* | DelayedDecl of var * ltype * ltype * pending * var SMap.t *)
  | DelayedDef of var * lexp * ltype * pending * var SMap.t

let lexp_erase_fmvars fvs =
  List.map (fun (v,_) -> (v, Aerasable)) fvs

let lset_add s x = if List.mem x s then s else x::s
let lset_append s1 s2 = List.fold_left lset_add s1 s2
           
let rec lexp_free_metavars sl e fvs =
  let lexp_free_metavars = lexp_free_metavars sl in
  match e with
  | Sort (_, e) -> lexp_free_metavars e fvs
  | SortLevel (SLsucc e) -> lexp_free_metavars e fvs
  | SortLevel (SLn _ | SLlevel | SLomega) -> fvs
  | (Imm _ | Builtin _ | Var _) -> fvs
  | Let (_, decls, body)
    (* FIXME: Some let-bindings will also be erasable, but since they're
     * not marked as such, we have no easy way to figure that out here.  *)
    -> List.fold_left (fun fvs (_,e,t)
                      -> lset_append
                          (lexp_erase_fmvars (lexp_free_metavars t []))
                          (lexp_free_metavars e fvs))
                     (lexp_free_metavars body fvs)
                     decls
  | Arrow (_,_,t1,_,t2) -> lexp_free_metavars t1 (lexp_free_metavars t2 fvs)
  | Lambda (_,_,t,e)
    -> lset_append (lexp_erase_fmvars (lexp_free_metavars t []))
                  (lexp_free_metavars e fvs)
  | Call (f,args)
    -> List.fold_left (fun fvs (kind,arg)
                      -> let fvs1 = lexp_free_metavars arg [] in
                        lset_append (match kind with
                                     | Aerasable -> lexp_erase_fmvars fvs1
                                     | _ -> fvs1)
                                    fvs)
                     (lexp_free_metavars f fvs)
                     args
  | Inductive (_,t,cases)
    -> SMap.fold (fun _ case fvs
                 -> lexp_free_metavars case fvs)
                cases
                (lexp_free_metavars t fvs)
  | Cons (t,_) -> lset_append (lexp_erase_fmvars (lexp_free_metavars t [])) fvs
  | Case (_,e,t,branches,default)
    -> let fvs = match default with None -> fvs
                                 | Some e -> lexp_free_metavars e fvs in
      let fvs = lexp_free_metavars t fvs in
      let fvs = lexp_free_metavars e fvs in
      SMap.fold (fun _ (_,_,branch) fvs
                 -> lexp_free_metavars branch fvs)
                branches fvs
  (* FIXME: we don't actually want WHNF here!  *)
  | Susp (subst, e) -> lexp_free_metavars (lexp_whnf subst e) fvs
  | Metavar ((l,_), MetaFoF, mvar) -> fvs
  | Metavar ((l,_), MetaGraft _, mvar)
    -> match !mvar,sl with
      | MetaSet e, _ -> lexp_free_metavars e fvs
      | MetaUnset (_, t, ScopeLevel sl'), ScopeLevel sl when sl' > sl
        -> lset_add (match t with
                    | Some t -> lset_append (lexp_erase_fmvars
                                              (lexp_free_metavars t []))
                                           fvs
                    | None -> fvs)
                   (mvar, Aimplicit)
      | _ -> fvs

let msg_unify_fail l e1 e2
  = msg_error l ("Type mismatch:");
    msg_info (lexp_location e1) "";
    sexp_print (pexp_unparse (lexp_unparse e1)); print_newline ();
    print_string " != "; print_newline ();
    msg_info (lexp_location e2) "";
    sexp_print (pexp_unparse (lexp_unparse e2)); print_newline ()
    
let lexp_unify_catch l venv e1 e2 p
  = try lexp_unify venv e1 e2 p
    with Unify_fail (e1, e2)
         -> msg_unify_fail l e1 e2; []

(* elaborate does the following:
 * - parse a sexp into a lexp.
 * - expand macros (well, when it'll be implemented!).
 * - infer types.
 *)
let rec elaborate (sl : scope_level)
                  (env : token_env * grammar
                         * var SMap.t              (* Map symbols to vars.  *)
                         * metavar ref SMap.t ref  (* free vars. *)
                         * (lexp option * lexp) VMap.t)
                  (e : pexp) : (lexp * lexp * pending) =
  let elab = elaborate sl in
  match e with
  | Pimm (Integer _ as s) -> (Imm s, type_int, [])
  | Pimm (Float _ as s) -> (Imm s, type_float, [])
  (* | Pimm (String _ as s) -> (Imm s, Var (dummy_location, var_string), []) *)
  | Pimm (Block (l,pts,_))
    -> let (tenv,grm,senv,fvars,venv) = env in
      let ts = lex tenv pts in
      let (se,_) = sexp_parse_all grm ts None in
      let pe = pexp_parse se in
      elab env pe
  | Pimm s -> let l = sexp_location s in
             let (_,_,_,_,venv) = env in
             let (e,t) = mk_meta2 sl venv l in
             msg_error l "Unrecognized sexp element";
             (e, t, [])
  | Pvar (l, name) ->
    let (tenv,grm,senv,fvars,venv) = env in
    (try let v = SMap.find name senv in
         let (_,t) = VMap.find v venv in
         (* sexp_print (pexp_unparse (lexp_unparse (Var (l,v))));
          * print_string " has type ";
          * sexp_print (pexp_unparse (lexp_unparse t)); print_newline(); *)
         (Var (l,v), t, [])
     with Not_found ->
       let (_,_,_,fvars,venv) = env in
       let r = try SMap.find name (!fvars)
               with Not_found
                    -> let t = mk_meta sl venv l in
                      (* The `venv' of Fof is ignored.  *)
                      let r = ref (MetaUnset (VMap.empty, Some t, sl)) in
                      print_string ("Registering forward ref to "^name^"\n");
                      fvars := SMap.add name r (!fvars);
                      r
       in match !r with
          | MetaUnset (_, Some t, _) -> (Metavar ((l,name), MetaFoF, r), t, [])
          | MetaUnset (_, None, _) -> internal_error "Untyped FoF!?"
          | _ -> internal_error "Instantiated FoF!?")
  | Pmetavar (l, "_") -> let (_,_,_,_,venv) = env in
                        let (e,t) = mk_meta2 sl venv l in (e, t, [])
  | Pmetavar (l,name) -> msg_error l ("Unrecognized metavariable "^name);
                        let (_,_,_,_,venv) = env in
                        let (e,t) = mk_meta2 sl venv l in (e, t, [])
  | Pcall (f,[])
    -> msg_error (pexp_location f) "Pcall without arguments"; elab env f
  | Pcall (f,sargs) ->
    let (tenv,grm,senv,fvars,venv) = env in
    let (fe, ft, p) = elab env f in
    (* sexp_print (pexp_unparse f); print_string " has type ";
     * sexp_print (pexp_unparse (lexp_unparse ft)); print_newline(); *)
    let rec mk_call f args =
      match f with
      (* Streamline Call(Call(f,args1),args2), but only for function calls,
       * of course, not for macro calls.  *)
      | Call (f, args') -> mk_call f (args' @ args)
      | _ -> Call (f, args) in
    let rec mk_call' f rargs p t pargs =
      match (lexp_whnf VMap.empty t, pargs) with
      (* FIXME: there can be implicit/erasable args at the end as well!  *)
      | (_, []) -> (mk_call f (List.rev rargs), t, p)
      | (Arrow ((Aimplicit | Aerasable) as ak, v, t1, l, t2), _)
        -> let arg = mk_metat sl venv l t1 in
          let t' = match v with
            | None -> t2
            | Some (_,v) -> mk_subst v arg t2
          in mk_call' f ((ak, arg) :: rargs) p t' pargs
      | (_, parg :: pargs)
        -> let l = pexp_location e in
          let (v, t2) = (mkvar "iv", mk_meta sl venv l) in
          let (arg, argt, p') = elab env parg in
          let csts = lexp_unify_catch
                       l venv
                       (Arrow (Aexplicit, Some (dummy_location,v),
                               argt, dummy_location, t2))
                       t []
          in
          mk_call' f ((Aexplicit, arg) :: rargs)
                   (p' @ csts @ p)
                   (mk_subst v arg t2)
                   pargs
    in mk_call' fe [] p ft (List.map pexp_parse sargs)
  | Pcase (l,pe,pbranches,pdefault)
    -> let (tenv,grm,senv,fvars,venv) = env in
      let (e,te,p1) = elab env pe in
      let tbody = mk_meta sl venv l in
      let (branches, ti, p2)
        = List.fold_left
            (fun (branches, ti, p) ((l,name),pargs,pbody)
             -> try let v = SMap.find name senv in
                   let (c,ct) = VMap.find v venv in
                   let rec mk_body senv' venv' pargs ct
                     = match pargs, lexp_whnf VMap.empty ct with
                     | (ak1,(lp,pname)) :: pargs, Arrow (ak2, vopt, t1, la, t2)
                         when ak1 = ak2
                              || ak1 = Aimplicit && ak2 = Aerasable
                              || ak2 = Aimplicit && ak1 = Aerasable
                       -> let arg = mkvar pname in
                         let senv' = SMap.add pname arg senv in
                         let venv' = VMap.add arg (None, t1) venv in
                         let t2'
                           = (match vopt with
                              | None -> t2
                              | Some (lv,v) -> mk_subst v (Var (lp,arg)) t2) in
                         let (args, body, pb)
                           = mk_body senv' venv' pargs t2' in
                         ((ak2, (lp, arg))::args, body, pb)
                     | _, Arrow (ak2, vopt, t1, la, t2)
                         when ak2 != Aexplicit
                       -> let arg = mkvar "iv" in
                         let venv' = VMap.add arg (None, t1) venv in
                         let t2'
                           = (match vopt with
                              | None -> t2
                              | Some (lv,v) -> mk_subst v (Var (l,arg)) t2) in
                         let (args, body, pb)
                           = mk_body senv' venv' pargs t2' in
                         ((ak2, (l, arg))::args, body, pb)
                     (* | [], Arrow _
                      *   -> msg_error l "Too few arguments";
                      *     ([], ti, p) *)
                     | [], _
                       -> let (body,p)
                           (* FIXME: Here we force every branch to have the
                            * same type, and disallow any refinement!  *)
                           = elaborate_check sl
                                             (tenv,grm,senv',fvars,venv')
                                             pbody tbody in
                         (* FIXME: And here we force every branch to use
                          * the same type for `e'.
                          * Instead, we should only unify with a pattern
                          * taking ct's head, allowing the indices to vary.  *)
                         let p = lexp_unify_catch l venv te ct p in
                         ([], body, p)
                     | (_ :: pargs), _
                       -> msg_error l "Too many arguments";
                         mk_body senv' venv' pargs ct
                   in
                   match opt_map (lexp_whnf VMap.empty) c with
                   | Some (Cons (t,(_,name)))
                     -> if SMap.mem name branches then
                         (msg_error l ("Duplicate branch for tag `"^name^"'");
                          (branches, ti, p))
                       else
                         let p = match ti with
                           | None -> p
                           | Some ti -> lexp_unify_catch l venv ti t p in
                         let (args, body, p2) = mk_body senv venv pargs ct in
                         (SMap.add name (l,args,body) branches,
                          Some t, p2 @ p)
                   | _ -> msg_error l ("`"^name^"' is not a constructor");
                         (branches, ti, p)
               with Not_found -> msg_error l ("Unknown variable `"^name^"'");
                                (branches, ti, p))
            (SMap.empty, None, []) pbranches in
      (* FIXME: you forgot `default'!  *)
      (* FIXME: Not all cases handled yet!  *)
      (Case (l, e, (match ti with Some ti -> ti), branches, None),
       te, p1 @ p2)
                   
  | Pcons ((l1,typename),((l2,tagname) as tag))
    -> let (tenv,grm,senv,fvars,venv) = env in
      (try let v = SMap.find typename senv in
           match VMap.find v venv with
           | (Some t, _)
             -> let t = lexp_whnf VMap.empty t in
               (match t with
                | Inductive (_,_,consts)
                  -> (try let t = SMap.find tagname consts in
                         (Cons (Var (l1,v), tag), t, [])
                     with Not_found
                          -> msg_error l2 ("Unknown constructor name `"
                                          ^tagname^"'");
                            let (e,t) = mk_meta2 sl venv l2 in (e, t, []))
                | _ -> msg_error l1 ("Unknown data type `"^typename^"'");
                      let (e,t) = mk_meta2 sl venv l2 in (e, t, []))
           | _ -> msg_error l2 ("Unknown data type `"^typename^"'");
                 let (e,t) = mk_meta2 sl venv l2 in (e, t, [])
       with Not_found
            -> msg_error l2 ("Unknown variable `"^typename^"'");
              let (e,t) = mk_meta2 sl venv l2 in (e, t, []))
  | Pinductive (t,cases)
    (* FIXME: pay attenton to universe levels.  *)
    -> let (t',k,p) = elab env t in
      let (cases',p') = List.fold_left
                          (fun (cases,p) ((_,name),case)
                           -> let (case,k,p') = elab env case in
                             (SMap.add name case cases, p' @ p))
                          (SMap.empty, p) cases in
      (Inductive ((pexp_location e, mkvar "%ind%"), t', cases'),
       t', p')
  | Plambda (ak,(l,name),pt,pe)
    -> let (tenv,grm,senv,fvars,venv) = env in
      let (t1,k,p) = match pt with
        | None -> let (e,t) = mk_meta2 sl venv l in (e, t, [])
        | Some pt -> elab env pt in
      let v = mkvar name in
      let (e,t2,p') = elab (tenv,grm, SMap.add name v senv, fvars,
                            VMap.add v (None, t1) venv)
                           pe in
      let csts = lexp_unify_sort venv k [] in
      (Lambda (ak, (l, v), t1, e),
       Arrow (ak, Some (l, v), t1, l, t2),
       p @ p' @ csts)
  | Parrow (ak,v,t1,l,t2)
    -> let (tenv,grm,senv,fvars,venv) = env in
      let (t1,k1,p1) = elab env t1 in
      let csts1 = lexp_unify_sort venv k1 [] in
      let (v',senv',venv') = match v with
        | Some (l,name) -> let v' = mkvar name in
                          (Some (l,v'), SMap.add name v' senv,
                           VMap.add v' (None, t1) venv)
        | None -> (None,senv,venv) in
      let (t2,k2,p2) = elab (tenv,grm,senv',fvars,venv') t2 in
      let csts2 = lexp_unify_sort venv' k2 [] in
      (Arrow (ak, v', t1, l, t2), Sort (l, lexp_max_sort (k1, k2)),
       p1 @ p2 @ csts2 @ csts1)
  | Phastype (l,e,t)
    -> let (tenv,grm,senv,fvars,venv) = env in
      let (t,k',p') = elab env t in
      let (e,p) = elaborate_check sl env e t in
      let csts = lexp_unify_sort venv k' [] in
      (e, t, p @ p' @ csts)
  | Plet (l,decls,body) ->
    let (tenv,grm,senv,fvars,venv) = env in
    let (decls',pnames,delayed,senv',venv')
      = List.fold_left
          (elaborate_decl sl (tenv,grm))
          ([], SMap.empty, [], senv, venv) decls in
    let (be, bt, p') = elab (tenv,grm,senv',fvars,venv') body in
    (Let (l, List.rev decls', be), bt, p')
  | _ ->
    let (_,_,_,_,venv) = env in
    let t = mk_meta sl venv (pexp_location e) in
    let (e, p) = elaborate_check sl env e t in
    (e, t, p)


(* Like elaborate, but rather than take an pexp and return the corresponding
 * lexp and its type, it take a pexp along with its expected type and just
 * returns the corresponding lexp after checking its got the right type.  *)
and elaborate_check sl env (e : pexp) (t : lexp): (lexp * pending) =
  match e with
  | Plambda (ak,(l,name),pt,pe)
    -> (match lexp_whnf VMap.empty t with
       | Arrow (ak', v', t1, _, t2) when ak = ak'
         -> let (tenv,grm,senv,fvars,venv) = env in
           let v = mkvar name in
           let p = match pt with
             | None -> []
             | Some pt -> let (t1',k,p) = elaborate sl env pt in
                         let csts = lexp_unify_catch l venv t1 t1' [] in
                         p @ csts in
           let (e,p')
             = elaborate_check sl
                               (tenv,grm, SMap.add name v senv, fvars,
                                 VMap.add v (None, t1) venv)
                                pe
                                (match v' with
                                 | None -> t2
                                 | Some (l,v') -> mk_subst v' (Var (l,v)) t2) in
           (Lambda (ak, (l, v), t1, e), p @ p')
       | Arrow (ak', v', t1, _, t2) when ak' = Aerasable || ak = Aexplicit
         (* Add implicit/erasable lambda.
          * FIXME: We should also do this wrapping for other "values",
          * i.e. basically Pcons and Pvar.  *)
         -> let (tenv,grm,senv,fvars,venv) = env in
           let v = (match v' with
                    | None -> mkvar "%implicit%"
                    | Some (l,v') -> copy_var v') in
           let (e,p)
             = elaborate_check sl
                               (tenv,grm, senv, fvars,
                                 VMap.add v (None, t1) venv)
                                e
                                (match v' with
                                 | None -> t2
                                 | Some (l,v') -> mk_subst v' (Var (l,v)) t2) in
           (* FIXME: if t2 does not refer to v', then we should look for
            * a "free" metavar of type t1 in e!  *)
           (Lambda (ak', (l, v), t1, e), p)
       | _ -> elaborate_check' sl env e t)
  (* Default case: fall back on elaborate and check the result.  *)
  | _ -> elaborate_check' sl env e t

and elaborate_check' sl env (e : pexp) (t : lexp): (lexp * pending) =
    let (tenv,grm,senv,fvars,venv) = env in
    let (e',t',p) = elaborate sl env e in
    let csts = lexp_unify_catch (pexp_location e) venv t t' [] in
    (e', p @ csts)

(* Elaborate a variable declaration (i.e. a "<var> : <type>" declaration).  *)
and elaborate_var_decl sl
                       (tenv,grm) (* Surrounding env.  *)
                        (decls,    (* Processed declarations.  *)
                         pnames,   (* Names declared but not defined.  *)
                         delayed,  (* Delayed defs.  *)
                         senv,venv)
                        ((l,name) as s, e) =
  let v = mkvar name in
  let senv' = SMap.add name v senv in
  let pnames' = SMap.add name true pnames in
  let fvars' = ref (SMap.empty) in
  let (t,k,p) = elaborate sl (tenv,grm,senv,fvars',venv) e in
  (* Type declarations can't have forward references.  *)
  let p = lexp_resolve_pending venv p in (* Includes macro expansion.  *)
  (match p with _::_ -> msg_error l "Unresolved unification constraints"
              | _ -> ());
  (* FIXME: What should we do with k?  *)
  (* FIXME: Topological sort!  *)
  let t = SMap.fold (fun s r e
                     -> match !r with
                       | MetaUnset (_, Some t, _)
                         -> let v = (l,mkvar s) in
                           r := MetaSet (Var v);
                           Arrow (Aerasable, Some v, t, l, e)
                       | MetaUnset (_,None,_) -> internal_error "Untyped FoF!?"
                       | _ -> internal_error "Instantiated FoF!?")
                    (* FIXME: Not fvars but lexp_free_metavars e []  *)
                    !fvars' t in
  let venv' = VMap.add
                v (Some (Metavar (s, MetaFoF,
                                  (* The `venv' is (hopefully) ignored.  *)
                                  ref (MetaUnset (VMap.empty, Some t, sl)))),
                   t)
                venv
  in (decls, pnames', delayed, senv', venv')

(* Elaborate a variable definition (i.e. a "<var> = <exp>" declaration).  *)
and elaborate_var_def sl
                      (tenv,grm) (* Surrounding env.  *)
                      (decls,          (* Processed declarations.  *)
                       pnames,         (* Names declared but not defined.  *)
                       delayed,        (* Delayed defs.  *)
                       senv,venv)
                      ((l,name) as s, e) =
  let (v,senv',pnames',r,t,t_known,venv)
    = if SMap.mem name pnames then
        let v = SMap.find name senv in
        match VMap.find v venv with
        | (Some (Metavar (_, MetaFoF, r)), t)
          -> (v, senv, SMap.remove name pnames, r, t, true, venv)
        | _ -> internal_error "pname not in venv!"
      else
        let v = mkvar name in
        let t = mk_meta sl venv l in
        (* The `venv' field of MetaFoF should hopefully be ignored.  *)
        let r = ref (MetaUnset (VMap.empty, Some t, sl)) in
        (v, SMap.add name v senv, pnames, r, t, false,
         VMap.add v (Some (Metavar (s, MetaFoF, r)), t) venv) in
  let fvars' = ref (SMap.empty) in
  let (e,t',p)
    = if t_known then
        let (e,p) = elaborate_check (next_scope sl)
                                    (tenv,grm,senv',fvars',venv) e t in
        (e,t,p)
      (* If t is not yet known (i.e. there are no type annotations),
       * don't use elaborate_check because it would unify t' with t
       * before we get a chance to generalize the metavars.  *)
      else elaborate (next_scope sl)
                     (tenv,grm,senv',fvars',venv) e in
  let p = lexp_resolve_pending venv p in (* Includes macro expansion.  *)
  if SMap.is_empty !fvars' (* I.e. no undeclared forward references.  *)
     && p = [] then         (* And no unresolved constraints.  *)
    if t_known then
      (if not (lexp_free_metavars sl e [] = []) then (* Left over metavars!  *)
         msg_error l "Unresolved metavars";
       (r := MetaSet e;
        (((l,v), e, t)::decls, pnames', delayed, senv', venv)))
    else
      let fv = lexp_free_metavars sl e [] in
      (* FIXME: Topological sort!  *)
      let (e,t') = List.fold_left
                     (fun (e,t) (r,kind)
                      -> match !r with
                        | MetaUnset (_, Some t', _)
                          -> let v = (l,mkvar name) in
                            r := MetaSet (Var v);
                            (Lambda (kind, v, t', e),
                             Arrow (kind, Some v, t', l, t))
                        | MetaSet _
                          -> internal_error "Instantiated yet free metavar!?"
                        | MetaUnset (_, None, _)
                          -> internal_error "Free metavar of unknown type")
                     (e,t') fv in
      let _ = lexp_unify_catch l venv t t' [] in
      r := MetaSet e;
      (((l,v), e, t)::decls, pnames', delayed, senv', venv)
  else if SMap.is_empty !fvars' then
    (msg_error l ("Unresolved constraints in "^name);
     (decls, pnames, delayed, senv, venv))
  else
    (* let (e,t) = mk_meta2_closed l in
     * let delayed' = DelayedDef (v, e, t, p, !fvars) in
     * (((l,v), e, t)::decls, pnames', delayed', senv', venv') *)
    (msg_error l ("Forward reference in "^name^":");
     SMap.iter (fun name _ -> print_string ("   "^name^"\n")) (!fvars');
     (decls, pnames, delayed, senv, venv))

and elaborate_decl sl env state (s, e, ta) =
  if ta then
    (* It's a type-annotation which just *declares* the variable's type.  *)
    elaborate_var_decl sl env state (s, e)
  else
    (* The declaration actually *defines* the variable.  *)
    elaborate_var_def sl env state (s, e)
