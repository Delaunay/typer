(* opslexp.ml --- Operations on Lexps

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
module SMap = U.SMap
(* open Lexer *)
open Sexp
module P = Pexp
(* open Myers *)
(* open Grammar *)
open Lexp
module E = Elexp
module L = Lexp

(* open Unify *)
module S = Subst
(* module L = List *)
module B = Builtin
module DB = Debruijn

let conv_erase = true              (* If true, conv ignores erased terms. *)

(* Lexp context *)

let lookup_type (ctx : DB.lexp_context) vref =
  let (_, i) = vref in
  let (_, _, _, t) = Myers.nth i ctx in
  mkSusp t (S.shift (i + 1))

let lookup_value (ctx : DB.lexp_context) vref =
  let (_, i) = vref in
  match Myers.nth i ctx with
  | (o, _, LetDef v, _) -> Some (push_susp v (S.shift (i + 1 - o)))
  | _ -> None

(********* Testing if two types are "convertible" aka "equivalent"  *********)

let rec conv_arglist_p s1 s2 args1 args2 : bool =
  List.fold_left2
    (fun eqp (ak1,t1) (ak2,t2) ->
      eqp && ak1 = ak2 && conv_p' s1 s2 t1 t2)
    true args1 args2

(* Returns true if e₁ and e₂ are equal (upto alpha/beta/...).  *)
and conv_p' (s1:lexp S.subst) (s2:lexp S.subst) e1 e2 : bool =
  let conv_p = conv_p' s1 s2 in
  (* e1 == e2    !! Looks obvious, but can fail because of s1 and s2 !!  *)
  match (e1, e2) with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
    | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
    | (SortLevel (sl1), SortLevel (sl2)) -> sl1 == sl2
    | (Sort (_, s1), Sort (_, s2)) -> s1 = s2
    | (Builtin ((_, s1), _), Builtin ((_, s2), _)) -> s1 == s2
    (* BEWARE: When we'll make expand let-defined vars here, we'll have to
     * be careful not to introduce infinite-recursion.  *)
    | (Var (l1, v1), e2) when not (S.identity_p s1) ->
       conv_p' S.identity s2 (slookup s1 l1 v1) e2
    | (e1, Var (l2, v2)) when not (S.identity_p s2) ->
       conv_p' s1 S.identity e1 (slookup s2 l2 v2)
    | (Var (_, v1), Var (_, v2)) -> v1 == v2
    | (Susp (e1, s1'), e2) -> conv_p' (scompose s1' s1) s2 e1 e2
    | (e1, Susp (e2, s2')) -> conv_p' s1 (scompose s2' s2) e1 e2
    | (Arrow (ak1, vd1, t11, _, t12), Arrow (ak2, vd2, t21, _, t22))
      -> ak1 == ak2 && conv_p t11 t21
        && conv_p' (match vd1 with None -> s1 | Some l -> ssink l s1)
                  (match vd2 with None -> s2 | Some l -> ssink l s2)
                  t12 t22
    | (Lambda (ak1, l1, t1, e1), Lambda (ak2, l2, t2, e2))
      -> ak1 == ak2 && conv_p t1 t2 && conv_p' (ssink l1 s1) (ssink l2 s2) e1 e2
    | (Call (f1, args1), Call (f2, args2))
      -> conv_p f1 f2 && conv_arglist_p s1 s2 args1 args2
    | (Inductive (_, l1, args1, cases1), Inductive (_, l2, args2, cases2))
      -> let rec conv_args s1 s2 args1 args2 =
          match args1, args2 with
          | ([], []) -> true
          | ((ak1,l1,t1)::args1, (ak2,l2,t2)::args2)
            -> ak1 == ak2 && conv_p' s1 s2 t1 t2
              && conv_args (ssink l1 s1) (ssink l2 s2) args1 args2
          | _,_ -> false in
        let rec conv_fields s1 s2 fields1 fields2 =
          match fields1, fields2 with
          | ([], []) -> true
          | ((ak1,vd1,t1)::fields1, (ak2,vd2,t2)::fields2)
            -> ak1 == ak2 && conv_p' s1 s2 t1 t2
              && conv_fields (match vd1 with None -> s1 | Some l1 -> ssink l1 s1)
                            (match vd2 with None -> s2 | Some l2 -> ssink l2 s2)
                            fields1 fields2
          | _,_ -> false in
        l1 == l2 && conv_args s1 s2 args1 args2
        && SMap.equal (conv_fields s1 s2) cases1 cases2
    | (Cons (t1, l1), Cons (t2, l2)) -> l1 == l2 && conv_p t1 t2
    (* FIXME: Various missing cases, such as Let, Case, and beta-reduction.  *)
    | (_, _) -> false

and conv_p e1 e2 = conv_p' S.identity S.identity e1 e2


(* Reduce to weak head normal form.
 * WHNF implies:
 * - Not a Let.
 * - Not a let-bound variable.
 * - Not a Susp.
 * - Not an instantiated Metavar.
 * - Not a Call (Lambda _).
 * - Not a Call (Call _).
 * - Not a Call (_, []).
 * - Not a Case (Cons _).
 * FIXME: This should be memoized!
 *
 * BEWARE: As a general rule lexp_whnf should not be used on actual *code*
 * but only on *types*.  If you must use it on code, be sure to use its
 * return value as little as possible since WHNF will inherently introduce
 * call-by-name behavior.  *)
let rec lexp_whnf e (ctx : DB.lexp_context) = match e with
  (* | Let (_, defs, body) -> FIXME!!  Need recursive substitutions!  *)
  | Var v -> (match lookup_value ctx v with
             | None -> e
             (* We can do this blindly even for recursive definitions!
              * IOW the risk of inf-looping should only show up when doing
              * things like full normalization (e.g. lexp_conv_p).  *)
             | Some e' -> lexp_whnf e' ctx)
  | Susp (e, s) -> lexp_whnf (push_susp e s) ctx
  | Call (e, []) -> lexp_whnf e ctx
  | Call (e, (((_, arg)::args) as xs)) ->
     (match lexp_whnf e ctx with
      | Lambda (_, _, _, body) ->
         (* Here we apply whnf to the arg eagerly to kind of stay closer
          * to the idea of call-by-value, although in this context
          * we can't really make sure we always reduce the arg to a value.  *)
         lexp_whnf (Call (push_susp body (S.substitute (lexp_whnf arg ctx)),
                          args))
                   ctx
      | Call (e', xs1) -> Call (e', List.append xs1 xs)
      | e' -> Call (e', xs))
  | Case (l, e, bt, rt, branches, default) ->
     let reduce name aargs =
       try
         let (_, _, branch) = SMap.find name branches in
         let (subst, _)
           = List.fold_left
               (fun (s,d) (_, arg) ->
                 (S.Cons (L.mkSusp (lexp_whnf arg ctx) (S.shift d), s),
                  d + 1))
               (S.identity, 0)
               aargs in
         lexp_whnf (push_susp branch subst) ctx
       with Not_found
            -> match default
              with | Some default -> lexp_whnf default ctx
                   | _ -> U.msg_error "WHNF" l
                                     ("Unhandled constructor " ^
                                        name ^ "in case expression");
                         Case (l, e, bt, rt, branches, default) in
     (match lexp_whnf e ctx with
      | Cons (_, (_, name)) -> reduce name []
      | Call (Cons (_, (_, name)), aargs) -> reduce name aargs
      | e' -> Case (l, e', bt, rt, branches, default))
  | e -> e


(********* Testing if a lexp is properly typed  *********)


let assert_type e t t' =
  if conv_p t t' then ()
  else U.msg_error "TC" (lexp_location e) "Type mismatch"; ()

let sort_compose l s1 s2 =
  match s1, s2 with
  | (Stype (SortLevel (SLn n1)), Stype (SortLevel (SLn n2)))
    (* Basic predicativity rule.  *)
    -> Stype (SortLevel (SLn (max n1 n2)))
  | ( (StypeLevel, Stype (SortLevel (SLn _)))
    | (StypeLevel, StypeOmega)
    (* | (Sort (_, Stype (SortLevel (SLn _))), Sort (_, StypeOmega)) *))
    -> StypeOmega
  | _,_ -> (U.msg_error "TC" l
                       "Mismatch sorts for arg and result";
           StypeOmega)

(* "check ctx e" should return τ when "Δ ⊢ e : τ"  *)
let rec check ctx e =
  (* let mustfind = assert_type e t in *)
  match e with
  | Imm (Float (_, _)) -> B.type_float
  | Imm (Integer (_, _)) -> B.type_int
  | Imm (Epsilon | Block (_, _, _) | Symbol _ | String (_, _) | Node (_, _))
    -> (U.msg_error "TC" (lexp_location e) "Unsupported immediate value!";
       B.type_int)
  | SortLevel (_) -> B.type_level
  | Sort (l, Stype (SortLevel (SLn n)))
    -> Sort (l, Stype (SortLevel (SLn (1 + n))))
  | Sort (_, (StypeOmega|StypeLevel))
    -> (U.msg_error "TC" (lexp_location e) "Reached Unreachable sorts!";
       B.type_omega)
  | Sort (_, (Stype _))
    -> (U.msg_error "TC" (lexp_location e) "Non-level arg to Type!";
       B.type_omega)
  | Builtin (_, t) -> t
  (* FIXME: Check recursive references.  *)
  | Var v -> lookup_type ctx v
  | Susp (e, s) -> check ctx (push_susp e s)
  | Let (_, defs, e)
    -> let tmp_ctx =
        List.fold_left (fun ctx (v, e, t)
                        -> (match check ctx t with
                           | Sort (_, Stype _) -> ()
                           | _ -> (U.msg_error "TC" (lexp_location t)
                                              "Def type is not a type!"; ()));
                          DB.lctx_extend ctx v ForwardRef t)
                       ctx defs in
      let _ = List.iter (fun (v, e, t) -> assert_type e t (check tmp_ctx e))
                        defs in
      let new_ctx = DB.lctx_extend_rec ctx defs in
      check new_ctx e
  | Arrow (ak, v, t1, l, t2)
    -> (let k1 = check ctx t1 in
       let k2 = check (DB.lexp_ctx_cons ctx 0 v Variable t1) t2 in
       match k1, k2 with
       | (Sort (_, s1), Sort (_, s2))
         -> Sort (l, sort_compose l s1 s2)
       | (Sort (_, _), _) -> (U.msg_error "TC" (lexp_location t2)
                            "Not a proper type";
                             Sort (l, StypeOmega))
       | (_, _) -> (U.msg_error "TC" (lexp_location t1)
                               "Not a proper type";
                   Sort (l, StypeOmega)))
  | Lambda (ak, ((l,_) as v), t, e)
    -> ((match check ctx t with
        | Sort _ -> ()
        | _ -> (U.msg_error "TC" (lexp_location t)
                           "Formal arg type is not a type!"; ()));
       Arrow (ak, Some v, t, l,
              (* FIXME: If ak is Aerasable, make sure the var only appears
               * in type annotations.  *)
              check (DB.lctx_extend ctx v Variable t) e))
  | Call (f, args)
    -> let ft = check ctx f in
      List.fold_left (fun ft (ak,arg)
                   -> let at = check ctx arg in
                     match ft with
                     | Arrow (ak', v, t1, l, t2)
                       -> if not (ak == ak') then
                            (U.msg_error "TC" (lexp_location arg)
                                         "arg kind mismatch"; ())
                          else ();
                         assert_type arg t1 at;
                         mkSusp t2 (S.substitute arg)
                     | _ -> (U.msg_error "TC" (lexp_location arg)
                                        "Calling a non function!"; ft))
                  ft args
  | Inductive (l, label, args, cases)
    -> let rec arg_loop args s ctx =
        match args with
        | [] -> Sort (l, s)
        | (ak, v, t)::args
          -> let s' = match check ctx t with
              | Sort (_, s') -> s'
              | _ -> (U.msg_error "TC" (lexp_location t)
                                 "Field type is not a Type!";
                     Stype (SortLevel (SLn 0))) in
            Arrow (ak, Some v, t, lexp_location t,
                   (* FIXME: `sort_compose` doesn't do what we want!  *)
                   arg_loop args (sort_compose l s s')
                            (DB.lctx_extend ctx v Variable t)) in
      let tct = arg_loop args (Stype (SortLevel (SLn 0))) ctx in
      (* FIXME: Check cases!  *)
      tct
  | Case (l, e, it, ret, branches, default)
    -> let rec call_split e =
        match e with
        | Call (f, args) -> let (f',args') = call_split f in (f', args' @ args)
        | _ -> (e,[]) in
      (match call_split (check ctx e) with
       | Inductive (_, _, fargs, constructors), aargs ->
          let rec mksubst s fargs aargs =
            match fargs, aargs with
            | [], [] -> s
            | _farg::fargs, (_ak, aarg)::aargs
              (* We don't check aarg's type, because we assume that `check`
               * returns a valid type.  *)
              -> mksubst (S.cons aarg s) fargs aargs
            | _,_ -> (U.msg_error "TC" l
                                 "Wrong arg number to inductive type!"; s) in
          let s = mksubst S.identity fargs aargs in
          SMap.iter
            (fun name (l, vdefs, branch)
             -> let fieldtypes = SMap.find name constructors in
               let rec mkctx ctx s vdefs fieldtypes =
                 match vdefs, fieldtypes with
                 | [], [] -> ctx
                 (* FIXME: If ak is Aerasable, make sure the var only
                  * appears in type annotations.  *)
                 | (ak, vdef)::vdefs, (ak', vdef', ftype)::fieldtypes
                   -> mkctx (DB.lexp_ctx_cons ctx 0
                                             vdef Variable (mkSusp ftype s))
                           (S.cons (Var ((match vdef with Some vd -> vd
                                                        | None -> (l, "_")),
                                         0)) s)
                           vdefs fieldtypes
                 | _,_ -> (U.msg_error "TC" l
                                      "Wrong number of args to constructor!";
                          ctx) in
               let nctx = mkctx ctx s vdefs fieldtypes in
               assert_type branch ret (check nctx branch))
            branches;
          (match default with
           | Some d -> assert_type d ret (check ctx d)
           | _ -> ())
       | _,_ -> U.msg_error "TC" l "Case on a non-inductive type!");
      ret
  | Cons (t, (_, name))
    -> (match lexp_whnf t ctx with
       | Inductive (l, _, fargs, constructors) as it
         -> let fieldtypes = SMap.find name constructors in
           let rec indtype fargs start_index =
             match fargs with
             | [] -> []
             | (ak, vd, _)::fargs -> (ak, Var (vd, start_index))
                                    :: indtype fargs (start_index - 1) in
           let rec fieldargs fieldtypes =
             match fieldtypes with
             | [] -> Call (it, indtype fargs (List.length fieldtypes
                                             + List.length fargs - 1))
             | (ak, vd, ftype) :: fieldtypes
               -> Arrow (ak, vd, ftype, lexp_location ftype,
                                       fieldargs fieldtypes) in
           let rec buildtype fargs =
             match fargs with
             | [] -> fieldargs fieldtypes
             | (ak, ((l,_) as vd), atype) :: fargs
               -> Arrow (P.Aerasable, Some vd, atype, l,
                        buildtype fargs) in
           buildtype fargs
       | _ -> (U.msg_error "TC" (lexp_location e)
                          "Cons of a non-inductive type!";
              B.type_int))

(*********** Type erasure, before evaluation.  *****************)

let rec erase_type (lxp: L.lexp): E.elexp =

    match lxp with
        | L.Imm(s)          -> E.Imm(s)
        | L.Builtin(v, _)   -> E.Builtin(v)
        | L.Var(v)          -> E.Var(v)
        | L.Cons(_, s)      -> E.Cons(s)

        | L.Lambda (P.Aerasable, _, _, body) ->
          (* The var shouldn't appear in body, basically, but we need
           * to adjust the debruijn indices of other vars, hence the subst.  *)
          erase_type (L.push_susp body (S.substitute Builtin.type0))
        | L.Lambda (_, vdef, _, body) ->
          E.Lambda (vdef, erase_type body)

        | L.Let(l, decls, body)       ->
            E.Let(l, (clean_decls decls), (erase_type body))

        | L.Call(fct, args) ->
            E.Call((erase_type fct), (filter_arg_list args))

        | L.Case(l, target, _, _, cases, default) ->
            E.Case(l, (erase_type target), (clean_map cases),
                                         (clean_maybe default))

        | L.Susp(l, s)                -> erase_type (L.push_susp l s)

        (* To be thrown out *)
        | L.Arrow _                   -> E.Type
        | L.SortLevel _               -> E.Type
        | L.Sort _                    -> E.Type
        (* Still useful to some extent.  *)
        | L.Inductive(l, label, _, _) -> E.Inductive(l, label)

and filter_arg_list lst =
    let rec filter_arg_list lst acc =
        match lst with
            | (kind, lxp)::tl ->
                let acc = if kind != P.Aerasable then
                    (erase_type lxp)::acc else acc in
                        filter_arg_list tl acc
            | [] -> List.rev acc in
        filter_arg_list lst []

and clean_decls decls =
   List.map (fun (v, lxp, _) -> (v, (erase_type lxp))) decls

and clean_maybe lxp =
    match lxp with
        | Some lxp -> Some (erase_type lxp)
        | None -> None

and clean_map cases =
    let clean_arg_list lst =
        let rec clean_arg_list lst acc =
            match lst with
                | (kind, var)::tl ->
                    let acc = if kind != P.Aerasable then
                        var::acc else acc in
                            clean_arg_list tl acc
                | [] -> List.rev acc in
        clean_arg_list lst [] in

    SMap.mapi (fun key (l, args, expr) ->
        (l, (clean_arg_list args), (erase_type expr))) cases

    
