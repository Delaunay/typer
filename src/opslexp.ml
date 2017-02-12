(* opslexp.ml --- Operations on Lexps

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
module DB = Debruijn

(* `conv_erase` is supposed to be safe according to the ICC papers. *)
let conv_erase = true          (* Makes conv ignore erased terms. *)

(* The safety of `impredicative_erase` is unknown.  But I like the idea.  *)
let impredicative_erase = true (* Allows erasable args to be impredicative. *)

(* Lexp context *)

let lookup_type  = DB.lctx_lookup_type
let lookup_value = DB.lctx_lookup_value

(** Extend a substitution S with a (mutually recursive) set
 * of definitions DEFS.
 * This is rather tricky.  E.g. for
 *
 *     (x₁ = e1; x₂ = e₂)
 *
 * Where x₁ will be DeBruijn #1 and x₂ will be DeBruijn #0,
 * we want a substitution of the form
 *
 *     (let x₂ = e₂ in e₂) · (let x₁ = e₁; x₂ = e₂ in e₁) · Id
 *
 * Because we want #2 in both e₂ and e₁ to refer to the nearest variable in
 * the surrouding context, but the substitution for #0 (defined here as
 * `let x₂ = e₂ in e₂`) will be interpreted in the remaining context,
 * which already provides "x₁".
 *)
(* FXIME: This creates an O(N^2) tree from an O(N) `let`!  *)
let rec lexp_defs_subst l s defs = match defs with
  | [] -> s
  | (_, lexp, _) :: defs'
    -> lexp_defs_subst l (S.cons (mkLet (l, defs, lexp)) s) defs'

(** Convert a lexp_context into a substitution.  *)

let rec lctx_to_subst lctx =
  match DB.lctx_view lctx with
  | DB.CVempty -> Subst.identity
  | DB.CVlet (_, LetDef e, _, lctx)
    -> let s = lctx_to_subst lctx in
       L.scompose (S.substitute e) s
  | DB.CVlet (ov, _, _, lctx)
    -> let s = lctx_to_subst lctx in
       (* Here we decide to keep those vars in the target domain.
        * Another option would be to map them to `L.impossible`,
        * hence making the target domain be empty (i.e. making the substitution
        * generate closed results).  *)
       L.ssink (maybev ov) s
  | DB.CVfix (defs, lctx)
    -> let s1 = lctx_to_subst lctx in
       let s2 = lexp_defs_subst DB.dloc S.identity
                                (List.map (fun (oname, odef, t)
                                           -> (maybev oname,
                                               (match odef with LetDef e -> e
                                                              | _ -> L.impossible),
                                               t))
                                          (List.rev defs)) in
       L.scompose s2 s1

(* Take an expression `e` that is "closed" relatively to context lctx
 * and return an equivalent expression valid in the empty context.
 * By "closed" I mean that it only refers to elements of the context which
 * are LetDef.  *)
let lexp_close meta_ctx lctx e =
  (* There are many different ways to skin this cat.
   * This is definitely not the best one:
   * - it inlines all the definitions everywhere they're used
   * - It turns the lctx (of O(log N) access time) into a subst
   *   (of O(N) access time)
   * Oh well!  *)
  L.clean meta_ctx (mkSusp e (lctx_to_subst lctx))
  

(** Reduce to weak head normal form.
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
let lexp_whnf e (ctx : DB.lexp_context) meta_ctx : lexp =
  let rec lexp_whnf e (ctx : DB.lexp_context) : lexp =
  match e with
  | Var v -> (match lookup_value ctx v with
             | None -> e
             (* We can do this blindly even for recursive definitions!
              * IOW the risk of inf-looping should only show up when doing
              * things like full normalization (e.g. lexp_conv_p).  *)
             | Some e' -> lexp_whnf e' ctx)
  | Susp (e, s) -> lexp_whnf (push_susp e s) ctx
  | Call (e, []) -> lexp_whnf e ctx
  | Call (f, (((_, arg)::args) as xs)) ->
     (match lexp_whnf f ctx with
      | Lambda (_, _, _, body) ->
         (* Here we apply whnf to the arg eagerly to kind of stay closer
          * to the idea of call-by-value, although in this context
          * we can't really make sure we always reduce the arg to a value.  *)
         lexp_whnf (mkCall (push_susp body (S.substitute (lexp_whnf arg ctx)),
                            args))
                   ctx
      | Call (f', xs1) -> mkCall (f', List.append xs1 xs)
      | _ -> e)                 (* Keep `e`, assuming it's more readable!  *)
  | Case (l, e, rt, branches, default) ->
     let e' = lexp_whnf e ctx in
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
              with | Some (v,default)
                     -> lexp_whnf (push_susp default (S.substitute e')) ctx
                   | _ -> U.msg_error "WHNF" l
                                     ("Unhandled constructor " ^
                                        name ^ "in case expression");
                         mkCase (l, e, rt, branches, default) in
     (match e' with
      | Cons (_, (_, name)) -> reduce name []
      | Call (Cons (_, (_, name)), aargs) -> reduce name aargs
      | _ -> mkCase (l, e, rt, branches, default))
  | Metavar (idx, s, _, _)
    -> (try lexp_whnf (mkSusp (L.VMap.find idx meta_ctx) s) ctx
       with Not_found -> e)

  (* FIXME: I'd really prefer to use "native" recursive substitutions, using
   *   ideally a trick similar to the db_offsets in lexp_context!  *)
  | Let (l, defs, body)
    -> lexp_whnf (push_susp body (lexp_defs_subst l S.identity defs)) ctx

  | e -> e

  in lexp_whnf e ctx


(** A very naive implementation of sets of pairs of lexps.  *)
type set_plexp = (lexp * lexp) list
let set_empty : set_plexp = []
let set_member_p meta_ctx (s : set_plexp) (e1 : lexp) (e2 : lexp) : bool
  = assert (e1 == Lexp.hc e1);
    assert (e2 == Lexp.hc e2);
    try let _ = List.find (fun (e1', e2')
                           -> L.eq meta_ctx e1 e1' && L.eq meta_ctx e2 e2')
                          s
        in true
     with Not_found -> false
let set_add (s : set_plexp) (e1 : lexp) (e2 : lexp) : set_plexp
  = (* assert (not (set_member_p meta_ctx s e1 e2)); *)
    ((e1, e2) :: s)
let set_shift_n (s : set_plexp) (n : U.db_offset)
  = List.map (let s = S.shift n in
              fun (e1, e2) -> (Lexp.push_susp e1 s, Lexp.push_susp e2 s))
             s
let set_shift s : set_plexp = set_shift_n s 1

(********* Testing if two types are "convertible" aka "equivalent"  *********)

(* Returns true if e₁ and e₂ are equal (upto alpha/beta/...).  *)
let rec conv_p' meta_ctx (ctx : DB.lexp_context) (vs : set_plexp) e1 e2 : bool =
  let conv_p' = conv_p' meta_ctx in
  let e1' = lexp_whnf e1 ctx meta_ctx in
  let e2' = lexp_whnf e2 ctx meta_ctx in
  e1' == e2' ||
    let changed = not (e1 == e1' && e2 == e2') in
    if changed && set_member_p meta_ctx vs e1' e2' then true else
    let vs' = if changed then set_add vs e1' e2' else vs in
    let conv_p = conv_p' ctx vs' in
    match (e1', e2') with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
    | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
    | (SortLevel sl1, SortLevel sl2)
      -> (match (sl1, sl2) with
         | (SLz, SLz) -> true
         | (SLsucc sl1, SLsucc sl2) -> conv_p sl1 sl2
         | (SLlub (sl11, sl12), sl2)
           (* FIXME: This should be "<=" rather than equality!  *)
           -> conv_p sl11 e2' && conv_p sl12 e2'
         | (sl1, SLlub (sl21, sl22))
           (* FIXME: This should be "<=" rather than equality!  *)
           -> conv_p e1' sl21 && conv_p e1' sl22
         | _ -> false)
    | (Sort (_, s1), Sort (_, s2))
      -> s1 == s2
        || (match (s1, s2) with
           | (Stype e1, Stype e2) -> conv_p e1 e2
           | _ -> false)
    | (Builtin ((_, s1), _, _), Builtin ((_, s2), _, _)) -> s1 = s2
    | (Var (_, v1), Var (_, v2)) -> v1 = v2
    | (Arrow (ak1, vd1, t11, _, t12), Arrow (ak2, vd2, t21, _, t22))
      -> ak1 == ak2
        && conv_p t11 t21
        && conv_p' (DB.lexp_ctx_cons ctx 0 vd1 Variable t11) (set_shift vs')
                  t12 t22
    | (Lambda (ak1, l1, t1, e1), Lambda (ak2, l2, t2, e2))
      -> ak1 == ak2 && (conv_erase || conv_p t1 t2)
        && conv_p' (DB.lexp_ctx_cons ctx 0 (Some l1) Variable t1)
                  (set_shift vs')
                  e1 e2
    | (Call (f1, args1), Call (f2, args2))
      -> let rec conv_arglist_p args1 args2 : bool =
          List.fold_left2
            (fun eqp (ak1,t1) (ak2,t2)
             -> eqp && ak1 = ak2
               && (conv_erase && ak1 = P.Aerasable || conv_p t1 t2))
            true args1 args2 in
        conv_p f1 f2 && conv_arglist_p args1 args2
    | (Inductive (_, l1, args1, cases1), Inductive (_, l2, args2, cases2))
      -> let rec conv_fields ctx vs fields1 fields2 =
          match fields1, fields2 with
          | ([], []) -> true
          | ((ak1,vd1,t1)::fields1, (ak2,vd2,t2)::fields2)
            -> ak1 == ak2 && conv_p' ctx vs t1 t2
              && conv_fields (DB.lexp_ctx_cons ctx 0 vd1 Variable t1)
                            (set_shift vs)
                            fields1 fields2
          | _,_ -> false in
        let rec conv_args ctx vs args1 args2 =
          match args1, args2 with
          | ([], []) ->
             (* Args checked alright, now go on with the fields,
              * using the new context.  *)
             SMap.equal (conv_fields ctx vs) cases1 cases2
          | ((ak1,l1,t1)::args1, (ak2,l2,t2)::args2)
            -> ak1 == ak2 && conv_p' ctx vs t1 t2
              && conv_args (DB.lexp_ctx_cons ctx 0 (Some l1) Variable t1)
                          (set_shift vs)
                          args1 args2
          | _,_ -> false in
        l1 == l2 && conv_args ctx vs' args1 args2
    | (Cons (t1, (_, l1)), Cons (t2, (_, l2))) -> l1 = l2 && conv_p t1 t2
    (* FIXME: Various missing cases, such as Case.  *)
    | (_, _) -> false

let conv_p meta_ctx (ctx : DB.lexp_context) e1 e2
  = if e1 == e2 then true
    else conv_p' meta_ctx ctx set_empty e1 e2

(********* Testing if a lexp is properly typed  *********)

(* Turn e into its canonical representation, which is basically the set
 * of vars it references along with the number of `succ` applied to them.
 * `c` is the maximum "constant" level that occurs in `e`
 * and `m` maps variable indices to the maxmimum depth at which they were
 * found.  *)
let level_canon e =
  let rec canon e d ((c,m) as acc) = match e with
    | SortLevel SLz -> if c < d then (d, m) else acc
    | SortLevel (SLsucc e) -> canon e (d + 1) acc
    | SortLevel (SLlub (e1, e2)) -> canon e1 d (canon e2 d acc)
    | Var (_, i) -> let o = try VMap.find i m with Not_found -> -1 in
                   if o < d then (c, VMap.add i d m) else acc
    | Metavar (i, _, _, _)
      -> let o = try VMap.find (- i) m with Not_found -> -1 in
        if o < d then (c, VMap.add (- i) d m) else acc
    | _ -> (max_int, m)
  in canon e 0 (0,VMap.empty)

let level_leq (c1, m1) (c2, m2) =
  c1 <= c2
  && c1 != max_int
  && VMap.for_all (fun i d -> try d <= VMap.find i m2 with Not_found -> false)
                 m1

let rec mkSLlub meta_ctx ctx e1 e2 =
  match (lexp_whnf e1 ctx meta_ctx, lexp_whnf e2 ctx meta_ctx) with
  | (SortLevel SLz, e2) -> e2
  | (e1, SortLevel SLz) -> e1
  | (SortLevel (SLsucc e1), SortLevel (SLsucc e2))
    -> mkSortLevel (SLsucc (mkSLlub meta_ctx ctx e1 e2))
  | (e1', e2')
    -> let ce1 = level_canon (L.clean meta_ctx e1') in
      let ce2 = level_canon (L.clean meta_ctx e2') in
      if level_leq ce1 ce2 then e1
      else if level_leq ce2 ce1 then e2
      else mkSortLevel (SLlub (e1, e2))

let sort_compose meta_ctx ctx l s1 s2 =
  match s1, s2 with
  | (Stype l1, Stype l2) -> Stype (mkSLlub meta_ctx ctx l1 l2)
  | ( (StypeLevel, Stype _)
    | (StypeLevel, StypeOmega)
    | (Stype _, StypeOmega))
    -> StypeOmega
  | _,_ -> (U.msg_error "TC" l
                       "Mismatch sorts for arg and result";
           StypeOmega)

let dbset_push ak erased =
  let nerased = DB.set_sink 1 erased in
  if ak = P.Aerasable then DB.set_set 0 nerased else nerased

(* "check ctx e" should return τ when "Δ ⊢ e : τ"  *)
let rec check' meta_ctx erased ctx e =
  let check = check' meta_ctx in
  let assert_type ctx e t t' =
    if conv_p meta_ctx ctx t t' then ()
    else (U.msg_error "TC" (lexp_location e)
                     ("Type mismatch for "
                      ^ lexp_string (L.clean meta_ctx e) ^ " : "
                      ^ lexp_string (L.clean meta_ctx t) ^ " != "
                      ^ lexp_string (L.clean meta_ctx t'));
          (* U.internal_error "Type mismatch" *)) in
  let check_type erased ctx t =
    let s = check erased ctx t in
    (match lexp_whnf s ctx meta_ctx with
    | Sort _ -> ()
    | _ -> U.msg_error "TC" (lexp_location t)
                      ("Not a proper type: " ^ lexp_string t));
    (* FIXME: return the `sort` rather than the surrounding `lexp`!  *)
    s in

  match e with
  | Imm (Float (_, _)) -> DB.type_float
  | Imm (Integer (_, _)) -> DB.type_int
  | Imm (String (_, _)) -> DB.type_string
  | Imm (Epsilon | Block (_, _, _) | Symbol _ | Node (_, _))
    -> (U.msg_error "TC" (lexp_location e) "Unsupported immediate value!";
       DB.type_int)
  | SortLevel SLz -> DB.type_level
  | SortLevel (SLsucc e)
    -> let t = check erased ctx e in
      (* FIXME: Actually, we should probably have a special function to check
       * that `e` is a level, so as to avoid `case` and other funny things.  *)
      assert_type ctx e t DB.type_level;
      DB.type_level
  | SortLevel (SLlub (e1, e2))
    -> let t1 = check erased ctx e1 in
      assert_type ctx e1 t1 DB.type_level;
      let t2 = check erased ctx e2 in
      assert_type ctx e2 t2 DB.type_level;
      DB.type_level
  | Sort (l, Stype e)
    -> let t = check erased ctx e in
      assert_type ctx e t DB.type_level;
      mkSort (l, Stype (mkSortLevel (SLsucc e)))
  | Sort (_, StypeLevel) -> DB.sort_omega
  | Sort (_, StypeOmega)
    -> ((* U.msg_error "TC" (lexp_location e) "Reached unreachable sort!";
        * U.internal_error "Reached unreachable sort!"; *)
       DB.sort_omega)
  | Builtin (_, t, _)
    -> let _ = check_type DB.set_empty Myers.nil t in
      (* FIXME: Check the attributemap as well!  *)
      t
  (* FIXME: Check recursive references.  *)
  | Var (((_, name), idx) as v)
    -> if DB.set_mem idx erased then
        U.msg_error "TC" (lexp_location e)
                    ("Var `" ^ name ^ "`"
                     ^ " can't be used here, because it's `erasable`");
      lookup_type ctx v
  | Susp (e, s) -> check erased ctx (push_susp e s)
  | Let (l, defs, e)
    -> let _ =
        List.fold_left (fun ctx (v, e, t)
                        -> (let _ = check_type DB.set_empty ctx t in
                           DB.lctx_extend ctx (Some v) ForwardRef t))
                       ctx defs in
      let nerased = DB.set_sink (List.length defs) erased in
      let nctx = DB.lctx_extend_rec ctx defs in
      (* FIXME: Termination checking!  Positivity-checker!  *)
      let _ = List.fold_left (fun n (v, e, t)
                              -> assert_type nctx e
                                            (push_susp t (S.shift n))
                                            (check nerased nctx e);
                                n - 1)
                             (List.length defs) defs in
      mkSusp (check nerased nctx e)
             (lexp_defs_subst l S.identity defs)
  | Arrow (ak, v, t1, l, t2)
    -> (let k1 = check_type erased ctx t1 in
       let nctx = DB.lexp_ctx_cons ctx 0 v Variable t1 in
       (* BEWARE!  `k2` can refer to `v`, but this should only happen
        * if `v` is a TypeLevel, and in that case sort_compose
        * should ignore `k2` and return TypeOmega anyway.  *)
       let k2 = check_type (DB.set_sink 1 erased) nctx t2 in
       let k2 = mkSusp k2 (S.substitute impossible) in
       match lexp_whnf k1 ctx meta_ctx, lexp_whnf k2 ctx meta_ctx with
       | (Sort (_, s1), Sort (_, s2))
         (* FIXME: fix scoping of `k2` and `s2`.  *)
         -> if ak == P.Aerasable && impredicative_erase && s1 != StypeLevel
           then k2
           else mkSort (l, sort_compose meta_ctx ctx l s1 s2)
       | (Sort (_, _), _) -> (U.msg_error "TC" (lexp_location t2)
                            "Not a proper type";
                             mkSort (l, StypeOmega))
       | (_, _) -> (U.msg_error "TC" (lexp_location t1)
                               "Not a proper type";
                   mkSort (l, StypeOmega)))
  | Lambda (ak, ((l,_) as v), t, e)
    -> ((match lexp_whnf (check_type DB.set_empty ctx t) ctx meta_ctx with
        | Sort _ -> ()
        | _ -> (U.msg_error "TC" (lexp_location t)
                           "Formal arg type is not a type!"; ()));
       mkArrow (ak, Some v, t, l,
                check (dbset_push ak erased)
                      (DB.lctx_extend ctx (Some v) Variable t)
                      e))
  | Call (f, args)
    -> let ft = check erased ctx f in
      List.fold_left
        (fun ft (ak,arg)
         -> let at = check (if ak = P.Aerasable then DB.set_empty else erased)
                          ctx arg in
           match lexp_whnf ft ctx meta_ctx with
           | Arrow (ak', v, t1, l, t2)
             -> if not (ak == ak') then
                 (U.msg_error "TC" (lexp_location arg)
                              "arg kind mismatch"; ())
               else ();
               assert_type ctx arg t1 at;
               mkSusp t2 (S.substitute arg)
           | _ -> (U.msg_error "TC" (lexp_location arg)
                              ("Calling a non function (type = "
                               ^ lexp_string ft ^ ")!");
                  ft))
        ft args
  | Inductive (l, label, args, cases)
    -> let rec arg_loop args ctx =
        match args with
        | []
          -> let level
              = SMap.fold
                  (fun _ case level ->
                    let level, _ =
                      List.fold_left
                        (fun (level, ctx) (ak, v, t) ->
                          (* FIXME: DB.set_empty seems wrong!  *)
                          (match lexp_whnf (check_type DB.set_empty ctx t)
                                           ctx meta_ctx with
                           | Sort (_, Stype _)
                                when ak == P.Aerasable && impredicative_erase
                             -> level
                           | Sort (_, Stype level')
                             (* FIXME: scoping of level vars!  *)
                             -> mkSLlub meta_ctx ctx level level'
                           | tt -> U.msg_error "TC" (lexp_location t)
                                              ("Field type "
                                               ^ lexp_string t
                                               ^ " is not a Type! ("
                                               ^ lexp_string tt ^")");
                                  DB.print_lexp_ctx ctx;
                                  (* U.internal_error "Oops"; *)
                                  level),
                          DB.lctx_extend ctx v Variable t)
                        (level, ctx)
                        case in
                    level)
                  cases (mkSortLevel SLz) in
            mkSort (l, Stype level)
        | (ak, v, t)::args
          -> mkArrow (ak, Some v, t, lexp_location t,
                     arg_loop args (DB.lctx_extend ctx (Some v) Variable t)) in
      let tct = arg_loop args ctx in
      tct
  | Case (l, e, ret, branches, default)
    -> let call_split e = match e with
        | Call (f, args) -> (f, args)
        | _ -> (e,[]) in
      let etype = lexp_whnf (check erased ctx e) ctx meta_ctx in
      let it, aargs = call_split etype in
      (match lexp_whnf it ctx meta_ctx, aargs with
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
               let rec mkctx erased ctx s vdefs fieldtypes =
                 match vdefs, fieldtypes with
                 | [], [] -> (erased, ctx)
                 (* FIXME: If ak is Aerasable, make sure the var only
                  * appears in type annotations.  *)
                 | (ak, vdef)::vdefs, (ak', vdef', ftype)::fieldtypes
                   -> mkctx (dbset_push ak erased)
                           (DB.lexp_ctx_cons ctx 0
                                             vdef Variable (mkSusp ftype s))
                           (S.cons (Var ((match vdef with Some vd -> vd
                                                        | None -> (l, "_")),
                                         0))
                                   (S.mkShift s 1))
                           vdefs fieldtypes
                 | _,_ -> (U.msg_error "TC" l
                                      "Wrong number of args to constructor!";
                          (erased, ctx)) in
               let (nerased, nctx) = mkctx erased ctx s vdefs fieldtypes in
               assert_type nctx branch
                           (mkSusp ret (S.shift (List.length fieldtypes)))
                           (check nerased nctx branch))
            branches;
          let diff = SMap.cardinal constructors - SMap.cardinal branches in
          (match default with
           | Some (v, d)
             -> if diff <= 0 then
                 U.msg_warning "TC" l "Redundant default clause";
               let nctx = (DB.lctx_extend ctx v (LetDef e) etype) in
               assert_type nctx d (mkSusp ret (S.shift 1))
                           (check (DB.set_sink 1 erased) nctx d)
           | None
             -> if diff > 0 then
                 U.msg_error "TC" l ("Non-exhaustive match: "
                                     ^ string_of_int diff ^ " cases missing"))
       | _,_ -> U.msg_error "TC" l "Case on a non-inductive type!");
      ret
  | Cons (t, (l, name))
    -> (match lexp_whnf t ctx meta_ctx with
       | Inductive (l, _, fargs, constructors)
         -> (try
              let fieldtypes = SMap.find name constructors in
              let rec indtype fargs start_index =
                match fargs with
                | [] -> []
                | (ak, vd, _)::fargs -> (ak, Var (vd, start_index))
                                       :: indtype fargs (start_index - 1) in
              let rec fieldargs ftypes =
                match ftypes with
                | [] -> let nargs = List.length fieldtypes + List.length fargs in
                       mkCall (mkSusp t (S.shift nargs),
                               indtype fargs (nargs - 1))
                | (ak, vd, ftype) :: ftypes
                  -> mkArrow (ak, vd, ftype, lexp_location ftype,
                             fieldargs ftypes) in
              let rec buildtype fargs =
                match fargs with
                | [] -> fieldargs fieldtypes
                | (ak, ((l,_) as vd), atype) :: fargs
                  -> mkArrow (P.Aerasable, Some vd, atype, l,
                             buildtype fargs) in
              buildtype fargs
            with Not_found
                 -> (U.msg_error "TC" l
                                ("Constructor \"" ^ name ^ "\" does not exist");
                    DB.type_int))
       | _ -> (U.msg_error "TC" (lexp_location e)
                          ("Cons of a non-inductive type: "
                           ^ lexp_string t);
              DB.type_int))
  | Metavar (idx, s, _, t)
    -> (try let e = push_susp (L.VMap.find idx meta_ctx) s in
           let t' = check erased ctx e in
           assert_type ctx e t' t
       with Not_found -> ());
      t

let check meta_ctx = check' meta_ctx DB.set_empty

(** Compute the set of free (meta)variables.  **)

let rec list_union l1 l2 = match l1 with
  | [] -> l2
  | (x::l1) -> list_union l1 (if List.mem x l2 then l2 else (x::l2))

type mv_set = subst list VMap.t
let mv_set_empty = VMap.empty
let mv_set_add ms m s
  = let ss = try VMap.find m ms with Not_found -> [] in
    if List.mem s ss then ms
    else VMap.add m (s::ss) ms
let mv_set_union : mv_set -> mv_set -> mv_set
  = VMap.merge (fun m oss1 oss2
                -> match (oss1, oss2) with
                  | (None, _) -> oss2
                  | (_, None) -> oss1
                  | (Some ss1, Some ss2)
                    ->  Some (list_union ss1 ss2))

module LMap
  (* Memoization table.  FIXME: Ideally the keys should be "weak", but
   * I haven't found any such functionality in OCaml's libs.  *)
  = Hashtbl.Make
      (struct type t = lexp let hash = Hashtbl.hash let equal = (==) end)
let fv_memo = LMap.create 1000

let fv_empty = (DB.set_empty, mv_set_empty)
let fv_union (fv1, mv1) (fv2, mv2)
  = (DB.set_union fv1 fv2, mv_set_union mv1 mv2)
let fv_sink n (fvs, mvs) = (DB.set_sink n fvs, mvs)
let fv_hoist n (fvs, mvs) = (DB.set_hoist n fvs, mvs)

let rec fv (e : lexp) : (DB.set * mv_set) =
  let fv' e = match e with
    | Imm _ -> fv_empty
    | SortLevel SLz -> fv_empty
    | SortLevel (SLsucc e) -> fv e
    | SortLevel (SLlub (e1, e2)) -> fv_union (fv e1) (fv e2)
    | Sort (_, Stype e) -> fv e
    | Sort (_, (StypeOmega | StypeLevel)) -> fv_empty
    | Builtin _ -> fv_empty
    | Var (_, i) -> (DB.set_singleton i, mv_set_empty)
    | Susp (e, s) -> fv (push_susp e s)
    | Let (_, defs, e)
      -> let len = List.length defs in
        let (s, _)
          = List.fold_left (fun (s, o) (_, e, t)
                            -> (fv_union s (fv_union (fv_sink o (fv t))
                                                    (fv e)),
                               o - 1))
                           (fv e, len) defs in
        fv_hoist len s
    | Arrow (_, _, t1, _, t2) -> fv_union (fv t1) (fv_hoist 1 (fv t2))
    | Lambda (_, _, t, e) -> fv_union (fv t) (fv_hoist 1 (fv e))
    | Call (f, args)
      -> List.fold_left (fun s (_, arg)
                        -> fv_union s (fv arg))
                       (fv f) args
    | Inductive (_, _, args, cases)
      -> let alen = List.length args in
        let s
          = List.fold_left (fun s (_, _, t)
                            -> fv_sink 1 (fv_union s (fv t)))
                           fv_empty args in
        let s
          = SMap.fold
              (fun _ fields s
               -> fv_union
                   s
                   (fv_hoist (List.length fields)
                             (List.fold_left (fun s (_, _, t)
                                              -> fv_sink 1 (fv_union s (fv t)))
                                             fv_empty fields)))
              cases s in
        fv_hoist alen s
    | Cons (t, _) -> fv t
    | Case (_, e, t, cases, def)
      -> let s = fv_union (fv e) (fv t) in
        let s = match def with
          | None -> s
          | Some (_, e) -> fv_union s (fv_hoist 1 (fv e)) in
        SMap.fold (fun _ (_, fields, e) s
                   -> fv_union s (fv_hoist (List.length fields) (fv e)))
                  cases s
    | Metavar (m, s, _, t)
      -> let (fvs, mvs) = fv t in
        (fvs, mv_set_add mvs m s)
  in
  try LMap.find fv_memo e
  with Not_found
       -> let r = fv' e in
         LMap.add fv_memo e r;
         r

(** Finding the type of a expression.  **)
(* This should never signal any warning/error.  *)

let rec get_type meta_ctx ctx e =
  let get_type = get_type meta_ctx in
  match e with
  | Imm (Float (_, _)) -> DB.type_float
  | Imm (Integer (_, _)) -> DB.type_int
  | Imm (String (_, _)) -> DB.type_string
  | Imm (Epsilon | Block (_, _, _) | Symbol _ | Node (_, _)) -> DB.type_int
  | Builtin (_, t, _) -> t
  | SortLevel _ -> DB.type_level
  | Sort (l, Stype e) -> mkSort (l, Stype (mkSortLevel (SLsucc e)))
  | Sort (_, StypeLevel) -> DB.sort_omega
  | Sort (_, StypeOmega) -> DB.sort_omega
  | Var (((_, name), idx) as v) -> lookup_type ctx v
  | Susp (e, s) -> get_type ctx (push_susp e s)
  | Let (l, defs, e)
    -> let nctx = DB.lctx_extend_rec ctx defs in
      mkSusp (get_type nctx e) (lexp_defs_subst l S.identity defs)
  | Arrow (ak, v, t1, l, t2)
    (* FIXME: Use `check` here but silencing errors?  *)
    -> (let k1 = get_type ctx t1 in
       let nctx = DB.lexp_ctx_cons ctx 0 v Variable t1 in
       (* BEWARE!  `k2` can refer to `v`, but this should only happen
        * if `v` is a TypeLevel, and in that case sort_compose
        * should ignore `k2` and return TypeOmega anyway.  *)
       let k2 = get_type nctx t2 in
       let k2 = mkSusp k2 (S.substitute impossible) in
       match lexp_whnf k1 ctx meta_ctx, lexp_whnf k2 ctx meta_ctx with
       | (Sort (_, s1), Sort (_, s2))
         -> if ak == P.Aerasable && impredicative_erase && s1 != StypeLevel
           then k2
           else mkSort (l, sort_compose meta_ctx ctx l s1 s2)
       | _ -> DB.type0)
  | Lambda (ak, ((l,_) as v), t, e)
    -> (mkArrow (ak, Some v, t, l,
                get_type (DB.lctx_extend ctx (Some v) Variable t)
                         e))
  | Call (f, args)
    -> let ft = get_type ctx f in
      List.fold_left
        (fun ft (ak,arg)
         -> match lexp_whnf ft ctx meta_ctx with
           | Arrow (ak', v, t1, l, t2)
             -> mkSusp t2 (S.substitute arg)
           | _ -> ft)
        ft args
  | Inductive (l, label, args, cases)
    (* FIXME: Use `check` here but silencing errors?  *)
    -> let rec arg_loop args ctx =
        match args with
        | []
          -> let level
              = SMap.fold
                  (fun _ case level ->
                    let level, _ =
                      List.fold_left
                        (fun (level, ctx) (ak, v, t) ->
                          (match lexp_whnf (get_type ctx t)
                                           ctx meta_ctx with
                           | Sort (_, Stype _)
                                when ak == P.Aerasable && impredicative_erase
                             -> level
                           | Sort (_, Stype level')
                             (* FIXME: scoping of level vars!  *)
                             -> mkSLlub meta_ctx ctx level level'
                           | tt -> level),
                          DB.lctx_extend ctx v Variable t)
                        (level, ctx)
                        case in
                    level)
                  cases (mkSortLevel SLz) in
            mkSort (l, Stype level)
        | (ak, v, t)::args
          -> mkArrow (ak, Some v, t, lexp_location t,
                     arg_loop args (DB.lctx_extend ctx (Some v) Variable t)) in
      let tct = arg_loop args ctx in
      tct
  | Case (l, e, ret, branches, default) -> ret
  | Cons (t, (l, name))
    -> (match lexp_whnf t ctx meta_ctx with
       | Inductive (l, _, fargs, constructors)
         -> (try
              let fieldtypes = SMap.find name constructors in
              let rec indtype fargs start_index =
                match fargs with
                | [] -> []
                | (ak, vd, _)::fargs -> (ak, Var (vd, start_index))
                                       :: indtype fargs (start_index - 1) in
              let rec fieldargs ftypes =
                match ftypes with
                | [] -> let nargs = List.length fieldtypes + List.length fargs in
                       mkCall (mkSusp t (S.shift nargs),
                               indtype fargs (nargs - 1))
                | (ak, vd, ftype) :: ftypes
                  -> mkArrow (ak, vd, ftype, lexp_location ftype,
                             fieldargs ftypes) in
              let rec buildtype fargs =
                match fargs with
                | [] -> fieldargs fieldtypes
                | (ak, ((l,_) as vd), atype) :: fargs
                  -> mkArrow (P.Aerasable, Some vd, atype, l,
                             buildtype fargs) in
              buildtype fargs
            with Not_found -> DB.type_int)
       | _ -> DB.type_int)
  | Metavar (idx, s, _, t) -> t

(*********** Type erasure, before evaluation.  *****************)

let rec erase_type (lxp: L.lexp): E.elexp =

    match lxp with
        | L.Imm(s)           -> E.Imm(s)
        | L.Builtin(v, _, _) -> E.Builtin(v)
        | L.Var(v)           -> E.Var(v)
        | L.Cons(_, s)       -> E.Cons(s)
        | L.Lambda (P.Aerasable, _, _, body) ->
          (* The var shouldn't appear in body, basically, but we need
           * to adjust the debruijn indices of other vars, hence the subst.  *)
          erase_type (L.push_susp body (S.substitute DB.type0))
        | L.Lambda (_, vdef, _, body) ->
          E.Lambda (vdef, erase_type body)

        | L.Let(l, decls, body)       ->
            E.Let(l, (clean_decls decls), (erase_type body))

        | L.Call(fct, args) ->
            E.Call((erase_type fct), (filter_arg_list args))

        | L.Case(l, target, _, cases, default) ->
            E.Case(l, (erase_type target), (clean_map cases),
                                         (clean_maybe default))

        | L.Susp(l, s)                -> erase_type (L.push_susp l s)

        (* To be thrown out *)
        | L.Arrow _                   -> E.Type
        | L.SortLevel _               -> E.Type
        | L.Sort _                    -> E.Type
        (* Still useful to some extent.  *)
        | L.Inductive(l, label, _, _) -> E.Inductive(l, label)
        | L.Metavar _                 -> U.internal_error "Metavar in erase_type"

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
        | Some (v, lxp) -> Some (v, erase_type lxp)
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
