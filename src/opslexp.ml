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
let rec lexp_defs_subst l s defs = match defs with
  | [] -> s
  | (_, lexp, _) :: defs'
    -> lexp_defs_subst l (S.cons (mkLet (l, defs, lexp)) s) defs'

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
    -> push_susp body (lexp_defs_subst l S.identity defs)

  | e -> e

  in lexp_whnf e ctx


(** A very naive implementation of sets of lexps.  *)
type set_lexp = lexp list
let set_empty : set_lexp = []
let set_member_p (s : set_lexp) (e : lexp) : bool
  = if not (e == Lexp.hc e) then
      (print_string "Not hashcons'd: ";
       lexp_print e;
       print_string "\n");
    assert (e == Lexp.hc e);
    List.mem e s
let set_add (s : set_lexp) (e : lexp) : set_lexp
  = assert (not (set_member_p s e));
    e :: s
let set_shift_n (s : set_lexp) (n : U.db_offset)
  = List.map (fun e -> Lexp.push_susp e (S.shift n)) s
let set_shift s : set_lexp = set_shift_n s 1

(********* Testing if two types are "convertible" aka "equivalent"  *********)

(* Returns true if e₁ and e₂ are equal (upto alpha/beta/...).  *)
let rec conv_p' meta_ctx (ctx : DB.lexp_context) (vs : set_lexp) e1 e2 : bool =
  let conv_p' = conv_p' meta_ctx in
  let e1' = lexp_whnf e1 ctx meta_ctx in
  let e2' = lexp_whnf e2 ctx meta_ctx in
  e1' == e2' ||
    let stop1 = not (e1 == e1') && set_member_p vs e1' in
    let stop2 = not (e2 == e2') && set_member_p vs e2' in
    let vs' = if not (e1 == e1') && not stop1 then set_add vs e1'
              else if not (e2 == e2') && not stop2 then set_add vs e2'
              else vs in
    let conv_p = conv_p' ctx vs' in
    match if stop1 || stop2 then (e1, e2) else (e1', e2') with
    | (Imm (Integer (_, i1)), Imm (Integer (_, i2))) -> i1 = i2
    | (Imm (Float (_, i1)), Imm (Float (_, i2))) -> i1 = i2
    | (Imm (String (_, i1)), Imm (String (_, i2))) -> i1 = i2
    | (SortLevel sl1, SortLevel sl2) -> sl1 = sl2
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
      -> let rec conv_args ctx vs args1 args2 =
          match args1, args2 with
          | ([], []) -> true
          | ((ak1,l1,t1)::args1, (ak2,l2,t2)::args2)
            -> ak1 == ak2 && conv_p' ctx vs t1 t2
              && conv_args (DB.lexp_ctx_cons ctx 0 (Some l1) Variable t1)
                          (set_shift vs)
                          args1 args2
          | _,_ -> false in
        let rec conv_fields ctx vs fields1 fields2 =
          match fields1, fields2 with
          | ([], []) -> true
          | ((ak1,vd1,t1)::fields1, (ak2,vd2,t2)::fields2)
            -> ak1 == ak2 && conv_p' ctx vs t1 t2
              && conv_fields (DB.lexp_ctx_cons ctx 0 vd1 Variable t1)
                            (set_shift vs)
                            fields1 fields2
          | _,_ -> false in
        l1 == l2 && conv_args ctx vs' args1 args2
        && SMap.equal (conv_fields ctx vs') cases1 cases2
    | (Cons (t1, (_, l1)), Cons (t2, (_, l2))) -> l1 = l2 && conv_p t1 t2
    (* FIXME: Various missing cases, such as Case.  *)
    | (_, _) -> false

let conv_p meta_ctx (ctx : DB.lexp_context) e1 e2
  = if e1 == e2 then true
    else conv_p' meta_ctx ctx set_empty e1 e2

(********* Testing if a lexp is properly typed  *********)


let rec sort_level_max l1 l2 = match nosusp l1, nosusp l2 with
  | SortLevel SLz, l2 -> l2
  | l1, SortLevel SLz -> l1
  | SortLevel (SLsucc l1), SortLevel (SLsucc l2)
    -> SortLevel (SLsucc (sort_level_max l1 l2))
  | _, _ (* FIXME: This requires s.th. like `SLmax of lexp * lexp`!  *)
    -> U.msg_error "TC" (lexp_location l1)
                  ("Can't compute the max of levels `"
                   ^ lexp_string l1 ^ "` and `"
                   ^ lexp_string l2 ^ "`");
      SortLevel SLz

let sort_compose l s1 s2 =
  match s1, s2 with
  | (Stype l1, Stype l2) -> Stype (sort_level_max l1 l2)
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
                      ^ lexp_string e ^ " : "
                      ^ lexp_string t ^ " != " ^ lexp_string t');
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
      assert_type ctx e t DB.type_level;
      (* FIXME: typelevel vs typelevelsort !? *)
      DB.type_level
  | Sort (l, Stype e)
    -> let t = check erased ctx e in
      assert_type ctx e t DB.type_level;
      Sort (l, Stype (SortLevel (SLsucc e)))
  | Sort (_, StypeLevel) -> DB.type_omega
  | Sort (_, StypeOmega)
    -> (U.msg_error "TC" (lexp_location e) "Reached Unreachable sort!";
       U.internal_error "Reached Unreachable sort!";
       DB.type_omega)
  | Builtin (_, t, _) -> t
  (* FIXME: Check recursive references.  *)
  | Var (((_, name), idx) as v)
    -> if DB.set_mem idx erased then
        U.msg_error "TC" (lexp_location e)
                    ("Var `" ^ name ^ "`"
                     ^ " can't be used here, because it's `erasable`")
      else if name = "erased" then U.internal_error "WOWO!";
      lookup_type ctx v
  | Susp (e, s) -> check erased ctx (push_susp e s)
  | Let (l, defs, e)
    -> let tmp_ctx =
        List.fold_left (fun ctx (v, e, t)
                        -> (let _ = check_type DB.set_empty ctx t in
                           DB.lctx_extend ctx (Some v) ForwardRef t))
                       ctx defs in
      let nerased = DB.set_sink (List.length defs) erased in
      let _ = List.fold_left (fun n (v, e, t)
                              -> assert_type tmp_ctx e
                                            (push_susp t (S.shift n))
                                            (check nerased tmp_ctx e);
                                n - 1)
                             (List.length defs) defs in
      let new_ctx = DB.lctx_extend_rec ctx defs in
      mkSusp (check nerased new_ctx e)
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
           else Sort (l, sort_compose l s1 s2)
       | (Sort (_, _), _) -> (U.msg_error "TC" (lexp_location t2)
                            "Not a proper type";
                             Sort (l, StypeOmega))
       | (_, _) -> (U.msg_error "TC" (lexp_location t1)
                               "Not a proper type";
                   Sort (l, StypeOmega)))
  | Lambda (ak, ((l,_) as v), t, e)
    -> ((match lexp_whnf (check_type DB.set_empty ctx t) ctx meta_ctx with
        | Sort _ -> ()
        | _ -> (U.msg_error "TC" (lexp_location t)
                           "Formal arg type is not a type!"; ()));
       Arrow (ak, Some v, t, l,
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
                             -> sort_level_max level level'
                           | tt -> U.msg_error "TC" (lexp_location t)
                                              ("Field type "
                                               ^ lexp_string t
                                               ^ " is not a Type! ("
                                               ^ lexp_string tt ^")");
                                  (* DB.print_lexp_ctx ctx;
                                   * U.internal_error "Oops"; *)
                                  level),
                          DB.lctx_extend ctx v Variable t)
                        (level, ctx)
                        case in
                    level)
                  cases (SortLevel SLz) in
            Sort (l, Stype level)
        | (ak, v, t)::args
          -> Arrow (ak, Some v, t, lexp_location t,
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
  | Cons (t, (_, name))
    -> (match lexp_whnf t ctx meta_ctx with
       | Inductive (l, _, fargs, constructors) as it
         -> let fieldtypes = SMap.find name constructors in
           let rec indtype fargs start_index =
             match fargs with
             | [] -> []
             | (ak, vd, _)::fargs -> (ak, Var (vd, start_index))
                                    :: indtype fargs (start_index - 1) in
           let rec fieldargs ftypes =
             match ftypes with
             | [] -> let nargs = List.length fieldtypes + List.length fargs in
                    Call (mkSusp t (S.shift nargs), indtype fargs (nargs - 1))
             | (ak, vd, ftype) :: ftypes
               -> Arrow (ak, vd, ftype, lexp_location ftype,
                                       fieldargs ftypes) in
           let rec buildtype fargs =
             match fargs with
             | [] -> fieldargs fieldtypes
             | (ak, ((l,_) as vd), atype) :: fargs
               -> Arrow (P.Aerasable, Some vd, atype, l,
                        buildtype fargs) in
           buildtype fargs
       | _ -> (U.msg_error "TC" (lexp_location e)
                          "Cons of a non-inductive type!";
              DB.type_int))
  | Metavar (idx, s, _, t)
    -> try check erased ctx (push_susp (L.VMap.find idx meta_ctx) s)
      with Not_found -> t

let check meta_ctx = check' meta_ctx DB.set_empty

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
