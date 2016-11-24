(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * ---------------------------------------------------------------------------
 *
 *      Description:
 *          parse pexp expression into lexp
 *
 * --------------------------------------------------------------------------- *)

open Util
open Fmt
open Myers

open Prelexer
open Lexer

open Sexp
open Pexp
open Lexp

open Env
open Debruijn
open Eval

open Grammar
open Builtin

module Unif = Unification

module OL = Opslexp
module EL = Elexp
module SU = Subst

(* Shortcut => Create a Var *)
let make_var name index loc =
    mkVar (((loc, name), index))

(* dummies *)
let dlxp = type0
let dltype = type0
let dloc = dummy_location

let _global_lexp_ctx = ref make_elab_context
let _parsing_internals = ref false
let btl_folder = ref "./btl/"

let warning = msg_warning "LPARSE"
let error = msg_error "LPARSE"
let fatal = msg_fatal "LPARSE"

(* Print Lexp name followed by the lexp in itself, finally throw an exception *)
let debug_message error_type type_name type_string loc expr message =
  debug_messages error_type loc
    message [
      (type_name expr) ^ ": " ^ (type_string expr);
    ]

let lexp_fatal   = debug_message fatal lexp_name lexp_string
let lexp_warning = debug_message warning lexp_name lexp_string
let lexp_error   = debug_message error lexp_name lexp_string
let pexp_fatal   = debug_message fatal pexp_name pexp_string
let pexp_error   = debug_message error pexp_name pexp_string
let value_fatal  = debug_message fatal value_name value_string

(* :-( *)
let global_substitution = ref (empty_meta_subst, [])

(* The prefix `elab_check_` is used for functions which do internal checking
 * (i.e. errors signalled here correspond to internal errors rather than
 * to errors in the user's code).  *)

let elab_check_sort (ctx : elab_context) lsort var ltp =
  let meta_ctx, _ = !global_substitution in
  match (try OL.lexp_whnf lsort (ectx_to_lctx ctx) meta_ctx
         with e ->
           print_string "Exception during whnf of ";
           lexp_print lsort;
           print_string "\n";
           raise e) with
  | Sort (_, _) -> () (* All clear!  *)
  | _ -> let lexp_string e = lexp_string (L.clean meta_ctx e) in
        let typestr = lexp_string ltp ^ " : " ^ lexp_string lsort in
        match var with
        | None -> lexp_error (lexp_location ltp) ltp
                            ("`" ^ typestr ^ "` is not a proper type")
        | Some (l, name)
          -> lexp_error l ltp
                       ("Type of `" ^ name ^ "` is not a proper type: "
                        ^ typestr)

(* Builtin Macro i.e, special forms *)
type macromap =
  (location -> lexp list -> elab_context -> lexp -> (lexp * lexp)) SMap.t

let elab_check_proper_type (ctx : elab_context) ltp var =
  let meta_ctx, _ = !global_substitution in
  try elab_check_sort ctx (OL.check meta_ctx (ectx_to_lctx ctx) ltp) var ltp
  with e -> print_string "Exception while checking type `";
           lexp_print ltp;
           (match var with
            | None -> ()
            | Some (_, name)
              -> print_string ("` of var `" ^ name ^"`\n"));
           print_lexp_ctx (ectx_to_lctx ctx);
           raise e

let elab_check_def (ctx : elab_context) var lxp ltype =
  let lctx = ectx_to_lctx ctx in
  let loc = lexp_location lxp in

  let meta_ctx, _ = !global_substitution in
  let lexp_string e = lexp_string (L.clean meta_ctx e) in
  let ltype' = try OL.check meta_ctx lctx lxp
    with e ->
      lexp_error loc lxp "Error while type-checking";
      print_lexp_ctx (ectx_to_lctx ctx);
      raise e in
  if (try OL.conv_p meta_ctx (ectx_to_lctx ctx) ltype ltype'
      with e
           -> print_string ("Exception while conversion-checking types:\n");
             lexp_print ltype;
             print_string (" and ");
             lexp_print ltype';
             print_string ("\n");
             lexp_error loc lxp
                        ("Exception while conversion-checking types "
                         ^ lexp_string ltype ^ " and " ^ lexp_string ltype');
             raise e)
  then
    elab_check_proper_type ctx ltype (Some var)
  else
    (debug_messages fatal loc "Type check error: ¡¡ctx_define error!!" [
      lexp_string lxp ^ " !: " ^ lexp_string ltype;
      "                    because";
      lexp_string ltype' ^ " != " ^ lexp_string ltype])

let ctx_extend (ctx: elab_context) (var : vdef option) def ltype =
  elab_check_proper_type ctx ltype var;
  ectx_extend ctx var def ltype

let ctx_define (ctx: elab_context) var lxp ltype =
  elab_check_def ctx var lxp ltype;
  env_extend ctx var (LetDef lxp) ltype

let ctx_define_rec (ctx: elab_context) decls =
  let nctx = ectx_extend_rec ctx decls in
  let _ = List.fold_left (fun n (var, lxp, ltp)
                          -> elab_check_proper_type
                              nctx (push_susp ltp (S.shift n)) (Some var);
                            n - 1)
                         (List.length decls)
                         decls in
  let _ = List.fold_left (fun n (var, lxp, ltp)
                          -> elab_check_def nctx var lxp
                                           (push_susp ltp (S.shift n));
                            n - 1)
                         (List.length decls)
                         decls in
  nctx

(*  The main job of lexp (currently) is to determine variable name (index)
 *  and to regroup type specification with their variable
 *
 *  elab_context is composed of two environment: senv and env.
 *  the senv environment is used to find the correct debruijn index
 *  while the env environment is used to save variable information.
 *  the env environment look a lot like the runtime environment that will be
 *  used in the eval section.
 *
 *  While most of the time senv and env will be synchronised it is
 *  possible for env to hold more variables than senv since senv is a map
 *  which does not allow multiple definition while env does.
 *
 *)

(*
 *      Type Inference
 * --------------------- *)
(* Parsing a Pexp into an Lexp is really "elaboration", i.e. it needs to
 * infer the types and perform macro-expansion.
 *
 * More specifically, we do it with 2 mutually recursive functions:
 * - `check` takes a Pexp along with its expected type and return an Lexp
 *   of that type (hopefully)
 * - `infer` takes a Pexp and infers its type (which it returns along with
 *   the Lexp).
 * This is the idea of "bidirectional type checking", which minimizes
 * the amount of "guessing" and/or annotations.  Since we infer types anyway
 * it doesn't really reduce the amount of type annotations for us, but it
 * reduces the amount of inference and checking, i.e. it reduces the number of
 * metavars we create/instantiate/dereference as well as the number of call to
 * the unification algorithm.
 * Basically guessing/annotations is only needed at those few places where the
 * code is not fully-normalized, which in normal programs is only in "let"
 * definitions.
 *)


let newMetavar l name t =
  let meta = Unif.create_metavar () in
  mkMetavar (meta, S.Identity, (l, name), t)

let newMetalevel () =
  newMetavar Util.dummy_location "l" (Sort (dummy_location, StypeLevel))

let newMetatype () = newMetavar Util.dummy_location "t" (newMetalevel ())

let rec infer (p : pexp) (ctx : elab_context): lexp * ltype =

    let tloc = pexp_location p in

    (* Save current trace in a global variable.  If an error occur,
       we will be able to retrieve the most recent trace and context.  *)
    _global_lexp_ctx := ctx;

    match p with
    (* Block/String/Integer/Float.  *)
    | Pimm v
      -> (mkImm (v),
         match v with
         | Integer _ -> type_int
         | Float _   -> type_float
         | String _  -> type_string;
         | _ -> pexp_error tloc p "Could not find type";
               dltype)

    (* Symbol i.e identifier.  *)
    | Pvar (loc, name)
      -> (try
           let idx = senv_lookup name ctx in
           let lxp = make_var name idx loc in

           (* Search type.  *)
           let ltp = env_lookup_type ctx ((loc, name), idx) in
           lxp, ltp

         with Not_found ->
           (pexp_error loc p ("The variable: `" ^ name ^ "` was not declared");
            (* Error recovery. The -1 index will raise an error later on *)
            (make_var name (-1) loc), dltype))

    (* Let, Variable declaration + local scope.  *)
    | Plet (loc, decls, body)
      -> let declss, nctx = lexp_p_decls decls ctx in
        let bdy, ltp = infer body nctx in
        let s = List.fold_left (OL.lexp_defs_subst loc) S.identity declss in
        (lexp_let_decls declss bdy nctx),
        mkSusp ltp s

    (* ------------------------------------------------------------------ *)
    | Parrow (kind, ovar, tp, loc, expr)
      -> let ltp = infer_type tp ctx ovar in
        let nctx = ectx_extend ctx ovar Variable ltp in

        let lxp = infer_type expr nctx None in

        let v = mkArrow(kind, ovar, ltp, tloc, lxp) in
        v, type0

    | Pinductive (label, formal_args, ctors)
      -> let nctx = ref ctx in
        (* (arg_kind * pvar * pexp option) list *)
        let formal = List.map (fun (kind, var, opxp)
                               -> let ltp, _ = match opxp with
                                   | Some pxp -> infer pxp !nctx
                                   | None -> dltype, dltype in

                                 nctx := env_extend !nctx var Variable ltp;
                                 (kind, var, ltp))
                              formal_args in

        let nctx = !nctx in
        let ltp = List.fold_left (fun tp (kind, v, ltp)
                                  -> (mkArrow (kind, Some v, ltp, tloc, tp)))
                                 (* FIXME: See OL.check for how to
                                  * compute the real target sort
                                  * (not always type0).  *)
                                 type0 (List.rev formal) in

        let map_ctor = lexp_parse_inductive ctors nctx in
        let v = mkInductive(tloc, label, formal, map_ctor) in
        v, ltp

    (* This case can be inferred.  *)
    | Plambda (kind, var, Some ptype, body)
      -> let ltp = infer_type ptype ctx (Some var) in

        let nctx = env_extend ctx var Variable ltp in
        let lbody, lbtp = infer body nctx in

        let lambda_type = mkArrow (kind, Some var, ltp, tloc, lbtp) in
        mkLambda(kind, var, ltp, lbody), lambda_type

    | Pcall (fname, args) -> infer_call fname args ctx

    | Pcons(t, sym)
      -> let idt, _ = infer t ctx in
        let (loc, cname) = sym in
        let meta_ctx, _ = !global_substitution in

        (* Get constructor args.  *)
        let formal, args = match OL.lexp_whnf idt
                                              (ectx_to_lctx ctx) meta_ctx with
          | Inductive(_, _, formal, ctor_def) as lxp
            -> (try formal, (SMap.find cname ctor_def)
               with Not_found ->
                 lexp_error loc lxp
                            ("Constructor \"" ^ cname ^ "\" does not exist");
                 [], [])

          | lxp -> lexp_error loc lxp ("`" ^ lexp_string idt
                                      ^ "` is not an inductive type");
                  [], [] in

        (* Build Arrow type.  *)
        let target = let targs, _
                       = List.fold_right
                           (fun (ak, v, _) (targs, i)
                            -> ((ak, Var (v, i)) :: targs,
                               i - 1))
                           formal
                           ([], List.length formal + List.length args - 1) in
                     mkCall (push_susp idt (S.shift (List.length formal
                                                     + List.length args)),
                             targs) in
        let cons_type
          = List.fold_left (fun ltp (kind, v, tp)
                            -> mkArrow (kind, v, tp, loc, ltp))
                           target
                           (List.rev args) in

        (* Add Aerasable arguments.  *)
        let cons_type = List.fold_left
                          (fun ltp (kind, v, tp)
                           -> mkArrow (Aerasable, Some v, tp, loc, ltp))
                          cons_type (List.rev formal) in

        mkCons(idt, sym), cons_type

    | Phastype (_, pxp, ptp)
      -> let ltp = infer_type ptp ctx None in
        (check pxp ltp ctx, ltp)

    | (Plambda _ | Pcase _ | Pmetavar _)
      -> let t = newMetatype () in
         let lxp = check p t ctx in
         (lxp, t)

(* Build the list of implicit arguments to instantiate.  *)
and instantiate_implicit e t ctx =
  let (meta_ctx, _) = !global_substitution in
  let rec instantiate t args =
    match OL.lexp_whnf t (ectx_to_lctx ctx) meta_ctx with
    | Arrow ((Aerasable | Aimplicit) as ak, v, t1, _, t2)
      -> let arg = newMetavar (lexp_location e)
                             (match v with Some (_, name) -> name | _ -> "v")
                             t1 in
        instantiate (mkSusp t2 (S.substitute arg)) ((ak, arg)::args)
    | _ -> (mkCall (e, List.rev args), t)
  in instantiate t []

and infer_type pexp ectx var =
  (* We could also use lexp_check with an argument of the form
   * Sort (?s), but in most cases the metavar would be allocated
   * unnecessarily.  *)
  let t, s = infer pexp ectx in
  (let meta_ctx, _ = !global_substitution in
   match OL.lexp_whnf s (ectx_to_lctx ectx) meta_ctx with
   | Sort (_, _) -> () (* All clear!  *)
   | _ ->
      (* FIXME: Here we rule out TypeLevel/TypeOmega.  *)
      match Unif.unify (mkSort (lexp_location s, Stype (newMetalevel ()))) s
                       (ectx_to_lctx ectx) meta_ctx with
      | (None | Some (_, _::_))
        -> (let lexp_string e = lexp_string (L.clean meta_ctx e) in
           let typestr = lexp_string t ^ " : " ^ lexp_string s in
           match var with
           | None -> lexp_error (lexp_location t) t
                               ("`" ^ typestr ^ "` is not a proper type")
           | Some (l, name)
             -> lexp_error l t
                          ("Type of `" ^ name ^ "` is not a proper type: "
                           ^ typestr))
      | Some subst -> global_substitution := subst);
  t

and lexp_let_decls declss (body: lexp) ctx =
  List.fold_right (fun decls lxp -> mkLet (dloc, decls, lxp))
                  declss body

and check (p : pexp) (t : ltype) (ctx : elab_context): lexp =

    let tloc = pexp_location p in

    (* Safe current trace in a global variable. If an error occur,
       we will be able to retrieve the most recent trace and context *)
    _global_lexp_ctx := ctx;

    let unify_with_arrow lxp kind var aty subst =
      let body = newMetatype () in
      let arg = match aty with
        | None -> newMetatype ()
        | Some laty -> laty in
      let l, _ = var in
      let arrow = mkArrow (kind, Some var, arg, l, body) in
      match Unif.unify arrow lxp (ectx_to_lctx ctx) subst with
      | None       -> lexp_error tloc lxp ("Type " ^ lexp_string lxp
                                          ^ " and "
                                          ^ lexp_string arrow
                                          ^ " does not match");
                     dltype, dltype
      | Some (_, (t1,t2)::_)
        -> lexp_error tloc lxp ("Types `" ^ lexp_string t1
                               ^ " and "
                               ^ lexp_string t2
                               ^ " do not match");
          dltype, dltype
      | Some subst -> global_substitution := subst; arg, body

    in
    let infer_lambda_body kind var def_arg_type body subst =
      (* Check argument type annotation, if any.  *)
      let def_arg_type = match def_arg_type with
        | Some def_arg_type
          -> Some (infer_type def_arg_type ctx (Some var))
        | _ -> None in

      (* Read var type from the provided type *)
      let meta_ctx, _ = !global_substitution in
      let given_arg_type, given_body_type =
        match OL.lexp_whnf t (ectx_to_lctx ctx) meta_ctx with
        | Arrow(kind, _, ltp, _, lbtp)
          -> (match def_arg_type with
             | None -> ()
             | Some def_arg_type
               -> if not (OL.conv_p meta_ctx (ectx_to_lctx ctx) def_arg_type ltp) then
                   lexp_error (lexp_location def_arg_type) def_arg_type
                              ("Type mismatch!  Context expected `"
                               ^ lexp_string ltp ^ "`"));
            ltp, lbtp
        | lxp -> unify_with_arrow lxp kind var def_arg_type subst in

      let nctx = env_extend ctx var Variable given_arg_type in
      let lbody = check body given_body_type nctx in
      mkLambda (kind, var, given_arg_type, lbody)

    in
    let subst, _ = !global_substitution in
    match p with
    | Plambda (kind, var, def_arg_type, body)
      -> infer_lambda_body kind var def_arg_type body subst

    | Pcase (loc, target, branches)
      -> check_case t (loc, target, branches) ctx

    (* FIXME: Handle *macro* pcalls here! *)
    (* | Pcall (fname, _args) -> *)

    | Pmetavar (l,"") -> newMetavar l "v" t
    | Pmetavar (l, name)
      -> pexp_error l p "Named metavars not supported (yet)";
        newMetavar l name t

    | _ -> infer_and_check p ctx t

and infer_and_check pexp ctx t =
  let (e, inferred_t) = infer pexp ctx in
  let subst, _ = !global_substitution in
  let (e, inferred_t) = match OL.lexp_whnf t (ectx_to_lctx ctx) subst with
    | Arrow ((Aerasable | Aimplicit), _, _, _, _)
      -> (e, inferred_t)
    | _ -> instantiate_implicit e inferred_t ctx in
  (match Unif.unify inferred_t t (ectx_to_lctx ctx) subst with
   | None
     -> lexp_error (pexp_location pexp) e
                  ("Type mismatch!  Context expected `"
                   ^ lexp_string t ^ "` but expression has type `"
                   ^ lexp_string inferred_t ^ "`")
   | Some (_, (t1,t2)::_)
     -> lexp_error (pexp_location pexp) e
                  ("Type mismatch!  Context expected `"
                   ^ lexp_string t2 ^ "` but expression has type `"
                   ^ lexp_string t1 ^ "`")
   | Some subst -> global_substitution := subst);
  e

(* Lexp.case can sometimes be inferred, but we prefer to always check.  *)
and check_case rtype (loc, target, ppatterns) ctx =
    (* FIXME: check if case is exhaustive  *)
    (* Helpers *)

  let pat_string p = sexp_string (pexp_u_pat p) in

    let uniqueness_warn pat =
      warning (pexp_pat_location pat)
              ("Pattern " ^ pat_string pat
               ^ " is a duplicate.  It will override previous pattern.") in

    let check_uniqueness pat name map =
      if SMap.mem name map then uniqueness_warn pat in

    (* get target and its type *)
    let tlxp, tltp = infer target ctx in
    let meta_ctx, _ = !global_substitution in
    (* FIXME: We need to be careful with whnf: while the output is "equivalent"
     * to the input, it's not necessarily as readable/efficient.
     * So try to reuse the "non-whnf" form whenever possible.  *)
    let call_split e = match (OL.lexp_whnf e (ectx_to_lctx ctx) meta_ctx) with
      | Call (f, args) -> (f, args)
      | _ -> (e,[]) in
    let it, targs = call_split tltp in
    let constructors = match OL.lexp_whnf it (ectx_to_lctx ctx) meta_ctx with
      | Inductive (_, _, fargs, constructors)
        -> assert (List.length fargs = List.length targs);
          constructors
      | _ -> lexp_error (pexp_location target) tlxp
                       ("Can't `case` on objects of this type: "
                        ^ lexp_string tltp);
            SMap.empty in

    (*  Read patterns one by one *)
    let fold_fun (lbranches, dflt) (pat, pexp) =

      let add_default v =
        (if dflt != None then uniqueness_warn pat);
        let nctx = ctx_extend ctx v Variable tltp in
        let rtype' = mkSusp rtype (S.shift (M.length (ectx_to_lctx nctx)
                                            - M.length (ectx_to_lctx ctx))) in
        let lexp = check pexp rtype' nctx in
        lbranches, Some (v, lexp) in

      let add_branch pctor pargs =
        let loc = pexp_location pctor in
        let lctor, _ = infer pctor ctx in
        let meta_ctx, _ = !global_substitution in
        match OL.lexp_whnf lctor (ectx_to_lctx ctx) meta_ctx with
        | Cons (it', (_, cons_name))
          -> let _ = if OL.conv_p meta_ctx (ectx_to_lctx ctx) it' it then ()
                    else lexp_error loc lctor
                                    ("Expected pattern of type `"
                                     ^ lexp_string it ^ "` but got `"
                                    ^ lexp_string it' ^ "`") in
            let _ = check_uniqueness pat cons_name lbranches in
            let cargs
              = try SMap.find cons_name constructors
                with Not_found
                     -> lexp_error loc lctor
                                  ("`" ^ (lexp_string it)
                                   ^ "` does not have a `"
                                   ^ cons_name ^ "` constructor");
                       [] in

            let subst = List.fold_right (fun (_, t) s -> S.cons t s)
                                        targs S.identity in
            let rec make_nctx ctx   (* elab context.  *)
                              s     (* Pending substitution.  *)
                              pargs (* Pattern arguments.  *)
                              cargs (* Constructor arguments.  *)
                              pe    (* Pending explicit pattern args.  *)
                              acc = (* Accumulated reult.  *)
              match (pargs, cargs) with
              | (_, []) when not (SMap.is_empty pe)
                -> let pending = SMap.bindings pe in
                  pexp_error loc pctor
                             ("Explicit pattern args `"
                              ^ String.concat ", " (List.map (fun (l, _) -> l)
                                                             pending)
                              ^ "` have no matching fields");
                  make_nctx ctx s pargs cargs SMap.empty acc
              | [], [] -> ctx, List.rev acc
              | (_, pat)::_, []
                -> lexp_error loc lctor
                             "Too many pattern args to the constructor";
                  make_nctx ctx s [] [] pe acc
              | (_, Ppatcons (p, _))::pargs, cargs
                -> lexp_error (pexp_location p) lctor
                             "Nested patterns not supported!";
                  make_nctx ctx s pargs cargs pe acc
              | (_, (ak, Some (_, fname), fty)::cargs)
                   when SMap.mem fname pe
                -> let var = SMap.find fname pe in
                  let nctx = ctx_extend ctx var Variable (mkSusp fty s) in
                  make_nctx nctx (ssink (maybev var) s) pargs cargs
                            (SMap.remove fname pe)
                            ((ak, var)::acc)
              | ((ef, fpat)::pargs, (ak, _, fty)::cargs)
                   when (match (ef, ak) with
                         | (Some (_, "_"), _) | (None, Aexplicit) -> true
                         | _ -> false)
                -> let var = match fpat with Ppatsym v -> Some v | _ -> None in
                  let nctx = ctx_extend ctx var Variable (mkSusp fty s) in
                  make_nctx nctx (ssink (maybev var) s) pargs cargs pe
                            ((ak, var)::acc)
              | ((Some (l, fname), fpat)::pargs, cargs)
                -> let var = match fpat with Ppatsym v -> Some v | _ -> None in
                  if SMap.mem fname pe then
                    pexp_error l pctor
                               ("Duplicate explicit field `" ^ fname ^ "`");
                  make_nctx ctx s pargs cargs (SMap.add fname var pe) acc
              | pargs, (ak, fname, fty)::cargs
                -> let nctx = ctx_extend ctx None Variable (mkSusp fty s) in
                  if ak = Aexplicit then
                    pexp_error loc pctor
                               ("Missing pattern for normal field"
                                ^ (match fname with Some (_,n) -> " `" ^ n ^ "`"
                                                  | _ -> ""));
                  make_nctx nctx (ssink vdummy s) pargs cargs pe
                            ((ak, None)::acc) in
            let nctx, fargs = make_nctx ctx subst pargs cargs SMap.empty [] in
            let rtype' = mkSusp rtype
                                (S.shift (M.length (ectx_to_lctx nctx)
                                          - M.length (ectx_to_lctx ctx))) in
            let lexp = check pexp rtype' nctx in
            SMap.add cons_name (loc, fargs, lexp) lbranches,
            dflt
        | _ -> lexp_error loc lctor "Not a constructor"; lbranches, dflt
      in

      match pat with
      | Ppatany _ -> add_default None
      | Ppatsym ((_, name) as var)
        -> (try let idx = senv_lookup name ctx in
               let meta_ctx, _ = !global_substitution in
               match OL.lexp_whnf (mkVar (var, idx))
                                  (ectx_to_lctx ctx) meta_ctx with
               | Cons _         (* It's indeed a constructor!  *)
                 -> add_branch (Pvar var) []
               | _ -> add_default (Some var) (* A named default branch.  *)
           with Not_found -> add_default (Some var))

      | Ppatcons (pctor, pargs) -> add_branch pctor pargs in

    let (lpattern, dflt) =
        List.fold_left fold_fun (SMap.empty, None) ppatterns in

    mkCase (loc, tlxp, rtype, lpattern, dflt)

(*  Identify Call Type and return processed call.  *)
and infer_call (func: pexp) (sargs: sexp list) ctx =
    let loc = pexp_location func in
    let meta_ctx, _ = !global_substitution in

    (*  Vanilla     : sqr is inferred and (lambda x -> x * x) is returned
     *  Macro       : sqr is returned
     *  Constructor : a constructor is returned
     *  Anonymous   : lambda                                                  *)

    (* retrieve function's body (sqr 3) sqr is a Pvar() *)
    let body, ltp = infer func ctx in

    let rec handle_fun_args largs sargs pending ltp =
      let ltp' = OL.lexp_whnf ltp (ectx_to_lctx ctx) meta_ctx in
      match sargs, ltp' with
      | _, Arrow (ak, Some (_, aname'), arg_type, _, ret_type)
           when SMap.mem aname' pending
        -> let sarg = SMap.find aname' pending in
          let parg = pexp_parse sarg in
          let larg = check parg arg_type ctx in
          handle_fun_args ((ak, larg) :: largs) sargs
                          (SMap.remove aname' pending)
                          (L.mkSusp ret_type (S.substitute larg))

      | [], _
        -> (if not (SMap.is_empty pending) then
             let pending = SMap.bindings pending in
             let loc = match pending with
               | (_, sarg)::_ -> sexp_location sarg
               | _ -> assert false in
             pexp_error loc func
                        ("Explicit actual args `"
                         ^ String.concat ", " (List.map (fun (l, _) -> l)
                                                        pending)
                         ^ "` have no matching formal args"));
          largs, ltp

      | (Node (Symbol (_, "_:=_"), [Symbol (_, aname); sarg])) :: sargs,
        Arrow (ak, _, arg_type, _, ret_type)
           when (aname = "_")
        (* Explicit-implicit argument.  *)
        -> let parg = pexp_parse sarg in
          let larg = check parg arg_type ctx in
          handle_fun_args ((ak, larg) :: largs) sargs pending
                          (L.mkSusp ret_type (S.substitute larg))

      | (Node (Symbol (_, "_:=_"), [Symbol (l, aname); sarg])) :: sargs,
        Arrow _
        -> if SMap.mem aname pending then
            sexp_error l ("Duplicate explicit arg `" ^ aname ^ "`");
          handle_fun_args largs sargs (SMap.add aname sarg pending) ltp

      | (Node (Symbol (_, "_:=_"), Symbol (l, aname) :: _)) :: sargs, _
        -> sexp_error l
                     ("Explicit arg `" ^ aname ^ "` to non-function "
                      ^ "(type = " ^ (lexp_string ltp) ^ ")");
          handle_fun_args largs sargs pending ltp

      | sarg :: sargs, Arrow (Aexplicit, _, arg_type, _, ret_type)
        -> let parg = pexp_parse sarg in
          let larg = check parg arg_type ctx in
          handle_fun_args ((Aexplicit, larg) :: largs) sargs pending
                          (L.mkSusp ret_type (S.substitute larg))
      (* Aimplicit, FIXME: use a meta var if a default macro is not provided *)
      | sarg :: sargs, Arrow (Aimplicit, v, arg_type, _, ret_type)
        -> ((* get default attribute *)
        (* FIXME: We shouldn't hard code as popular a name as `default`.  *)
        let pidx, pname = (senv_lookup "default" ctx), "default" in
        let default = Var((dloc, pname), pidx) in

        (* lookup default attribute of ltp *)
        let attr = get_attribute_impl loc [default; arg_type] ctx arg_type in
        (* FIXME: The `default` attribute table shouldn't contain elements of
         * type `Macro` but elements of type `something -> Sexp`.
         * The point of the `Macro` type is to be able to distinguish
         * a macro call from a function call, but here, we have no need
         * to distinguish two cases.
         * Better yet: let's not do any table lookup here.  Instead,
         * call a `default-arg-filler` function, implemented in Typer,
         * just like `expand_macro_` function.  That one can then look
         * things up in a table and/or do anything else it wants.  *)
        let v = lexp_expand_macro attr [] ctx in

        (* get the sexp returned by the macro *)
        let lsarg = match v with
          | Vsexp (sexp) -> sexp
          | _ -> value_fatal loc v "default attribute should return a sexp" in

        (* lparse the argument *)
        let parg = pexp_parse lsarg in
        let larg = check parg arg_type ctx in

            handle_fun_args ((Aimplicit, larg) :: largs) (sarg::sargs) pending
                          (L.mkSusp ret_type (S.substitute larg)))
      (* Aerasable *)
      | sarg :: sargs, Arrow (Aerasable, v, arg_type, _, ret_type)
        -> let larg = newMetavar (sexp_location sarg)
                              (match v with Some (_, name) -> name | _ -> "v")
                              arg_type in
           handle_fun_args ((Aerasable, larg) :: largs) (sarg::sargs) pending
                           (L.mkSusp ret_type (S.substitute larg))

      | sarg :: sargs, t ->
         print_lexp_ctx (ectx_to_lctx ctx);
         lexp_fatal (sexp_location sarg) t
                    ("Explicit arg `" ^ sexp_string sarg
                     ^ "` to non-function (type = " ^ lexp_string ltp ^ ")") in

    let handle_funcall () =
      (* Here we use lexp_whnf on actual code, but it's OK
       * because we only use the result when it's a "predefined constant".  *)
      match OL.lexp_whnf body (ectx_to_lctx ctx) meta_ctx with
      | Builtin((_, "Built-in"), _, _)
        -> (
        (* ------ SPECIAL ------ *)
        match !_parsing_internals, sargs with
        | true, [String (_, str)] ->
          Builtin((loc, str), ltp, None), ltp

        | true, [String (_, str); stp] ->
           let ptp = pexp_parse stp in
           let ltp, _ = infer ptp ctx in
           Builtin((loc, str), ltp, None), ltp

        | true, _ -> error loc "Wrong Usage of `Built-in`";
          dlxp, dltype

        | false, _ -> error loc "Use of `Built-in` in user code";
          dlxp, dltype)

      | e ->
        (*  Process Arguments.  *)
        let largs, ret_type = handle_fun_args [] sargs SMap.empty ltp in
          mkCall (body, List.rev largs), ret_type in

    let handle_macro_call () =
      let sxp = match lexp_expand_macro body sargs ctx with
          | Vsexp(sxp) -> sxp
          (* Those are sexp converted by the eval function *)
          | Vint(i)    -> Integer(dloc, i)
          | Vstring(s) -> String(dloc, s)
          | Vfloat(f)  -> Float(dloc, f)
          | v          ->
            value_fatal loc v "Macro_ expects `(List Sexp) -> Sexp`" in

      let pxp = pexp_parse sxp in
        infer pxp ctx  in

    (* This is the builtin Macro type *)
    let macro_type, macro_disp = match get_predef_option "Macro" ctx with
      | Some lxp -> OL.lexp_whnf lxp (ectx_to_lctx ctx) meta_ctx, true
      (* When type.typer is being parsed and the predef is not yet available *)
      | None -> dltype, false     in

    (* determine function type *)
    match func, ltp with
      | macro, _ when (macro_disp
                       && OL.conv_p meta_ctx (ectx_to_lctx ctx)
                                   ltp macro_type) -> (
        match macro with
          | Pvar(l, name) when is_builtin_macro name ->
            let pargs = List.map pexp_parse sargs in
            let largs = lexp_parse_all pargs ctx in
            let e = (get_macro_impl loc name) loc largs ctx ltp in
            let meta_ctx, _ = !global_substitution in
            (* FIXME: We don't actually need to typecheck `e`, we just need
             * to find its type.  *)
            (e, OL.check meta_ctx (ectx_to_lctx ctx) e)

          (* true macro *)
          | _ -> handle_macro_call ())

      (* FIXME: Handle special-forms here as well!  *)
      | _ -> handle_funcall ()

(*  Parse inductive type definition.  *)
and lexp_parse_inductive ctors ctx =

    let make_args (args:(arg_kind * pvar option * pexp) list) ctx
        : (arg_kind * vdef option * ltype) list =
        let rec loop args acc ctx =
            match args with
                | [] -> (List.rev acc)
                | hd::tl -> begin
                    match hd with
                    | (kind, var, exp) ->
                       let lxp = infer_type exp ctx var in
                       let nctx = ectx_extend ctx var Variable dltype in
                       loop tl ((kind, var, lxp)::acc) nctx
                  end in
        loop args [] ctx in

    List.fold_left
      (fun lctors ((_, name), args) ->
        SMap.add name (make_args args ctx) lctors)
      SMap.empty ctors

(* Macro declaration handling, return a list of declarations
 * to be processed *)
and lexp_expand_macro macro_funct sargs ctx
  = lexp_expand_macro_ macro_funct sargs ctx "expand_macro_"

and lexp_expand_dmacro macro_funct sargs ctx
  = lexp_expand_macro_ macro_funct sargs ctx "expand_dmacro_"

and lexp_expand_macro_ macro_funct sargs ctx expand_fun : value_type =

  (* Build the function to be called *)
  let macro_expand = get_predef expand_fun ctx in
  let args = [(Aexplicit, macro_funct);
              (Aexplicit, (olist2tlist_lexp sargs ctx))] in

  let macro = mkCall (macro_expand, args) in
  let emacro = OL.erase_type macro in
  let rctx = from_lctx ctx in

  (* eval macro *)
  let vxp = try _eval emacro rctx ([], [])
    with e -> print_eval_trace None; raise e in
    (* Return results *)
    (* Vint/Vstring/Vfloat might need to be converted to sexp *)
      vxp

and lexp_decls_macro (loc, mname) sargs ctx: (pdecl list * elab_context) =
   try (* Lookup macro declaration *)
     let idx = senv_lookup mname ctx in
     (* FIXME: We should only check that `ltp` is Macro, and not look
      * at `lxp` here (just like we do for expression macros).  *)
      let ltp = env_lookup_type ctx ((loc, mname), idx) in
      let lxp = env_lookup_expr ctx ((loc, mname), idx) in

      (* lxp has the form (Call (Var(_, "Macro_"), [(_, function)]))
       * We need the function so we can call it later *)
      let body, mfun = match lxp with
        | Some (Call(_, [(_, lxp)]) as e) -> e, lxp
        | Some lxp -> lxp, lxp
        | None -> fatal loc "expression does not exist" in

      (* Special Form *)
            let ret = lexp_expand_dmacro body sargs ctx in

      (* convert typer list to ocaml *)
      let decls = tlist2olist [] ret in

      (* extract sexp from result *)
      let decls = List.map (fun g ->
        match g with
          | Vsexp(sxp) -> sxp
          | _ -> value_fatal loc g "Macro expects sexp list") decls in

      (* read as pexp_declaraton *)
      pexp_decls_all decls, ctx
  with e ->
    fatal loc ("Macro `" ^ mname ^ "`not found")

and lexp_check_decls (ectx : elab_context) (* External context.  *)
                     (nctx : elab_context) (* Context with type declarations. *)
                     (defs : (vdef * pexp * ltype) list)
    : (vdef * lexp * ltype) list * elab_context =
  let declmap = List.fold_right
                  (fun ((_, vname) as v, pexp, ltp) map ->
                    let i = senv_lookup vname nctx in
                    let adjusted_ltp = push_susp ltp (S.shift (i + 1)) in
                    IntMap.add i (v, check pexp adjusted_ltp nctx, ltp)
                               map)
                  defs IntMap.empty in
  let decls = List.rev (List.map (fun (_, d) -> d) (IntMap.bindings declmap)) in
  decls, ctx_define_rec ectx decls


and lexp_decls_1
      (pdecls : pdecl list)
      (ectx : elab_context)                       (* External ctx.  *)
      (nctx : elab_context)                       (* New context.  *)
      (pending_decls : (location * ltype) SMap.t) (* Pending type decls. *)
      (pending_defs : (vdef * pexp * ltype) list) (* Pending definitions. *)
    : (vdef * lexp * ltype) list * pdecl list * elab_context =

  match pdecls with
  | [] -> (if not (SMap.is_empty pending_decls) then
            let (s, (l, _)) = SMap.choose pending_decls in
              error l ("Variable `" ^ s ^ "` declared but not defined!")
          else
            assert (pending_defs == []));
         [], [], nctx

  | Ptype ((l, vname) as v, ptp) :: pdecls
    -> let ltp = infer_type ptp nctx (Some v) in
      if SMap.mem vname pending_decls then
        (error l ("Variable `" ^ vname ^ "` declared twice!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)
      else if List.exists (fun ((_, vname'), _, _) -> vname = vname')
                          pending_defs then
        (error l ("Variable `" ^ vname ^ "` already defined!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)
      else lexp_decls_1 pdecls ectx
                        (env_extend nctx v ForwardRef ltp)
                        (SMap.add vname (l, ltp) pending_decls)
                        pending_defs

  | Pexpr ((l, vname) as v, pexp) :: pdecls
       when SMap.is_empty pending_decls
    -> assert (pending_defs == []);
      assert (ectx == nctx);
      let (lexp, ltp) = infer pexp nctx in
      (* Lexp decls are always recursive, so we have to shift by 1 to account
       * for the extra var (ourselves).  *)
      [(v, mkSusp lexp (S.shift 1), ltp)], pdecls,
      ctx_define nctx v lexp ltp

  | Pexpr ((l, vname) as v, pexp) :: pdecls
    -> (try let (_, ltp) = SMap.find vname pending_decls in
           let pending_decls = SMap.remove vname pending_decls in
           let pending_defs = ((v, pexp, ltp) :: pending_defs) in
           if SMap.is_empty pending_decls then
             let decls, nctx = lexp_check_decls ectx nctx pending_defs in
             decls, pdecls, nctx
           else
             lexp_decls_1 pdecls ectx nctx pending_decls pending_defs

       with Not_found ->
         error l ("`" ^ vname ^ "` defined but not declared!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)

  | Pmcall ((l, _) as v, sargs) :: pdecls
   -> ((* expand macro and get the generated declarations *)
      let pdecls', nctx' = lexp_decls_macro v sargs nctx in

      if nctx == nctx' then
        (* Plain macro expansion!  *)
        lexp_decls_1 (List.append pdecls' pdecls) ectx nctx
                     pending_decls pending_defs

      else if ectx == nctx then
        (assert (SMap.is_empty pending_decls);
         assert (pending_defs = []);

         lexp_decls_1 (List.append pdecls' pdecls) ectx nctx'
                      pending_decls pending_defs)

      else fatal l "Context changed in already changed context")


and lexp_p_decls pdecls ctx: ((vdef * lexp * ltype) list list * elab_context) =
  if pdecls = [] then [], ctx else
    let decls, pdecls, nctx = lexp_decls_1 pdecls ctx ctx SMap.empty [] in
    let declss, nnctx = lexp_p_decls pdecls nctx in
    decls :: declss, nnctx

and lexp_parse_all (p: pexp list) (ctx: elab_context) : lexp list =

    let rec loop (plst: pexp list) ctx (acc: lexp list) =
        match plst with
            | [] -> (List.rev acc)
            | pe :: plst  -> let lxp, _ = infer pe ctx in
                    (loop plst ctx (lxp::acc)) in

    (loop p ctx [])

(* --------------------------------------------------------------------------
 *  Built-in Macro: i.e special forms
 * -------------------------------------------------------------------------- *)
and builtin_macro = [
  (* FIXME: These should be functions!  *)
  ("decltype",      decltype_impl);
  ("declexpr",      declexpr_impl);
  (* FIXME: These are not macros but `special-forms`.
   * We should add here `let_in_`, `case_`, etc...  *)
  ("get-attribute", get_attribute_impl);
  ("new-attribute", new_attribute_impl);
  ("has-attribute", has_attribute_impl);
  ("add-attribute", add_attribute_impl);
]

and make_macro_map unit =
 List.fold_left (fun map (name, funct) ->
    SMap.add name funct map) SMap.empty builtin_macro

and get_macro_impl loc name =
  try SMap.find name (make_macro_map ())
    with Not_found -> fatal loc ("Builtin macro" ^ name ^ " not found")

and is_builtin_macro name =
  SMap.mem name (make_macro_map ())

(* --------------------------------------------------------------------------
 *  Special form implementation
 * -------------------------------------------------------------------------- *)
and new_attribute_impl loc largs ctx ftype =
  let ltp = match largs with
    | [ltp] -> ltp
    | _ -> fatal loc "new-attribute expects a single Type argument" in

  Builtin ((loc, "new-attribute"), ltp, Some AttributeMap.empty)

and add_attribute_impl loc largs ctx ftype =
  let meta_ctx, _ = !global_substitution in
  let n = get_size ctx in
  let table, var, attr = match largs with
    | [table; Var((_, name), idx); attr] -> table, (n - idx, name), attr
    | _ -> fatal loc "add-attribute expects 3 arguments (table; var; attr)" in

  let map, attr_type =  match OL.lexp_whnf table (ectx_to_lctx ctx) meta_ctx with
      | Builtin (_, attr_type, Some map)-> map, attr_type
      | _ -> fatal loc "add-attribute expects a table as first argument" in

    (* FIXME: Type check (attr: type == attr_type) *)
  let table =  AttributeMap.add var attr map in
    Builtin ((loc, "add-attribute"), attr_type, Some table)

and get_attribute_impl loc largs ctx ftype =
  let meta_ctx, _ = !global_substitution in
  let ctx_n = get_size ctx in
  let table, var = match largs with
    | [table; Var((_, name), idx)] -> table, (ctx_n - idx, name)
    | _ -> fatal loc "get-attribute expects 2 arguments (table; var)" in

  let map = match OL.lexp_whnf table (ectx_to_lctx ctx) meta_ctx with
    | Builtin (_, attr_type, Some map) -> map
    | _ -> fatal loc "get-attribute expects a table as first argument" in

  let lxp = AttributeMap.find var map in
    (lxp : lexp)

and has_attribute_impl loc largs ctx ftype =
  let meta_ctx, _ = !global_substitution in
  let n = get_size ctx in
  let table, var = match largs with
    | [table; Var((_, name), idx)] -> table, (n - idx, name)
    | _ -> fatal loc "get-attribute expects 2 arguments (table; var)" in

  let map, attr_type = match OL.lexp_whnf table (ectx_to_lctx ctx) meta_ctx with
    | Builtin (_, attr_type, Some map) -> map, attr_type
    | lxp -> lexp_fatal loc lxp "get-attribute expects a table as first argument" in

    try let _ = AttributeMap.find var map in
      (get_predef "True" ctx)
    with Not_found ->
      (get_predef "False" ctx)

(*  Only print var info *)
and lexp_print_var_info ctx =
    let ((m, _), env, _) = ctx in
    let n = Myers.length env in

    for i = 0 to n - 1 do (
        let (_, (_, name), exp, tp) = Myers.nth i env in
        print_int i; print_string " ";
        print_string name; (*   name must match *)
        print_string " = ";
         (match exp with
             | None -> print_string "<var>"
             | Some exp -> lexp_print exp);
        print_string ": ";
        lexp_print tp;
        print_string "\n")
    done

(*      Default context with builtin types
 * --------------------------------------------------------- *)

(* Make lxp context with built-in types *)
let default_lctx, default_rctx =

      (* Empty context *)
      let lctx = make_elab_context in
      let lctx = ctx_define lctx (dloc, "Type1") type1 type2 in
      let lctx = ctx_define lctx (dloc, "Type") type0 type1 in
      (* FIXME: Add builtins directly here.  *)
      let lxp = Builtin((dloc, "Built-in"), type0, None) in
      let lctx = ctx_define lctx (dloc, "Built-in") lxp type0 in

      (* Read BTL files *)
      let pres = prelex_file (!btl_folder ^ "types.typer") in
      let sxps = lex default_stt pres in
      let nods = sexp_parse_all_to_list default_grammar sxps (Some ";") in
      let pxps = pexp_decls_all nods in

      _parsing_internals := true;
          let d, lctx = lexp_p_decls pxps lctx in
      _parsing_internals := false;

      (* dump grouped decls * )
      List.iter (fun decls ->
        print_string "[";
        List.iter (fun ((_, s), _, _) ->
          print_string (s ^ ", ")) decls; print_string "] \n") d; *)

      builtin_size := get_size lctx;

      (* Once default builtin are set we can populate the predef table *)
      let lctx = try
          List.iter (fun name ->
              let idx = senv_lookup name lctx in
              let v = Var((dloc, name), idx) in
              set_predef name (Some v)) predef_name;
      (* -- DONE -- *)
          lctx
      with e ->
        warning dloc "Predef not found";
        lctx in
      lctx, from_lctx lctx

(*      String Parsing
 * --------------------------------------------------------- *)

(* Lexp helper *)
let _lexp_expr_str (str: string) (tenv: token_env)
            (grm: grammar) (limit: string option) (ctx: elab_context) =
  let pxps = _pexp_expr_str str tenv grm limit in
  let lexps = lexp_parse_all pxps ctx in
  let meta_ctx, _ = !global_substitution in
  List.iter (fun lxp -> ignore (OL.check meta_ctx (ectx_to_lctx ctx) lxp))
            lexps;
  lexps


(* specialized version *)
let lexp_expr_str str lctx =
    _lexp_expr_str str default_stt default_grammar (Some ";") lctx

let _lexp_decl_str (str: string) tenv grm limit ctx =
    let pxps = _pexp_decl_str str tenv grm limit in
        lexp_p_decls pxps ctx

(* specialized version *)
let lexp_decl_str str lctx =
    _lexp_decl_str str default_stt default_grammar (Some ";") lctx


(*  Eval String
 * --------------------------------------------------------- *)
(* Because we cant include lparse in eval.ml *)

let _eval_expr_str str lctx rctx silent =
    let lxps = lexp_expr_str str lctx in
    let elxps = List.map OL.erase_type lxps in
        (eval_all elxps rctx silent)

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
    let elxps = (List.map OL.clean_decls lxps) in
        (eval_decls_toplevel elxps rctx), lctx

