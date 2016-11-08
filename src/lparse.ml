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
let _global_lexp_trace = ref []
let _parsing_internals = ref false
let btl_folder = ref "./btl/"

let warning = msg_warning "LPARSE"
let error = msg_error "LPARSE"
let fatal = msg_fatal "LPARSE"

let root_string () =
  match !_global_lexp_trace with
    | [] -> ""
    | e::_ -> OL.pol_string e

(* Print Lexp name followed by the lexp in itself, finally throw an exception *)
let debug_message error_type type_name type_string loc expr message =
  debug_messages error_type loc
    message [
      (type_name expr) ^ ": " ^ (type_string expr);
      "Root: " ^ (root_string ());
    ]

let lexp_fatal   = debug_message fatal lexp_name lexp_string
let lexp_warning = debug_message warning lexp_name lexp_string
let lexp_error   = debug_message error lexp_name lexp_string
let pexp_fatal   = debug_message fatal pexp_name pexp_string
let pexp_error   = debug_message error pexp_name pexp_string
let value_fatal  = debug_message fatal value_name value_string

let elab_check_sort (ctx : elab_context) lsort var ltp =
  match OL.lexp_whnf lsort (ectx_to_lctx ctx) with
  | Sort (_, _) -> () (* All clear!  *)
  | _ -> let typestr = lexp_string ltp  ^ " : " ^ lexp_string lsort in
        match var with
        | None -> lexp_error (lexp_location ltp) ltp
                            ("`" ^ typestr ^ "` is not a proper type")
        | Some (l, name)
          -> lexp_error l ltp
                       ("Type of `" ^ name ^ "` is not a proper type: "
                        ^ typestr)

let elab_check_proper_type (ctx : elab_context) ltp var =
  try elab_check_sort ctx (OL.check (ectx_to_lctx ctx) ltp) var ltp
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

  let ltype' = try OL.check lctx lxp
    with e ->
      lexp_error loc lxp "Error while type-checking";
      print_lexp_ctx (ectx_to_lctx ctx);
      raise e in
  if OL.conv_p (ectx_to_lctx ctx) ltype ltype' then
    elab_check_proper_type ctx ltype (Some var)
  else
    (debug_messages fatal loc "Type check error: ¡¡ctx_define error!!" [
      (lexp_string lxp) ^ "!: " ^ (lexp_string ltype);
       "                    because";
      (lexp_string (OL.check lctx lxp)) ^ "!= " ^ (lexp_string ltype);])

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
 * infer the types and perform macro-expansion.  For won't really
 * do any of that, but we can already start structuring it accordingly.
 *
 * More specifically, we do it with 2 mutually recursive functions:
 * one takes a Pexp along with its expected type and return an Lexp
 * of that type (hopefully), whereas the other takes a Pexp and
 * infers its type (which it returns along with the Lexp).
 * This is the idea of "bidirectional type checking", which minimizes
 * the amount of "guessing" and/or annotations.  Basically guessing/annotations
 * is only needed at those few places where the code is not fully-normalized,
 * which in normal programs is only in "let" definitions.
 * So the rule of thumbs are:
 * - use lexp_p_infer for destructors, and use lexp_p_check for constructors.
 * - use lexp_p_check whenever you can.
 *)


let rec _lexp_p_infer (p : pexp) (ctx : elab_context) trace: lexp * ltype =

    let trace = ((OL.Pexp p)::trace) in
    let tloc = pexp_location p in
    let lexp_infer p ctx = _lexp_p_infer p ctx trace in

    (* Save current trace in a global variable.  If an error occur,
       we will be able to retrieve the most recent trace and context.  *)
    _global_lexp_ctx := ctx;
    _global_lexp_trace := trace;

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
           let idx = (senv_lookup name ctx) in
           let lxp = (make_var name idx loc) in

           (* Search type.  *)
           let ltp = env_lookup_type ctx ((loc, name), idx) in
           lxp, ltp (* Return Macro[22] *)

         with Not_found ->
           (pexp_error loc p ("The variable: `" ^ name ^ "` was not declared");
            (* Error recovery. The -1 index will raise an error later on *)
            (make_var name (-1) loc), dltype))

    (* Let, Variable declaration + local scope.  *)
    | Plet (loc, decls, body)
      -> let declss, nctx = _lexp_decls decls ctx trace in
        let bdy, ltp = lexp_infer body nctx in
        let s = List.fold_left (OL.lexp_defs_subst loc) S.identity declss in
        (lexp_let_decls declss bdy nctx trace),
        mkSusp ltp s

    (* ------------------------------------------------------------------ *)
    | Parrow (kind, ovar, tp, loc, expr)
      -> let ltp = lexp_type_infer tp ctx ovar trace in
        let nctx = ectx_extend ctx ovar Variable ltp in

        let lxp = lexp_type_infer expr nctx None trace in

        let v = mkArrow(kind, ovar, ltp, tloc, lxp) in
        v, type0

    | Pinductive (label, formal_args, ctors)
      -> let nctx = ref ctx in
        (* (arg_kind * pvar * pexp option) list *)
        let formal = List.map (fun (kind, var, opxp)
                               -> let ltp, _ = match opxp with
                                   | Some pxp -> _lexp_p_infer pxp !nctx trace
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

        let map_ctor = lexp_parse_inductive ctors nctx trace in
        let v = mkInductive(tloc, label, formal, map_ctor) in
        v, ltp

    (* This case can be inferred *)
    | Plambda (kind, var, optype, body)
      -> let ltp, _ = match optype with
          | Some ptype -> lexp_infer ptype ctx
          (* This case must have been lexp_p_check *)
          | None -> pexp_error tloc p "Lambda require type annotation";
                   dltype, dltype in

        let nctx = env_extend ctx var Variable ltp in
        let lbody, lbtp = lexp_infer body nctx in

        let lambda_type = mkArrow (kind, Some var, ltp, tloc, lbtp) in
        mkLambda(kind, var, ltp, lbody), lambda_type

    | Pcall (fname, _args) -> lexp_call fname _args ctx trace

    | Pcons(t, sym)
      -> let idt, _ = lexp_infer t ctx in
        let (loc, cname) = sym in

        (* Get constructor args.  *)
        let formal, args = match OL.lexp_whnf idt (ectx_to_lctx ctx) with
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
        let target = if formal = [] then
                       push_susp idt (S.shift (List.length args))
                     else
                       let targs, _
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
      -> let ltp = lexp_type_infer ptp ctx None trace in
        (_lexp_p_check pxp ltp ctx trace), ltp

    | _ -> pexp_fatal tloc p "Unhandled Pexp"

and lexp_type_infer pexp ectx var trace =
  let t, s = _lexp_p_infer pexp ectx trace in
  elab_check_sort ectx s var t;
  t

and lexp_let_decls declss (body: lexp) ctx i =
  List.fold_right (fun decls lxp -> mkLet (dloc, decls, lxp))
                  declss body

and _lexp_p_check (p : pexp) (t : ltype) (ctx : elab_context) trace: lexp =

    let trace = ((OL.Pexp p)::trace) in
    let tloc = pexp_location p in
    let lexp_infer p ctx = _lexp_p_infer p ctx trace in
    let lexp_check p ltp ctx = _lexp_p_check p ltp ctx trace in

    (* Safe current trace in a global variable. If an error occur,
       we will be able to retrieve the most recent trace and context *)
    _global_lexp_ctx := ctx;
    _global_lexp_trace := trace;

    match p with
    (* This case cannot be inferred *)
    | Plambda (kind, var, def_arg_type, body)
      -> (* Read var type from the provided type *)
       let given_arg_type, given_body_type = match OL.lexp_whnf t (ectx_to_lctx ctx) with
         | Arrow(kind, _, ltp, _, lbtp) -> ltp, lbtp
         | expr ->
            lexp_fatal tloc expr "Expected Type Arrow ( _ -> _ )" in

       (* Check argument type *)
       let _ = match def_arg_type with
         | Some def_arg_type
           -> let def_arg_type, lasort = _lexp_p_infer def_arg_type ctx trace in
             elab_check_sort ctx lasort (Some var) def_arg_type;
             () (* FIXME: Check `conv_p def_arg_type given_arg_type`!  *)
         | _ -> () in

       let nctx = env_extend ctx var Variable latp in
       let lbody = lexp_check body given_body_type nctx in

       mkLambda(kind, var, given_arg_type, lbody)

    (* This is mostly for the case where no branches are provided *)
    | Pcase (loc, target, branches)
      -> lexp_case t (loc, target, branches) ctx trace

    (* FIXME: Handle *macro* pcalls here! *)
    (* | Pcall (fname, _args) -> *)

    | _ -> let (e, inferred_t) = lexp_infer p ctx in
          if not (OL.conv_p (ectx_to_lctx ctx) inferred_t t) then
            lexp_error (pexp_location p) e
                       ("Type mismatch!  Context expected `"
                        ^ lexp_string t ^ "` but expression has type `"
                        ^ lexp_string inferred_t ^ "`\n");
          e

(* Lexp.case can sometimes be inferred, but we prefer to always check.  *)
and lexp_case rtype (loc, target, ppatterns) ctx i =
    (* FIXME: check if case is exhaustive  *)
    (* Helpers *)

  let lexp_infer p ctx = _lexp_p_infer p ctx i in

  let pat_string p = sexp_string (pexp_u_pat p) in

    let uniqueness_warn pat =
      warning (pexp_pat_location pat)
              ("Pattern " ^ pat_string pat
               ^ " is a duplicate.  It will override previous pattern.") in

    let check_uniqueness pat name map =
        try let _ = SMap.find name map in uniqueness_warn pat
            with e -> () in

    (* get target and its type *)
    let tlxp, tltp = lexp_infer target ctx in
    (* FIXME: We need to be careful with whnf: while the output is equivalent
     * to the input, it's not necessarily as readable.  So try to reuse the
     * "non-whnf" form whenever possible.  *)
    let call_split e = match (OL.lexp_whnf e (ectx_to_lctx ctx)) with
      | Call (f, args) -> (f, args)
      | _ -> (e,[]) in
    let it, targs = call_split tltp in
    let constructors = match OL.lexp_whnf it (ectx_to_lctx ctx) with
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
        let lexp = _lexp_p_check pexp rtype' nctx i in
        lbranches, Some (v, lexp) in

      let add_branch pctor pargs =
        let loc = pexp_location pctor in
        let lctor, _ = _lexp_p_infer pctor ctx i in
        match OL.lexp_whnf lctor (ectx_to_lctx ctx) with
        | Cons (it', (_, cons_name))
          -> let _ = if OL.conv_p (ectx_to_lctx ctx) it' it then ()
                    else lexp_error loc lctor
                                    ("Expected pattern of type `"
                                     ^ lexp_string it ^ "` but got `"
                                    ^ lexp_string it' ^ "`") in
            let _ = check_uniqueness pat cons_name lbranches in
            let cons_args
              = try SMap.find cons_name constructors
                with Not_found
                     -> lexp_error loc lctor
                                  ("`" ^ (lexp_string it)
                                   ^ "` does not have a `"
                                   ^ cons_name ^ "` constructor");
                       [] in

            let subst = List.fold_right (fun (_, t) s -> S.cons t s)
                                        targs S.identity in
            let rec make_nctx ctx fargs s pargs cargs = match pargs, cargs with
              | [], [] -> ctx, List.rev fargs
              | (_, pat)::_, []
                -> lexp_error loc lctor
                             "Too many arguments to the constructor";
                  make_nctx ctx fargs s [] []
              | (None, Ppatany _)::pargs, (Aexplicit, _, fty)::cargs
                -> let nctx = ctx_extend ctx None Variable (mkSusp fty s) in
                  make_nctx nctx ((Aexplicit, None)::fargs)
                            (ssink vdummy s) pargs cargs
              | (None, Ppatsym v)::pargs, (Aexplicit, _, fty)::cargs
                -> let nctx = ctx_extend ctx (Some v) Variable (mkSusp fty s) in
                  make_nctx nctx ((Aexplicit, Some v)::fargs)
                            (ssink v s) pargs cargs
              | (_, Ppatcons (p, _))::pargs, cargs
                -> lexp_error (pexp_location p) lctor
                             "Nested patterns not supported!";
                  make_nctx ctx fargs s pargs cargs
              | pargs, (ak, _, fty)::cargs
                -> let nctx = ctx_extend ctx None Variable (mkSusp fty s) in
                  make_nctx nctx ((ak, None)::fargs)
                            (ssink vdummy s) pargs cargs in
            let nctx, fargs = make_nctx ctx [] subst pargs cons_args in
            let rtype' = mkSusp rtype
                                (S.shift (M.length (ectx_to_lctx nctx)
                                          - M.length (ectx_to_lctx ctx))) in
            let lexp = _lexp_p_check pexp rtype' nctx i in
            SMap.add cons_name (loc, fargs, lexp) lbranches,
            dflt
        | _ -> lexp_error loc lctor "Not a constructor"; lbranches, dflt
      in

      match pat with
      | Ppatany _ -> add_default None
      | Ppatsym ((_, name) as var)
        -> (try let idx = senv_lookup name ctx in
               match OL.lexp_whnf (mkVar (var, idx)) (ectx_to_lctx ctx) with
               | Cons _         (* It's indeed a constructor!  *)
                 -> add_branch (Pvar var) []
               | _ -> add_default (Some var) (* A named default branch.  *)
           with Not_found -> add_default (Some var))

      | Ppatcons (pctor, pargs) -> add_branch pctor pargs in

    let (lpattern, dflt) =
        List.fold_left fold_fun (SMap.empty, None) ppatterns in

    mkCase (loc, tlxp, rtype, lpattern, dflt)

(*  Identify Call Type and return processed call *)
and lexp_call (func: pexp) (sargs: sexp list) ctx i =
    let loc = pexp_location func in

    let lexp_infer p ctx = _lexp_p_infer p ctx i in
    let lexp_check p ltp ctx = _lexp_p_check p ltp ctx i in

    (*  Vanilla     : sqr is inferred and (lambda x -> x * x) is returned
     *  Macro       : sqr is returned
     *  Constructor : a constructor is returned
     *  Anonymous   : lambda                                                  *)

    (* retrieve function's body (sqr 3) sqr is a Pvar() *)
    let body, ltp = lexp_infer func ctx in
    let ltp = nosusp ltp in

    let rec handle_fun_args largs sargs ltp = match sargs with
      | [] -> largs, ltp
      | (Node (Symbol (_, "_:=_"), [Symbol (_, aname); sarg])) :: sargs
        (* Explicit-implicit argument.  *)
        (* check if a = b in (a : Type) -> ... and (b := val) *)
        -> (match OL.lexp_whnf ltp (ectx_to_lctx ctx) with
           | Arrow (ak, Some (_, aname'), arg_type, _, ret_type)
                when (aname = aname' || aname = "_")
             -> let parg = pexp_parse sarg in
               let larg = lexp_check parg arg_type ctx in
               handle_fun_args ((ak, larg) :: largs) sargs
                               (L.mkSusp ret_type (S.substitute larg))

           | _ -> fatal (sexp_location sarg)
                  ("Explicit arg `" ^ aname ^ "` to non-function " ^
                    "(type = " ^ (lexp_string ltp) ^ ")"))
      | sarg :: sargs
        (*  Process Argument *)
        -> (match OL.lexp_whnf ltp (ectx_to_lctx ctx) with
           | Arrow (Aexplicit, _, arg_type, _, ret_type)
             -> let parg = pexp_parse sarg in
               let larg = _lexp_p_check parg arg_type ctx i in
               handle_fun_args ((Aexplicit, larg) :: largs) sargs
                               (L.mkSusp ret_type (S.substitute larg))
           | Arrow _ as t ->
              debug_messages fatal (sexp_location sarg) "Expected non-explicit arg" [
                "ltype    : " ^ (lexp_string t);
                "s-exp arg: " ^ (sexp_string sarg);]

           | t ->
              print_lexp_ctx (ectx_to_lctx ctx);
              lexp_fatal (sexp_location sarg) t
                ("Explicit arg `" ^ sexp_string sarg ^
                 "` to non-function (type = " ^ lexp_string ltp ^ ")")) in

    let handle_funcall () =
      (* Here we use lexp_whnf on actual code, but it's OK
       * because we only use the result when it's a "predefined constant".  *)
      match OL.lexp_whnf body (ectx_to_lctx ctx) with
      | Builtin((_, "Built-in"), _)
        -> (
        (* ------ SPECIAL ------ *)
        match !_parsing_internals, sargs with
        | true, [String (_, str)] ->
          Builtin((loc, str), ltp), ltp

        | true, [String (_, str); stp] ->
           let ptp = pexp_parse stp in
           let ltp, _ = lexp_infer ptp ctx in
           Builtin((loc, str), ltp), ltp

        | true, _ -> error loc "Wrong Usage of `Built-in`";
          dlxp, dltype

        | false, _ -> error loc "Use of `Built-in` in user code";
          dlxp, dltype)

      | _ ->
        (*  Process Arguments *)

        (* Extract correct ordering aargs: all args and eargs: explicit args*)
        let rec extract_order ltp aargs eargs =
          match OL.lexp_whnf ltp (ectx_to_lctx ctx) with
            | Arrow (kind, Some (_, varname), ltp, _, ret) ->
                extract_order ret ((kind, varname, ltp)::aargs)
                  (if kind = Aexplicit then (varname::eargs) else eargs)

            | e -> (List.rev aargs), List.rev eargs in

        (* first list has all the arguments, second only holds explicit arguments *)
        let order, eorder = extract_order ltp [] [] in

        (*)
        print_string "Type :"; lexp_print ltp; print_string "\n";
        print_string "Order:"; List.iter (fun (_, b, _) -> print_string (b ^ " ")) (order); print_string "\n";
        print_string "Sarg1: ";
        List.iter (fun lxp -> sexp_print lxp; print_string ", ") sargs;
        print_string "\n";*)


        (* from arg order build a dictionnary that will hold the defined args *)
        let args_dict = List.fold_left
          (fun map (kind, key, _) -> SMap.add key (kind, None) map) SMap.empty order in

        let args_dict, eargs = List.fold_left (fun (map, eargs) sexp ->
          match sexp with
            | Node (Symbol (_, "_:=_"), [Symbol (_, aname); sarg]) ->
              let kind, _ = try SMap.find aname map
                with Not_found ->
                  print_string (aname ^ " was not found" ^ "\n");
                  Aerasable, None in
                (SMap.add aname (kind, Some sarg) map),
                (if kind = Aexplicit then
                  (match eargs with
                    | _::tl -> tl
                    | _ -> []) else eargs)

            | _ -> (match eargs with
              | name::tl -> (SMap.add name (Aexplicit, Some sexp) map), tl
              | _ -> map, []))
                (args_dict, eorder) sargs in


        (* Generate an argument list with the correct order *)
        let sargs2 = List.map (fun (_, name, ltp) ->
          try match SMap.find name args_dict with
            | Aimplicit, (Some sexp) -> Node (Symbol (dloc, "_:=_"), [Symbol (dloc, name); sexp])
            | Aerasable,  Some sexp  -> Node (Symbol (dloc, "_:=_"), [Symbol (dloc, name); sexp])
            | Aexplicit, (Some sexp) -> sexp
            | Aexplicit, None        -> fatal dloc "Explicit argument expected"
            | Aimplicit, None        -> (
                (* get variable info *)
                let vidx, vname = match ltp with
                  | Var ((_, name), idx) -> idx, name
                  | _ -> lexp_fatal loc ltp "Unable to find default attribute" in

                (* get default property *)
                let pidx, pname = (senv_lookup "default" ctx), "default" in

                (* get macro *)
                let default_macro = try get_property ctx (vidx, vname) (pidx, pname)
                  with _ -> dump_properties ctx; dltype in

                lexp_print default_macro;

                print_string ((lexp_name ltp) ^ ": ");
                lexp_print ltp; print_string "\n";
                fatal dloc "Default Arg lookup not implemented")


            with Not_found -> fatal dloc (name ^ " not found")
          ) order in

        (*
        print_string "\nSarg2: "; List.iter (fun lxp -> sexp_print lxp; print_string ", ") sargs2;
        print_string "\n"; *)

        (* check if we had enough information to reorder args *)
        let sargs = if (List.length order >= List.length sargs) then sargs2 else sargs in

        let largs, ret_type = handle_fun_args [] sargs ltp in
        mkCall (body, List.rev largs), ret_type in

    let handle_macro_call () =
      let sxp = match lexp_expand_macro body sargs ctx i with
          | Vsexp(sxp) -> sxp
          (* Those are sexp converted by the eval function *)
          | Vint(i)    -> Integer(dloc, i)
          | Vstring(s) -> String(dloc, s)
          | Vfloat(f)  -> Float(dloc, f)
          | v          ->
            value_fatal loc v "Macro_ expects `(List Sexp) -> Sexp`" in

      let pxp = pexp_parse sxp in
        lexp_infer pxp ctx  in

    (* This is the builtin Macro type *)
    let macro_type, macro_disp = match get_predef_option "Macro" ctx with
      | Some lxp -> OL.lexp_whnf lxp (ectx_to_lctx ctx), true
      (* When type.typer is being parsed and the predef is not yet available *)
      | None -> dltype, false     in

    (* determine function type *)
    match func, ltp with
      | macro, _ when (macro_disp
                       && OL.conv_p (ectx_to_lctx ctx) ltp macro_type) -> (
        match macro with
          | Pvar(l, name) when is_builtin_macro name ->
            let pargs = List.map pexp_parse sargs in
            let largs = _lexp_parse_all pargs ctx i in
              (get_macro_impl loc name) loc largs ctx ltp

          (* true macro *)
          | _ -> handle_macro_call ())

      (* FIXME: Handle special-forms here as well!  *)
      | _ -> handle_funcall ()

(*  Parse inductive type definition.  *)
and lexp_parse_inductive ctors ctx i =
    let lexp_parse p ctx = _lexp_p_infer p ctx i in

    let make_args (args:(arg_kind * pvar option * pexp) list) ctx
        : (arg_kind * vdef option * ltype) list =
        let rec loop args acc ctx =
            match args with
                | [] -> (List.rev acc)
                | hd::tl -> begin
                    match hd with
                    | (kind, var, exp) ->
                       let lxp, _ = lexp_parse exp ctx in
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
and lexp_expand_macro macro_funct sargs ctx trace
  = lexp_expand_macro_ macro_funct sargs ctx trace "expand_macro_"

and lexp_expand_dmacro macro_funct sargs ctx trace
  = lexp_expand_macro_ macro_funct sargs ctx trace "expand_dmacro_"

and lexp_expand_macro_ macro_funct sargs ctx trace expand_fun =

  (* Build the function to be called *)
  let macro_expand = get_predef expand_fun ctx in
  let args = [(Aexplicit, macro_funct); (Aexplicit, (olist2tlist_lexp sargs ctx))] in

  let macro = mkCall (macro_expand, args) in
  let emacro = OL.erase_type macro in
  let rctx = from_lctx ctx in

  (* eval macro *)
  let vxp = try _eval emacro rctx (trace, [])
    with e -> print_eval_trace None; raise e in
    (* Return results *)
    (* Vint/Vstring/Vfloat might need to be converted to sexp *)
      vxp

and lexp_decls_macro (loc, mname) sargs ctx: (pdecl list * elab_context) =
   try (* Lookup macro declaration *)
      let idx = senv_lookup mname ctx in
      let ltp = env_lookup_type ctx ((loc, mname), idx) in
      let lxp = env_lookup_expr ctx ((loc, mname), idx) in

      (* lxp has the form (Call (Var(_, "Macro_"), [(_, function)]))
       * We need the function so we can call it later *)
      let body, mfun = match lxp with
        | Some (Call(_, [(_, lxp)]) as e) -> e, lxp
        | Some lxp -> lxp, lxp
        | None -> fatal loc "expression does not exist" in

      (* Special Form *)
        match mfun with
          | Var((_, "add-attribute"), _) ->(
            (* Builtin macro *)
            let pargs = List.map pexp_parse sargs in
            let largs = _lexp_parse_all pargs ctx [] in

            (* extract info *)
            let var, att, fn = match largs with
              | [Var((_, vn), vi); Var((_, an), ai); fn] -> (vi, vn), (ai, an), fn
              | _ -> fatal loc "add-attribute expects 3 args" in

            let ctx = add_property ctx var att fn in

            (* FIXME: We need to have something in lexp to represent this
             * add-attribute operation!  *)
              [], ctx)

          | _ ->(
            let ret = lexp_expand_dmacro body sargs ctx [] in

            (* convert typer list to ocaml *)
            let decls = tlist2olist [] ret in

            (* extract sexp from result *)
            let decls = List.map (fun g ->
              match g with
                | Vsexp(sxp) -> sxp
                | _ -> value_fatal loc g "Macro expects sexp list") decls in

            (* read as pexp_declaraton *)
            pexp_decls_all decls, ctx)
  with e ->
    fatal loc ("Macro `" ^ mname ^ "`not found")

(*  Parse let declaration *)
and lexp_p_decls decls ctx = _lexp_decls decls ctx []

and lexp_check_decls (ectx : elab_context) (* External context.  *)
                     (nctx : elab_context) (* Context with type declarations. *)
                     (defs : (vdef * pexp * ltype) list)
    : (vdef * lexp * ltype) list * elab_context =
  let declmap = List.fold_right
                  (fun ((_, vname) as v, pexp, ltp) map ->
                    let i = senv_lookup vname nctx in
                    let adjusted_ltp = push_susp ltp (S.shift (i + 1)) in
                    IntMap.add i (v, _lexp_p_check pexp adjusted_ltp nctx [], ltp)
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
    -> let (ltp, lsort) = _lexp_p_infer ptp nctx [] in
      if SMap.mem vname pending_decls then
        (error l ("Variable `" ^ vname ^ "` declared twice!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)
      else if List.exists (fun ((_, vname'), _, _) -> vname = vname')
                          pending_defs then
        (error l ("Variable `" ^ vname ^ "` already defined!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)
      else (elab_check_sort nctx lsort (Some v) ltp;
            lexp_decls_1 pdecls ectx
                         (env_extend nctx v ForwardRef ltp)
                         (SMap.add vname (l, ltp) pending_decls)
                         pending_defs)

  | Pexpr ((l, vname) as v, pexp) :: pdecls
       when SMap.is_empty pending_decls
    -> assert (pending_defs == []);
      assert (ectx == nctx);
      let (lexp, ltp) = _lexp_p_infer pexp nctx [] in
      (* Lexp decls are always recursive, so we have to shift by 1 to account
       * for the extra var (ourselves).  *)
      [(v, push_susp lexp (S.shift 1), ltp)], pdecls,
      env_extend nctx v (LetDef lexp) ltp

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


and _lexp_decls pdecls ctx i: ((vdef * lexp * ltype) list list * elab_context) =
  if pdecls = [] then [], ctx else
    let decls, pdecls, nctx = lexp_decls_1 pdecls ctx ctx SMap.empty [] in
    let declss, nnctx = _lexp_decls pdecls nctx i in
    decls :: declss, nnctx

and lexp_decls_toplevel decls ctx =
  _lexp_decls decls ctx []

and _lexp_parse_all (p: pexp list) (ctx: elab_context) i : lexp list =

    let rec loop (plst: pexp list) ctx (acc: lexp list) =
        match plst with
            | [] -> (List.rev acc)
            | pe :: plst  -> let lxp, _ = _lexp_p_infer pe ctx i in
                    (loop plst ctx (lxp::acc)) in

    (loop p ctx [])


and print_lexp_trace (trace : (OL.pexporlexp list) option) =
  print_trace " ELAB TRACE " trace !_global_lexp_trace

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

(* Those call reinitialize the calltrace *)
let lexp_parse_all p ctx = _lexp_parse_all p ctx []

let lexp_p_check (p : pexp) (t : ltype) (ctx : elab_context): lexp =
  _lexp_p_check p t ctx []

let lexp_p_infer (p : pexp) (ctx : elab_context): lexp * ltype =
    _lexp_p_infer p ctx []


(*      Default context with builtin types
 * --------------------------------------------------------- *)

(* Make lxp context with built-in types *)
let default_lctx, default_rctx =

      (* Empty context *)
      let lctx = make_elab_context in
      let lctx = ctx_define lctx (dloc, "Type1") type1 type2 in
      let lctx = ctx_define lctx (dloc, "Type") type0 type1 in
      (* FIXME: Add builtins directly here.  *)
      let lxp = Builtin((dloc, "Built-in"), type0) in
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
      let rctx = make_runtime_ctx in
      let rctx = eval_decls_toplevel (List.map OL.clean_decls d) rctx in
        lctx, rctx

(*      String Parsing
 * --------------------------------------------------------- *)

(* Lexp helper *)
let _lexp_expr_str (str: string) (tenv: token_env)
            (grm: grammar) (limit: string option) (ctx: elab_context) =
    let pxps = _pexp_expr_str str tenv grm limit in
        lexp_parse_all pxps ctx

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

