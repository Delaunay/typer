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
    Var(((loc, name), index))

let dlxp = type0
let dltype = type0
let dloc = dummy_location

let lexp_warning = msg_warning "LPARSE"
let lexp_error = msg_error "LPARSE"
let lexp_fatal = msg_fatal "LPARSE"

let _global_lexp_ctx = ref make_elab_context
let _global_lexp_trace = ref []
let _parsing_internals = ref false
let btl_folder = ref "./btl/"

(* Print Lexp name followed by the lexp in itself, finally throw an exception *)
let lexp_debug_message loc lxp message =
  print_string "\n";
  print_string (lexp_string lxp); print_string ": "; lexp_print lxp; print_string "\n";
  lexp_fatal loc message


(* merged declaration, allow us to process declaration in multiple pass *)
(* first detect recursive decls then lexp decls*)
type mdecl =
  | Ldecl of symbol * pexp option * pexp option
  | Lmcall of symbol * sexp list

let elab_check_sort (ctx : elab_context) lsort (l, name) ltp =
  match OL.lexp_whnf lsort (ectx_to_lctx ctx) VMap.empty with
  | Sort (_, _) -> () (* All clear!  *)
  | _ -> lexp_error l ("Type of `" ^ name ^ "` is not a proper type: "
                      ^ lexp_string ltp)

let elab_check_proper_type (ctx : elab_context) ltp v =
  try elab_check_sort ctx (OL.check (ectx_to_lctx ctx) ltp) v ltp
  with e -> print_string ("Exception while checking type `"
                         ^ lexp_string ltp ^ "` of var `" ^
                           (let (_, name) = v in name) ^"`\n");
           print_lexp_ctx (ectx_to_lctx ctx);
           raise e

let elab_check_def (ctx : elab_context) var lxp ltype =
  let lctx = ectx_to_lctx ctx in
  let ltype' = try OL.check lctx lxp
               with e ->
                 print_string "Error while type-checking:\n";
                 lexp_print lxp;
                 print_string "\nIn context:\n";
                 print_lexp_ctx (ectx_to_lctx ctx);
                 raise e in
  (* FIXME: conv_p fails too often, e.g. it fails to see that `Type` is
   * convertible to `Type_0`, because it doesn't have access to lctx. *)
  if true (* OL.conv_p ltype ltype' *) then
    elab_check_proper_type ctx ltype var
  else
    (print_string "¡¡ctx_define error!!\n";
     lexp_print lxp;
     print_string " !: ";
     lexp_print ltype;
     print_string "\nbecause\n";
     lexp_print (OL.check lctx lxp);
     print_string " != ";
     lexp_print ltype;
     print_string "\n";
     lexp_fatal (let (l,_) = var in l) "TC error")

let ctx_define (ctx: elab_context) var lxp ltype =
  elab_check_def ctx var lxp ltype;
  env_extend ctx var (LetDef lxp) ltype

let ctx_define_rec (ctx: elab_context) decls =
  let nctx = ectx_extend_rec ctx decls in
  let _ = List.fold_left (fun n (var, lxp, ltp)
                          -> elab_check_proper_type
                              nctx (push_susp ltp (S.shift n)) var;
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


let build_var name ctx =
    let type0_idx = senv_lookup name ctx in
        Var((dloc, name), type0_idx)

(* FIXME: We need to keep track of the type of metavars.  We could keep it
 * in the `Metavar` constructor of the `lexp` type, but that's risky (it could
 * be difficult to make sure it's the same for all occurrences of that
 * metavar).  *)

(* :-( *)
let global_substitution = ref (empty_subst, [])

let mkMetavar () = let meta = Unif.create_metavar ()
  in let name = "__Metavar_" ^ (string_of_int meta)
  in Metavar (meta, S.Identity, (Util.dummy_location, name))

let rec lexp_p_infer (p : pexp) (ctx : elab_context): lexp * ltype =
    _lexp_p_infer p ctx 1

and _lexp_p_infer (p : pexp) (ctx : elab_context) i: lexp * ltype =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let _lexp_p_infer p ctx i");
      prerr_endline ("[StackTrace] p        = " ^ pexp_string p);
      prerr_endline ("[StackTrace] ctx      = ???");
      prerr_endline ("[StackTrace] i        = " ^ string_of_int i);
      (* prerr_endline (Printexc.raw_backtrace_to_string (Printexc.get_callstack 20)); *)
      prerr_endline ("[StackTrace] ------------------------------------------");
      ());

    let lexp_infer p ctx = _lexp_p_infer p ctx (i + 1) in
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value -> (Imm(value),
            match value with
                | Integer _ -> type_int
                | Float _   -> type_float
                | String _  -> type_string;
                | _ -> lexp_error tloc "Could not find type";
                        pexp_print p; print_string "\n"; dltype)

        (*  Symbol i.e identifier *)
        | Pvar (loc, name) ->(
            try
                let idx = (senv_lookup name ctx) in
                let lxp = (make_var name idx loc) in

                (* search type *)
                let ltp = env_lookup_type ctx ((loc, name), idx) in
                    lxp, ltp (* Return Macro[22] *)

            with Not_found ->
                (lexp_error loc ("The variable: \"" ^ name ^ "\" was not declared");
                (* Error recovery. The -1 index will raise an error later on *)
                (make_var name (-1) loc), dltype))

        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->
            let decls, nctx = _lexp_decls decls ctx i in
            let bdy, ltp = lexp_infer body nctx in
              (lexp_let_decls decls bdy nctx i), ltp

        (* ------------------------------------------------------------------ *)
        | Parrow (kind, ovar, tp, loc, expr) ->
            let ltp, _ = lexp_infer tp ctx in
            let nctx = ectx_extend ctx ovar Variable ltp in

            let lxp, _ = lexp_infer expr nctx in

            let v = Arrow(kind, ovar, ltp, tloc, lxp) in
                v, type0

        (* Pinductive *)
        | Pinductive (label, formal_args, ctors) ->
            let nctx = ref ctx in
            (* (arg_kind * pvar * pexp option) list *)
            let formal = List.map (fun (kind, var, opxp) ->
                let ltp, _ = match opxp with
                    | Some pxp -> _lexp_p_infer pxp !nctx (i + 1)
                    | None -> dltype, dltype in

                nctx := env_extend !nctx var Variable ltp;
                    (kind, var, ltp)
                ) formal_args in

            let nctx = !nctx in
            let ltp = List.fold_left (fun tp (kind, v, ltp)
                                      -> (Arrow (kind, Some v, ltp, tloc, tp)))
                                     (* FIXME: See OL.check for how to
                                      * compute the real target sort
                                      * (not always type0).  *)
                                     type0 (List.rev formal) in

            let map_ctor = lexp_parse_inductive ctors nctx i in
            let v = Inductive(tloc, label, formal, map_ctor) in
                v, ltp

        | Pcall (fname, _args) ->
            lexp_call fname _args ctx i

        (* Pcons *)
        | Pcons(t, sym) ->
            let idt, _ = lexp_infer t ctx in
            let (loc, cname) = sym in
            let meta_ctx, _ = !global_substitution in

            (* Get constructor args *)
            let formal, args = match OL.lexp_whnf idt (ectx_to_lctx ctx)
                                                  meta_ctx with
              | Inductive(_, _, formal, ctor_def) -> (
                try formal, (SMap.find cname ctor_def)
                with Not_found ->
                  lexp_error loc
                             ("Constructor \"" ^ cname ^ "\" does not exist");
                  [], [])

              | _ -> lexp_error loc "Not an Inductive Type";
                    Debug_fun.do_debug (fun () ->
                        print_string "idt  : ";
                        lexp_print (nosusp idt);
                        print_string (", p : " ^ (pexp_string p));
                        print_newline (); ());
                    [], [] in

            (* build Arrow type *)
            let target = if formal = [] then
                           push_susp idt (S.shift (List.length args))
                         else
                           let targs, _ =
                             List.fold_right
                               (fun (ak, v, _) (targs, i)
                                -> ((ak, Var (v, i)) :: targs,
                                   i - 1))
                               formal
                               ([], List.length formal + List.length args - 1) in
                           Call (push_susp idt (S.shift (List.length formal
                                                         + List.length args)),
                                 targs) in
            let cons_type
              = List.fold_left (fun ltp (kind, v, tp)
                                -> Arrow (kind, v, tp, loc, ltp))
                               target
                               (List.rev args) in

            (* Add Aerasable argument *)
            let cons_type = List.fold_left
                              (fun ltp (kind, v, tp)
                               -> Arrow (Aerasable, Some v, tp, loc, ltp))
                              cons_type (List.rev formal) in

            Cons(idt, sym), cons_type

        (* Pcase: we can infer iff `patterns` is not empty *)
        | Pcase (loc, target, patterns) ->
            lexp_case None (loc, target, patterns) ctx i

        | Pmetavar _ -> (let meta = mkMetavar () (*TODO *)
                         and type_ = mkMetavar ()
                         in lexp_warning dloc "<LEXP_P_INFER>(Pmetavar case) Check output : may be wrong lexp/type returned";
                         (meta, type_) (* FIXME return the right type *))

        | Phastype (_, pxp, ptp) ->
            let ltp, _ = lexp_infer ptp ctx in
                (_lexp_p_check pxp ltp ctx (i + 1)), ltp

        | Plambda _ -> (let meta = mkMetavar ()
                in let lxp = lexp_p_check p meta ctx
                in (lxp, meta))

and lexp_let_decls decls (body: lexp) ctx i =
  (* build the weird looking let *)
  let decls = List.rev decls in
    List.fold_left (fun lxp decls ->
      Let(dloc, decls, lxp)) body decls

and lexp_p_check (p : pexp) (t : ltype) (ctx : elab_context): lexp =
  _lexp_p_check p t ctx 1

and _lexp_p_check (p : pexp) (t : ltype) (ctx : elab_context) i: lexp =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let _lexp_p_check p t ctx i");
      prerr_endline ("[StackTrace] p        = " ^ pexp_string p);
      prerr_endline ("[StackTrace] t        = " ^ lexp_string t);
      prerr_endline ("[StackTrace] ctx      = ???");
      prerr_endline ("[StackTrace] i        = " ^ string_of_int i);
      prerr_endline ("[StackTrace] ------------------------------------------");
      ());
    let tloc = pexp_location p
    in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    let unify_with_arrow lxp kind subst =
      let arg, body = mkMetavar (), mkMetavar ()
      in let arrow = Arrow (kind, None, arg, Util.dummy_location, body)
      in match Unif.unify arrow lxp subst with
      | Some(subst) -> global_substitution := subst; arg, body
      | None       -> lexp_error tloc ("Type " ^ lexp_string lxp
                                               ^ " and "
                                               ^ lexp_string arrow
                                               ^ " does not match"); dltype, dltype

    in
    let infer_lambda_body kind var body subst =
        (* Read var type from the provided type *)
        let ltp, lbtp = match nosusp t (* t is captured *) with
            | Arrow(kind, _, ltp, _, lbtp) -> ltp, lbtp
            | lxp -> (unify_with_arrow lxp kind subst)
        in
        let nctx = env_extend ctx var Variable ltp in
        let lbody = _lexp_p_check body lbtp nctx (i + 1) in
        Lambda(kind, var, ltp, lbody)

    in
    let subst, _ = !global_substitution in
    let lexp_infer p ctx = _lexp_p_infer p ctx (i + 1) in
    match p with
        (* This case cannot be inferred *)
        | Plambda (kind, var, None, body) ->(infer_lambda_body kind var body subst)

        (* This case can be inferred *)
        | Plambda (kind, var, Some (ptype), body) ->
          let ltp, _ = lexp_infer ptype ctx
          in let nctx = env_extend ctx var Variable ltp
          in let lbody, lbtp = lexp_infer body nctx
          in Lambda(kind, var, ltp, lbody)


        (* This is mostly for the case where no branches are provided *)
        | Pcase (loc, target, patterns) ->
            let lxp, _ = lexp_case (Some t) (loc, target, patterns) ctx i in
                lxp

        (* handle pcall here * )
        | Pcall (fname, _args) -> *)

        | _ -> lexp_p_infer_and_check p ctx t (i + 1)

and lexp_p_infer_and_check pexp ctx t i =
  let (e, inferred_t) = _lexp_p_infer pexp ctx i in
  (match e with
   (* Built-in is a dummy function with no type. We cannot check
    * Built-in *)
   | Builtin _ -> ()
   | _ ->
      let subst, _ = !global_substitution in
      match Unif.unify inferred_t t subst with
      | Some subst -> global_substitution := subst
      | None
        -> debug_msg (
              let print_lxp str =
                print_string (lexp_string str) in
              Debug_fun.do_debug (fun () ->
                  prerr_endline ("0 pxp " ^ pexp_string pexp);
                  ());
              print_string "1 exp "; lexp_print e; print_string "\n";
              print_string "2 inf "; lexp_print inferred_t; print_string "\n";
              print_string "3 ann "; lexp_print t; print_string "\n";
              lexp_warning (pexp_location pexp)
                           "Type Mismatch inferred != Annotation"));
  e

(* Lexp.case cam be checked and inferred *)
and lexp_case (rtype: lexp option) (loc, target, patterns) ctx i =
    (* FIXME: check if case is exhaustive  *)
    (* Helpers *)
    let lexp_infer p ctx = _lexp_p_infer p ctx (i + 1) in

    let rtype = ref rtype in

    let type_check ltp =
        match !rtype with
            (* FIXME: check if branch returns correct type *)
            | Some rltp -> true
             (* if rtype was not provided then we use the first branch as reference *)
            | None -> rtype := (Some ltp); true in

    let uniqueness_warn name =
        lexp_warning loc ("Pattern " ^ name ^ " is a duplicate." ^
                          " It will override previous pattern.") in

    let check_uniqueness loc name map =
        try let _ = SMap.find name map in uniqueness_warn name
            with e -> () in

    (* get target and its type *)
    let tlxp, tltp = lexp_infer target ctx in

    (* make a list of all branches return type *)
    let texp = ref [] in

    (*  Read patterns one by one *)
    let fold_fun (merged, dflt) (pat, exp) =
        (*  Create pattern context *)
        let (name, iloc, arg), nctx = lexp_read_pattern pat exp tlxp ctx in

        (*  parse using pattern context *)
        let exp, ltp = lexp_infer exp nctx in
            (* we added len(arg) variable int the context *)
            texp := ltp::!texp;

        (* Check ltp type. Must be similar to rtype *)
        (if type_check ltp then ()
            else lexp_error iloc "Branch return type mismatch");

        if name = "_" then (
            (if dflt != None then uniqueness_warn name);
                merged, (Some exp))
        else (
            check_uniqueness iloc name merged;
            let merged = SMap.add name (iloc, arg, exp) merged in
                merged, dflt) in

    let (lpattern, dflt) =
        List.fold_left fold_fun (SMap.empty, None) patterns in

    let return_type = match (!texp), (!rtype) with
        | hd::_, _ -> hd
        | _    , Some v -> v

        (* This is impossible *)
        | _, None -> typer_unreachable "The case has no return type info" in

    Case (loc, tlxp, tltp, return_type, lpattern, dflt), return_type

(*  Identify Call Type and return processed call *)
and lexp_call (func: pexp) (sargs: sexp list) ctx i =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let lexp_call func sargs ctx i");
      prerr_endline ("[StackTrace] func     = " ^ pexp_string func);
      prerr_endline ("[StackTrace] sargs    = ???");
      prerr_endline ("[StackTrace] ctx      = ???");
      prerr_endline ("[StackTrace] i        = " ^ string_of_int i);
      prerr_endline ("[StackTrace] ------------------------------------------");
      ());
    let loc = pexp_location func in
    let meta_ctx, _ = !global_substitution in

    let from_lctx ctx = try (from_lctx ctx)
        with e ->(
            lexp_error loc "Could not convert lexp context into rte context";
            print_eval_trace ();
            raise e) in

    (*  Vanilla     : sqr is inferred and (lambda x -> x * x) is returned
     *  Macro       : sqr is returned
     *  Constructor : a constructor is returned
     *  Anonymous   : lambda                                                  *)

    (* retrieve function's body (sqr 3) sqr is a Pvar() *)
    let body, ltp = _lexp_p_infer func ctx (i + 1) in
    let ltp = nosusp ltp in

    let rec handle_fun_args largs sargs ltp =
    Debug_fun.do_debug (fun () ->
        print_endline ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
        print_lexp_ctx (ectx_to_lctx ctx);
        flush stdout;
        prerr_endline "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<";
        print_newline ();(););
      match sargs with
      | [] -> largs, ltp
      | (Node (Symbol (_, "_:=_"), [Symbol (_, aname); sarg])) :: sargs
        (* Explicit-implicit argument.  *)
        -> (match OL.lexp_whnf ltp (ectx_to_lctx ctx) meta_ctx with
           | Arrow (ak, Some (_, aname'), arg_type, _, ret_type)
                when aname = aname'
             -> let parg = pexp_parse sarg in
               let larg = _lexp_p_check parg arg_type ctx i in
               handle_fun_args ((ak, larg) :: largs) sargs
                               (L.mkSusp ret_type (S.substitute larg))
           | _ -> lexp_fatal (sexp_location sarg)
                            ("Explicit-implicit arg `" ^ aname ^ "` to non-function (type = " ^ lexp_string ltp ^ ")"))
      | sarg :: sargs
        (*  Process Argument *)
        -> (match OL.lexp_whnf ltp (ectx_to_lctx ctx) meta_ctx with
           | Arrow (Aexplicit, _, arg_type, _, ret_type)
             -> let parg = pexp_parse sarg in
               let larg = _lexp_p_check parg arg_type ctx i in
               handle_fun_args ((Aexplicit, larg) :: largs) sargs
                               (L.mkSusp ret_type (S.substitute larg))
           | Arrow _ as t -> lexp_print t; print_string "\n";
                            sexp_print sarg; print_string "\n";
                       lexp_fatal (sexp_location sarg)
                                  "Expected non-explicit arg"
           | t ->
            lexp_print t; print_string "\n";
            print_lexp_ctx (ectx_to_lctx ctx);
            lexp_fatal (sexp_location sarg)
                       ("Explicit arg `" ^ sexp_string sarg
                        ^ "` to non-function (type = " ^ lexp_string ltp ^ ")")) in

    let handle_funcall () =
      (* Here we use lexp_whnf on actual code, but it's OK
       * because we only use the result when it's a "predefined constant".  *)
      match OL.lexp_whnf body (ectx_to_lctx ctx) meta_ctx with
      | Builtin((_, "Built-in"), _)
        -> (
        (* ------ SPECIAL ------ *)
        match !_parsing_internals, sargs with
        | true, [String (_, str)] ->
          Builtin((loc, str), ltp), ltp

        | true, [String (_, str); stp] ->
           let ptp = pexp_parse stp in
           let ltp, _ = _lexp_p_infer ptp ctx (i + 1) in
           Builtin((loc, str), ltp), ltp

        | true, _ ->
          lexp_error loc "Wrong Usage of \"Built-in\"";
          dlxp, dltype

        | false, _ ->
          lexp_error loc "Use of \"Built-in\" in user code";
          dlxp, dltype)

      | e ->
        (*  Process Arguments *)
        let largs, ret_type = try handle_fun_args [] sargs ltp
          with Internal_error m -> print_string ( ( lexp_string e ) ^ "---\n" );
            List.iter (fun s ->  Sexp.sexp_print s; print_newline () ) sargs;
            print_endline (">>>" ^ lexp_string ltp);
            raise (Internal_error m)
        in
        Call (body, List.rev largs), ret_type in

    let handle_macro_call () =
      let sxp = match lexp_expand_macro body sargs ctx with
          | Vsexp(sxp) -> sxp
          (* Those are sexp converted by the eval function *)
          | Vint(i)    -> Integer(dloc, i)
          | Vstring(s) -> String(dloc, s)
          | Vfloat(f)  -> Float(dloc, f)
          | v          ->
            value_debug_message loc v "Macro_ expects '(List Sexp) -> Sexp'" in

      let pxp = pexp_parse sxp in
        _lexp_p_infer pxp ctx (i + 1)  in

    (* This is the builtin Macro type *)
    let macro_type, macro_disp = match get_predef_option "Macro" ctx with
      | Some lxp -> OL.lexp_whnf lxp (ectx_to_lctx ctx) meta_ctx, true
      (* When type.typer is being parsed and the predef is not yet available *)
      | None -> dltype, false     in

    (* determine function type *)
    match func, ltp with
      | macro, _ when (macro_disp
                       (* FIXME: This call to lexp_whnf shouldn't be needed!  *)
                       && OL.conv_p (OL.lexp_whnf ltp (ectx_to_lctx ctx)
                                                 meta_ctx)
                                   macro_type) -> (
        match macro with
          | Pvar(l, name) when is_builtin_macro name ->
            let pargs = List.map pexp_parse sargs in
            let largs = _lexp_parse_all pargs ctx i in
              (get_macro_impl loc name) loc largs ctx ltp

          (* true macro *)
          | _ ->
            handle_macro_call ())

      (* FIXME: Handle special-forms here as well!  *)
      | _ -> handle_funcall ()

(*  Read a pattern and create the equivalent representation *)
and lexp_read_pattern pattern exp target ctx:
          ((string * location * (arg_kind * vdef option) list) * elab_context) =

    match pattern with
        | Ppatany (loc) ->            (* Catch all expression nothing to do.  *)
            ("_", loc, []), ctx

        | Ppatvar ((loc, name) as var) ->(
            try(
                let idx = senv_lookup name ctx in
                match env_lookup_expr ctx ((loc, name), idx) with
                (* We are matching a constructor.  *)
                | Some (Cons _) -> (name, loc, []), ctx

                (* name is defined but is not a constructor  *)
                (* it technically could be ... (expr option) *)
                (* What about Var -> Cons ?                  *)
                | _ -> let nctx = ctx_define ctx var target dltype in
                      (name, loc, []), nctx)

            (* Would it not make a default match too?  *)
            with Not_found ->
                (* Create a variable containing target.  *)
                let nctx = ctx_define ctx var target dltype in
                    (name, loc, []), nctx)

        | Ppatcons (ctor, args) ->
           (* Get cons argument types.  *)
           let lctor, _ = lexp_p_infer ctor ctx in
           let meta_ctx, _ = !global_substitution in
           match OL.lexp_whnf lctor (ectx_to_lctx ctx) meta_ctx with
           | Cons (it, (loc, cons_name))
             -> let cons_args = match OL.lexp_whnf it (ectx_to_lctx ctx)
                                                  meta_ctx with
                 | Inductive(_, _, _, map)
                   -> (try SMap.find cons_name map
                      with Not_found
                           -> lexp_warning loc
                                          ("`" ^ lexp_string (it)
                                           ^ "` does not hold a `"
                                           ^ cons_name ^ "` constructor"); [])
                 | it -> lexp_fatal loc
                                  ("`" ^ lexp_string (it)
                                   ^ "` is not an inductive type!") in

               (* FIXME: Don't remove them, add them without names!  *)
               (* FIXME: Add support for explicit-implicit fields!  *)
               (* Remove non explicit argument.  *)
               let rec remove_nexplicit args acc =
                 match args with
                 | [] -> List.rev acc
                 | (Aexplicit, _, ltp)::tl -> remove_nexplicit tl (ltp::acc)
                 | hd::tl -> remove_nexplicit tl acc in

               let cons_args = remove_nexplicit cons_args [] in

               (* read pattern args *)
               let args, nctx = lexp_read_pattern_args args cons_args ctx in
               (cons_name, loc, args), nctx
           | _ -> lexp_warning (pexp_location ctor)
                              ("Invalid constructor `"
                               ^ (pexp_string ctor) ^ "`");
                 ("_", pexp_location ctor, []), ctx

(*  Read patterns inside a constructor *)
and lexp_read_pattern_args args (args_type : lexp list) ctx:
                   (((arg_kind * vdef option) list) * elab_context)=

    let length_type = List.length args_type in
    let length_pat = List.length args in

    let make_list elem size =
      let rec loop i acc =
        if i < size then loop (i + 1) (elem::acc) else acc
        in loop 0 [] in

    let args_type = if length_type != length_pat then
      make_list dltype length_pat else args_type in

    (if length_type != length_pat then lexp_warning dloc "Size Mismatch");

    let rec loop args args_type acc ctx =
        match args, args_type with
            | [], _ -> (List.rev acc), ctx
            | hd::tl, ltp::type_tl -> (
                let (_, pat) = hd in
                match pat with
                    (* Nothing to do *)
                    | Ppatany (loc) -> loop tl type_tl ((Aexplicit, None)::acc) ctx
                    | Ppatvar ((loc, name) as var) ->
                        (*  Add var *)
                        let nctx = env_extend ctx var Variable ltp in
                        let nacc = (Aexplicit, Some var)::acc in
                            loop tl type_tl nacc nctx
                    | _ -> lexp_error dloc "Constructor inside a Constructor";
                           loop tl type_tl ((Aexplicit, None)::acc) ctx)
            | _ -> typer_unreachable "unreachable branch"

    in loop args args_type [] ctx

(*  Parse inductive type definition.  *)
and lexp_parse_inductive ctors ctx i =
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let lexp_parse_inductive ctors ctx i");
      prerr_endline ("[StackTrace] ctors    = ???");
      prerr_endline ("[StackTrace] ctx      = ???");
      prerr_endline ("[StackTrace] i        = " ^ string_of_int i);
      prerr_endline ("[StackTrace] ------------------------------------------");
      ());
    let lexp_parse p ctx = _lexp_p_infer p ctx (i + 1) in

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
and lexp_expand_macro macro_funct sargs ctx =

  (* Build the function to be called *)
  let macro_expand = get_predef "expand_macro_" ctx in
  let args = [(Aexplicit, macro_funct); (Aexplicit, (olist2tlist_lexp sargs ctx))] in

  let macro = Call(macro_expand, args) in
  let emacro = OL.erase_type macro in
  let rctx = from_lctx ctx in

  (* eval macro *)
   _global_eval_trace := [];
  let vxp = try eval emacro rctx
    with e -> print_eval_trace (); raise e in
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
        | None -> lexp_fatal loc "expression does not exist" in

      (* Special Form *)
        match mfun with
          | Var((_, "add-attribute"), _) ->(
            (* Builtin macro *)
            let pargs = List.map pexp_parse sargs in
            let largs = _lexp_parse_all pargs ctx 0 in

            (* extract info *)
            let var, att, fn = match largs with
              | [Var((_, vn), vi); Var((_, an), ai); fn] -> (vi, vn), (ai, an), fn
              | _ -> lexp_fatal loc "add-attribute expects 3 args" in

            let ctx = add_property ctx var att fn in

            (* FIXME: We need to have something in lexp to represent this
             * add-attribute operation!  *)
              [], ctx)

          | _ ->(
            let ret = lexp_expand_macro body sargs ctx in

            (* convert typer list to ocaml *)
            let decls = tlist2olist [] ret in

            (* extract sexp from result *)
            let decls = List.map (fun g ->
              match g with
                | Vsexp(sxp) -> sxp
                | _ -> value_debug_message loc g "Macro expects sexp list") decls in

            (* read as pexp_declaraton *)
            pexp_decls_all decls, ctx)
  with _ ->
    lexp_fatal loc "Macro not found"

(*  Parse let declaration *)
and lexp_p_decls decls ctx = _lexp_decls decls ctx 0

and lexp_check_decls (ectx : elab_context) (* External context.  *)
                     (nctx : elab_context) (* Context with type declarations. *)
                     (defs : (vdef * pexp * ltype) list)
    : (vdef * lexp * ltype) list * elab_context =
  let declmap = List.fold_right
                  (fun ((_, vname) as v, pexp, ltp) map ->
                    let i = senv_lookup vname nctx in
                    let adjusted_ltp = push_susp ltp (S.shift (i + 1)) in
                    IntMap.add i (v, lexp_p_check pexp adjusted_ltp nctx, ltp)
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
            lexp_error l ("Variable `" ^ s ^ "` declared but not defined!")
          else
            assert (pending_defs == []));
         [], [], nctx

  | Ptype ((l, vname) as v, ptp) :: pdecls
    -> let (ltp, lsort) = lexp_p_infer ptp nctx in
      if SMap.mem vname pending_decls then
        (lexp_error l ("Variable `" ^ vname ^ "` declared twice!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)
      else if List.exists (fun ((_, vname'), _, _) -> vname = vname')
                          pending_defs then
        (lexp_error l ("Variable `" ^ vname ^ "` already defined!");
         lexp_decls_1 pdecls ectx nctx pending_decls pending_defs)
      else (elab_check_sort nctx lsort v ltp;
            lexp_decls_1 pdecls ectx
                         (env_extend nctx v ForwardRef ltp)
                         (SMap.add vname (l, ltp) pending_decls)
                         pending_defs)

  | Pexpr ((l, vname) as v, pexp) :: pdecls
       when SMap.is_empty pending_decls
    -> assert (pending_defs == []);
      assert (ectx == nctx);
      let (lexp, ltp) = lexp_p_infer pexp nctx in
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
         lexp_error l ("`" ^ vname ^ "` defined but not declared!");
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

      else lexp_fatal l "Context changed in already changed context")


and _lexp_decls pdecls ctx i: ((vdef * lexp * ltype) list list * elab_context) =
  if pdecls = [] then [], ctx else
    let decls, pdecls, nctx = lexp_decls_1 pdecls ctx ctx SMap.empty [] in
    let declss, nnctx = _lexp_decls pdecls nctx i in
    decls :: declss, nnctx

and lexp_decls_toplevel decls ctx =
  _lexp_decls decls ctx 1

and _lexp_parse_all (p: pexp list) (ctx: elab_context) i : lexp list =

    let rec loop (plst: pexp list) ctx (acc: lexp list) =
        match plst with
            | [] -> (List.rev acc)
            | pe :: plst  -> let lxp, _ = _lexp_p_infer pe ctx (i + 1) in
                    (loop plst ctx (lxp::acc)) in

    (loop p ctx [])


and print_lexp_trace () =
    print_trace " LEXP TRACE " 50 pexp_string pexp_print !_global_lexp_trace

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


let lexp_parse_all p ctx = _lexp_parse_all p ctx 1


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
        lexp_warning dloc "Predef not found";
        lctx in
      let rctx = make_runtime_ctx in
      let rctx = eval_decls_toplevel (List.map OL.clean_decls d) rctx in
      _global_eval_trace := [];
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
  Debug_fun.do_debug (fun () ->
      prerr_endline ("[StackTrace] ------------------------------------------");
      prerr_endline ("[StackTrace] let _eval_expr_str str lctx rctx silent");
      prerr_endline ("[StackTrace] str = " ^ str);
      prerr_endline ("[StackTrace] lctx = ???");
      prerr_endline ("[StackTrace] rctx = ???");
      prerr_endline ("[StackTrace] silent = " ^ string_of_bool silent);
      prerr_endline ("[StackTrace] ------------------------------------------");
    ());
    let lxps = lexp_expr_str str lctx in
    let elxps = List.map OL.erase_type lxps in
        (eval_all elxps rctx silent)

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
    let elxps = (List.map OL.clean_decls lxps) in
        (eval_decls_toplevel elxps rctx), lctx

