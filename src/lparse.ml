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

type debug_type =
  | Dbi of int
  | Str of string
  | Lexp of lexp

let debug_print str = let _ = match str with
  | Str str -> print_string str
  | Dbi dbi -> print_string "DBI: "; print_int dbi
  | Lexp lxp -> lexp_print lxp in
    print_string "\n"

(* merged declaration, allow us to process declaration in multiple pass *)
(* first detect recursive decls then lexp decls*)
type mdecl =
  | Ldecl of symbol * pexp option * pexp option
  | Lmcall of symbol * sexp list

let elab_check_def (ctx : lexp_context) var lxp ltype =
  if OL.conv_p ltype (OL.check ctx lxp) then
    ()                          (* FIXME: Check ltype as well!  *)
  else
    (print_string "¡¡ctx_define error!!\n";
     lexp_print lxp;
     print_string " !: ";
     lexp_print ltype;
     print_string "\nbecause\n";
     lexp_print (OL.check ctx lxp);
     print_string " != ";
     lexp_print ltype;
     print_string "\n";
     lexp_fatal (let (l,_) = var in l) "TC error")

let ctx_define (ctx: elab_context) var lxp ltype =
  elab_check_def (ectx_to_lctx ctx) var lxp ltype;
  env_extend ctx var (LetDef lxp) ltype

let ctx_define_rec (ctx: elab_context) decls =
  let nctx = ectx_extend_rec ctx decls in
  (* FIXME: conv_p fails too often, e.g. it fails to see that `Type` is
   * convertible to `Type_0`, because it doesn't have access to lctx.
   *
   * let nlctx = ectx_to_lctx nctx in
   * let _ = List.fold_left (fun n (var, lxp, ltp)
   *                         -> elab_check_def nlctx var lxp
   *                                          (push_susp ltp (S.shift n));
   *                           n - 1)
   *                        (List.length decls)
   *                        decls in *)
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

let rec lexp_p_infer (p : pexp) (ctx : elab_context): lexp * ltype =
    _lexp_p_infer p ctx 1

and _lexp_p_infer (p : pexp) (ctx : elab_context) i: lexp * ltype =

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

        (* This case can be inferred *)
        | Plambda (kind, var, optype, body) ->
            let ltp, _ = match optype with
                | Some ptype -> lexp_infer ptype ctx
                (* This case must have been lexp_p_check *)
                | None -> lexp_error tloc "Lambda require type annotation";
                    dltype, dltype in

            let nctx = env_extend ctx var Variable ltp in
            let lbody, lbtp = lexp_infer body nctx in

            let lambda_type = Arrow(kind, None, ltp, tloc, lbtp) in
                Lambda(kind, var, ltp, lbody), lambda_type

        | Pcall (fname, _args) ->
            lexp_call fname _args ctx i

        (* Pcons *)
        | Pcons(t, sym) ->
            let idt, _ = lexp_infer t ctx in
            let (loc, cname) = sym in

            (* Get constructor args *)
            let formal, args = match OL.lexp_whnf idt (ectx_to_lctx ctx) with
              | Inductive(_, _, formal, ctor_def) -> (
                try formal, (SMap.find cname ctor_def)
                with Not_found ->
                  lexp_error loc
                             ("Constructor \"" ^ cname ^ "\" does not exist");
                  [], [])

              | _ -> lexp_error loc "Not an Inductive Type"; [], [] in

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

        | Phastype (_, pxp, ptp) ->
            let ltp, _ = lexp_infer ptp ctx in
                (_lexp_p_check pxp ltp ctx (i + 1)), ltp

        | _ -> pexp_print p; print_string "\n";
            lexp_fatal tloc "Unhandled Pexp"


and lexp_let_decls decls (body: lexp) ctx i =
  (* build the weird looking let *)
  let decls = List.rev decls in
    List.fold_left (fun lxp decls ->
      Let(dloc, decls, lxp)) body decls

and lexp_p_check (p : pexp) (t : ltype) (ctx : elab_context): lexp =
  _lexp_p_check p t ctx 1

and _lexp_p_check (p : pexp) (t : ltype) (ctx : elab_context) i: lexp =
    let tloc = pexp_location p in

    _global_lexp_ctx := ctx;
    _global_lexp_trace := (i, tloc, p)::!_global_lexp_trace;

    match p with
        (* This case cannot be inferred *)
        | Plambda (kind, var, None, body) ->(
            (* Read var type from the provided type *)
            let ltp, lbtp = match nosusp t with
                | Arrow(kind, _, ltp, _, lbtp) -> ltp, lbtp
                | _ -> lexp_error tloc "Type does not match"; dltype, dltype in

            let nctx = env_extend ctx var Variable ltp in
            let lbody = _lexp_p_check body lbtp nctx (i + 1) in

                Lambda(kind, var, ltp, lbody))

        (* This is mostly for the case where no branches are provided *)
        | Pcase (loc, target, patterns) ->
            let lxp, _ = lexp_case (Some t) (loc, target, patterns) ctx i in
                lxp

        (* handle pcall here * )
        | Pcall (fname, _args) -> *)

        | _ -> let (e, inferred_t) = _lexp_p_infer p ctx (i + 1) in
            e (*
            match e with
                (* Built-in is a dummy function with no type. We cannot check
                 * Built-in *)
                | Builtin _ -> e
                | _ ->
            (if OL.conv_p inferred_t t then () else debug_msg (
                print_string "1 exp "; lexp_print e; print_string "\n";
                print_string "2 inf "; lexp_print inferred_t; print_string "\n";
                print_string "3 Ann "; lexp_print t; print_string "\n";
                lexp_warning tloc "Type Mismatch inferred != Annotation"));
                e*)

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
    let loc = pexp_location func in

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

    let rec handle_fun_args largs sargs ltp = match sargs with
      | [] -> largs, ltp
      | (Node (Symbol (_, "_:=_"), [Symbol (_, aname); sarg])) :: sargs
        (* Explicit-implicit argument.  *)
        -> (match OL.lexp_whnf ltp (ectx_to_lctx ctx) with
           | Arrow (ak, Some (_, aname'), arg_type, _, ret_type)
                when aname = aname'
             -> let parg = pexp_parse sarg in
               let larg = _lexp_p_check parg arg_type ctx i in
               handle_fun_args ((ak, larg) :: largs) sargs
                               (L.mkSusp ret_type (S.substitute larg))
           | _ -> lexp_fatal (sexp_location sarg)
                            ("Explicit arg `" ^ aname ^ "` to non-function (type = " ^ lexp_to_str ltp ^ ")"))
      | sarg :: sargs
        (*  Process Argument *)
        -> (match OL.lexp_whnf ltp (ectx_to_lctx ctx) with
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
                       ("Explicit arg `" ^ sexp_to_str sarg
                        ^ "` to non-function (type = " ^ lexp_to_str ltp ^ ")")) in

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
           let ltp, _ = _lexp_p_infer ptp ctx (i + 1) in
           Builtin((loc, str), ltp), ltp

        | true, _ ->
          lexp_error loc "Wrong Usage of \"Built-in\"";
          dlxp, dltype

        | false, _ ->
          lexp_error loc "Use of \"Built-in\" in user code";
          dlxp, dltype)

      | _ ->
        (*  Process Arguments *)
        let largs, ret_type = handle_fun_args [] sargs ltp in
        Call (body, List.rev largs), ret_type in

    let handle_macro_call () =
        (* Build function to be called *)
        let macro_expand = get_predef "expand_macro_" ctx in
        let args = [(Aexplicit, body); (Aexplicit, (olist2tlist_lexp sargs ctx))] in
        let macro = Call(macro_expand, args) in
        let emacro = OL.erase_type macro in
        let rctx = (from_lctx ctx 0) in

        _global_eval_trace := [];

        let vxp = try eval emacro rctx
          with e ->
            print_eval_trace ();
            raise e in

          let sxp = match vxp with
              | Vsexp(sxp) -> sxp
              (* Those are sexp converted by the eval function *)
              | Vint(i)    -> Integer(dloc, i)
              | Vstring(s) -> String(dloc, s)
              | Vfloat(f)  -> Float(dloc, f)
              (* I have vdum here WHY *)
              | v -> debug_msg (value_print v); print_string "\n";
                  lexp_fatal loc "Macro_ expects '(List Sexp) -> Sexp'" in

        let pxp = pexp_parse sxp in
            _lexp_p_infer pxp ctx (i + 1)  in

    (* This is the builtin Macro type *)
    let macro_type, macro_disp = match get_predef_option "Macro" ctx with
      | Some lxp -> OL.lexp_whnf lxp (ectx_to_lctx ctx), true
      (* When type.typer is being parsed and the predef is not yet available *)
      | None -> dltype, false     in

    (*)
    lexp_print ltp; print_string "\n";
    print_string (if (OL.conv_p ltp macro_type) then "true" else "false"); print_string "\n"; *)

    (* determine function type *)
    match func, ltp with
      | macro, _ when (macro_disp
                       (* FIXME: This call to lexp_whnf shouldn't be needed!  *)
                       && OL.conv_p (OL.lexp_whnf ltp (ectx_to_lctx ctx))
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
           match OL.lexp_whnf lctor (ectx_to_lctx ctx) with
           | Cons (it, (loc, cons_name))
             -> let cons_args = match OL.lexp_whnf it (ectx_to_lctx ctx) with
                 | Inductive(_, _, _, map)
                   -> (try SMap.find cons_name map
                      with Not_found
                           -> lexp_warning loc
                                          ("`" ^ lexp_to_str (it)
                                           ^ "` does not hold a `"
                                           ^ cons_name ^ "` constructor"); [])
                 | it -> lexp_fatal loc
                                  ("`" ^ lexp_to_str (it)
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
                               ^ (pexp_to_string ctor) ^ "`");
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
and lexp_decls_macro (loc, mname) sargs ctx: (pdecl list * elab_context) =
  (* lookup for mname_  *)
  let idx = try senv_lookup mname ctx
    with Not_found ->
      lexp_warning loc ("Macro \"" ^ mname ^ "\" was not found!"); 0 in

  (* get Macro declaration *)
  let lxp = try env_lookup_expr ctx ((loc, mname), idx)
    with Not_found ->
      lexp_fatal loc (mname ^ " was found but " ^ (string_of_int idx) ^
                  " is not a correct index.") in

  (* get stored function *)
  let lxp = match lxp with
    | Some (Call(Var((_, "Macro_"), _), [(_, fct)])) -> fct
    | None -> lexp_fatal loc "expression does not exist"
    | Some lxp -> print_string "\n";
      print_string (lexp_to_str lxp); print_string "\n";
      lexp_print lxp; print_string "\n";
      lexp_fatal loc "Macro is ill formed" in

    match lxp with
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
          [], ctx
        )
        (* Standard Macro *)
      | _ -> (
        (* build new function *)
        let arg = olist2tlist_lexp sargs ctx in
        let lxp = Call(lxp, [(Aexplicit, arg)]) in
        let elexp = OL.erase_type lxp in
        let rctx = (from_lctx ctx 0) in

        (* get a list of declaration *)
        let decls = eval elexp rctx in

        (* convert typer list to ocaml *)
        let decls = tlist2olist [] decls in

        (* extract sexp from result *)
        let decls = List.map (fun g ->
          match g with
            | Vsexp(sxp) -> sxp
            | _ ->
              print_string ((value_name g) ^ " : ");
              value_print g; print_string "\n";
              lexp_fatal loc "Macro expects sexp list") decls in

        (* read as pexp_declaraton *)
          pexp_decls_all decls, ctx)

(*  Parse let declaration *)
and lexp_p_decls decls ctx = _lexp_decls decls ctx 0

and lexp_detect_recursive pdecls =
  (* Pack mutually recursive declarations                 *)
  (* mutually recursive def must use forward declarations *)

  let decls = ref [] in
  let pending = ref [] in
  let merged = ref [] in

  List.iter (fun expr ->
    match expr with
      | Pexpr((l, s), pxp) ->(
        let was_forward = (List.exists
                      (fun (Ldecl((_, p), _, _)) -> p = s) !pending) in

        let is_empty = (List.length !pending) = 0 in
        let is_one = (List.length !pending) = 1 in

        (* This is a standard declaration: not forwarded *)
        if (was_forward = false) && is_empty then(
          decls := [Ldecl((l, s), Some pxp, None)]::!decls;
        )
        (* This is an annotated expression
         * or the last element of a mutually rec definition *)
        else if (was_forward && is_one) then (

          (* we know that names match already *)
          let ptp = (match (!pending) with
            | Ldecl(_, _, ptp)::[] -> ptp
            (* we already checked that len(pending) == 1*)
            | Ldecl(_, _, ptp)::_  -> lexp_fatal l "Unreachable"
            | []                   -> lexp_fatal l "Unreachable"
            | Lmcall _ :: _        -> lexp_fatal l "Unreachable") in

          (* add declaration to merged decl *)
          merged := Ldecl((l, s), Some pxp, ptp)::(!merged);

          (* append decls *)
          decls := (List.rev !merged)::!decls;

          (* Reset State *)
          pending := [];
          merged := [];
        )
        (* This is a mutually recursive definition *)
        else (
          (* get pending element and remove it from the list *)
          let elem, lst = List.partition
                                (fun (Ldecl((_, n), _, _)) -> n = s) !pending in

          let _ = (match elem with
              (* nothing to merge *)
              | [] ->
                merged := Ldecl((l, s), Some pxp, None)::!merged;

              (* append new element to merged list *)
              | Ldecl((l, s), _, Some ptp)::[] ->
                merged := Ldecl((l, s), Some pxp, (Some ptp))::!merged;

              (* s should be unique *)
              | _ -> lexp_error l "declaration must be unique") in

          (* element is not pending anymore *)
          pending := lst;
        ))

      | Ptype((l, s), ptp) ->
        pending := Ldecl((l, s), None, Some ptp)::!pending

      (* macro will be handled later *)
      | Pmcall(a, sargs) ->
          decls := [Lmcall(a, sargs)]::!decls;

      ) pdecls;

      (List.rev !decls)


and _lexp_decls decls ctx i: ((vdef * lexp * ltype) list list * elab_context) =
  (* detect mutually recursive def and merge definition *)
  let decls = lexp_detect_recursive decls in
  let all = ref [] in

  let ctx = List.fold_left (fun ctx decl ->
    match decl with
      (* Special case *)
      | [Lmcall ((l, s), sargs)] ->
        (* get pexp decls *)
        let pdecls, ctx = lexp_decls_macro (l, s) sargs ctx in
        let decls, ctx = _lexp_decls pdecls ctx i in
          all := (List.append (List.rev decls) !all);
            ctx

      | _ ->
        let d, ctx = _lexp_rec_decl decl ctx i in
          all := d::!all;
          ctx) ctx decls in

      (List.rev !all), ctx

and _lexp_rec_decl decls ctx i =
  (* parse a group of mutually recursive definitions
   * i.e let decl parsing *)

  (* to compute recursive offset *)
  let lst = ref [] in

  (* add all elements to the environment *)
  let tctx = List.fold_left (fun vctx decl ->
    match decl with
      | Ldecl((l, s), _, None) ->
        env_extend vctx (l, s) ForwardRef dltype

      | Ldecl((l, s), _, Some ptp) ->
        let ltp, _ = lexp_p_infer ptp vctx in
          env_extend vctx (l, s) ForwardRef ltp

      | Lmcall _ ->
        lexp_fatal dloc "use lexp_decl_macro to parse macro decls") ctx decls in

        (* ectx_extend_rec (ctx: elab_context) (defs: (vdef * lexp * ltype) list) *)
  let i = ref (1 + List.length decls) in
  let ctx = List.fold_left (fun vctx decl ->
    i := !i - 1;
    match decl with
      (* +1 because we allow each definition to be recursive *)
      (* lexp infer *)
      | Ldecl ((l, s), Some pxp, None) ->
          (* debug_print (Str "Lexp Rec Decl");
             debug_print (Str s); *)
          let lxp, ltp = lexp_p_infer pxp tctx in
          lst := ((l, s), lxp, ltp)::!lst;
          (env_extend_rec (!i) vctx (l, s) (LetDef lxp) ltp)

      (* lexp check *)
      | Ldecl ((l, s), Some pxp, Some ptp) ->
          let ltp, _ = lexp_p_infer ptp tctx in
          let lxp = lexp_p_check pxp ltp tctx in
          lst := ((l, s), lxp, ltp)::!lst;
          (env_extend_rec (!i) vctx (l, s) (LetDef lxp) ltp)

      (* macros *)
      | Lmcall (a, sargs) ->
        lexp_fatal dloc "use lexp_decl_macro to parse macro decls"

      (* unused arg *)
      | Ldecl ((l, s), None, _) ->
        lexp_error l ("Variable \"" ^ s ^ "\" is unused!");
        vctx) ctx decls in

        (List.rev !lst), ctx

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
    print_trace " LEXP TRACE " 50 pexp_to_string pexp_print !_global_lexp_trace

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
    let lxps = lexp_expr_str str lctx in
    let elxps = List.map OL.erase_type lxps in
        (eval_all elxps rctx silent)

let eval_expr_str str lctx rctx = _eval_expr_str str lctx rctx false

let eval_decl_str str lctx rctx =
    let lxps, lctx = lexp_decl_str str lctx in
    let elxps = (List.map OL.clean_decls lxps) in
        (eval_decls_toplevel elxps rctx), lctx

